use super::{errors, obj::Object};
use std::{cell::RefCell, rc::Rc};

use fxhash::FxHashMap;
use itertools::Itertools;

use crate::{
    analysis::program_data::{
        ConstraintAssign, ExprRef, IdentRef, InstanceDefId, InstanceRef, PatternRef, ProgramData,
        VarId,
    },
    ast::{Expr, Pattern},
    lexer::Token,
    runner::obj::Func,
    std_lib,
};

macro_rules! native_func {
    ($runner_ident:ident, $p:pat => $body:expr) => {
        Object::Func(Func::NativeFunc(Rc::new(
            move |$runner_ident: &mut Runner, arg: Rc<Object>| match &*arg {
                $p => $body,
                #[allow(unreachable_patterns)]
                _ => panic!("invalid argument type for native function"),
            },
        )))
    };
}

pub struct Runner {
    program_data: ProgramData,
    scope: Scope,
    pub instance_body_cache: FxHashMap<InstanceRef, Rc<InstanceBody>>,
    pub instance_body_definers: FxHashMap<InstanceDefId, InstanceDefiner>,
}
pub type DefInner = Rc<dyn Fn(&mut Runner, ConstraintAssign) -> errors::Result<Rc<Object>>>;
#[derive(Clone)]
pub enum Variable {
    Var(Rc<Object>),
    Def(DefInner),
}
impl From<Rc<Object>> for Variable {
    fn from(obj: Rc<Object>) -> Self {
        Variable::Var(obj)
    }
}
impl From<Object> for Variable {
    fn from(obj: Object) -> Self {
        Variable::Var(Rc::new(obj))
    }
}

pub struct InstanceBody {
    pub methods: FxHashMap<Rc<str>, Variable>,
}
pub enum InstanceDefiner {
    Just(Rc<InstanceBody>),
    WithConstraintAssign(Rc<dyn Fn(&mut Runner, ConstraintAssign) -> Rc<InstanceBody>>),
}

#[derive(Default, Clone)]
pub struct Scope {
    vars: im_rc::HashMap<VarId, Variable, fxhash::FxBuildHasher>,
    instance_replace: ConstraintAssign,
    implicit_args: im_rc::Vector<Rc<Object>>,
}

impl Runner {
    pub fn new(program_data: ProgramData, std_lib: std_lib::StdLib) -> Self {
        Self {
            program_data,
            scope: Scope {
                vars: std_lib
                    .extern_funcs
                    .into_iter()
                    .map(|(var_id, (_, _, obj))| (var_id, obj))
                    .collect(),
                instance_replace: ConstraintAssign::default(),
                implicit_args: im_rc::Vector::new(),
            },
            instance_body_cache: FxHashMap::default(),
            instance_body_definers: std_lib.instance_body_definers,
        }
    }
    pub fn read_var(
        &mut self,
        variable: &Variable,
        given_instance: ConstraintAssign,
    ) -> errors::Result<Rc<Object>> {
        match variable {
            Variable::Var(obj) => Ok(obj.clone()),
            Variable::Def(def) => def(self, given_instance),
        }
    }
    pub fn eval(&mut self, expr: Rc<Expr>) -> errors::Result<Rc<Object>> {
        if let Some(desugared) = self.program_data.desugaered.get(&ExprRef(expr.clone())) {
            return self.eval(desugared.clone());
        }
        match &*expr {
            Expr::LitInt(n) => Ok(Rc::new(Object::Int(n.parse().unwrap()))),
            Expr::LitFloat(n) => Ok(Rc::new(Object::Float(n.parse().unwrap()))),
            Expr::LitStr(s) => Ok(Rc::new(Object::String(Rc::new(s.to_string())))),
            Expr::LitBool(b) => Ok(Rc::new(Object::Bool(*b))),
            Expr::AppFun(f, p) => {
                let func = self.eval(f.clone())?;
                let Object::Func(func) = &*func else {
                    panic!("expected function")
                };
                let param = self.eval(p.clone())?;
                self.call(func, param)
            }
            Expr::LitList(items) => Ok(Rc::new(Object::List(
                items
                    .iter()
                    .map(|item| self.eval(item.clone()))
                    .try_collect()?,
            ))),
            Expr::Unit => Ok(Rc::new(Object::Unit)),
            Expr::Ident(name) => {
                let ident_ref = self.program_data.expr_ident_ref[&ExprRef(expr.clone())].clone();

                let (data, mut given_instance) = match ident_ref {
                    IdentRef::Var(var_id, given_instance) => {
                        let data = self.scope.vars.get(&var_id).cloned().unwrap_or_else(|| {
                            panic!("variable with id {var_id:?}(name: {name}) not found in scope")
                        });
                        (data, given_instance)
                    }
                    IdentRef::Method(mut instance, method_name, given_instance) => {
                        self.replace_instance(&mut instance);
                        let instance_body = self.get_instance_body(instance.clone());
                        let data = instance_body.methods[&method_name].clone();
                        (data, given_instance)
                    }
                };
                for (_, to) in given_instance.iter_mut() {
                    self.replace_instance(to);
                }
                let data = self.read_var(&data, given_instance)?;
                Ok(data)
            }
            Expr::Brace(statements)
                if self.program_data.partial_app_arg_types[&ExprRef(expr.clone())].is_empty() =>
            {
                let out_scope = self.scope.clone();
                let mut result = Rc::new(Object::Unit);
                for expr in statements {
                    result = self.eval(expr.clone())?;
                }
                self.scope = out_scope;
                Ok(result)
            }
            Expr::Brace(_) => {
                let implicit_arg_count =
                    self.program_data.partial_app_arg_types[&ExprRef(expr.clone())].len();
                Ok(Rc::new(Object::Func(Func::PartialApp(
                    expr.clone(),
                    self.scope.clone(),
                    implicit_arg_count,
                    im_rc::Vector::new(),
                ))))
            }
            Expr::Let(pattern, assigned_expr, _) => {
                let obj = self.eval(assigned_expr.clone())?;
                self.assign_pattern(pattern.clone(), obj)?;
                Ok(Rc::new(Object::Unit))
            }
            Expr::Lambda(pat, body) => {
                let pat = pat.clone();
                let body = body.clone();
                let scope = self.scope.clone();
                Ok(Rc::new(Object::Func(Func::UserDefFunc(pat, body, scope))))
            }
            Expr::Def(_, assigned_expr, _) => {
                let scope = Rc::new(RefCell::new(self.scope.clone()));
                let var_id = self.program_data.def_var_ids[&ExprRef(expr.clone())];
                let assigned_expr = assigned_expr.clone();
                {
                    let scope = scope.clone();
                    self.scope.vars.insert(
                        var_id,
                        Variable::Def(Rc::new(move |runner: &mut Runner, instance_replace| {
                            let out_scope = runner.scope.clone();
                            runner.scope = scope.borrow().clone();
                            runner.scope.instance_replace.extend(instance_replace);
                            let result = runner.eval(assigned_expr.clone());
                            runner.scope = out_scope;
                            result
                        })),
                    );
                }
                *scope.borrow_mut() = self.scope.clone();
                Ok(Rc::new(Object::Unit))
            }
            Expr::UnOp(Token::Apostrophe, expr) => {
                let scope = self.scope.clone();
                let expr = expr.clone();
                Ok(Rc::new(native_func!(runner,
                    Object::Unit => {
                        let out_scope = runner.scope.clone();
                        runner.scope = scope.clone();
                        let result = runner.eval(expr.clone());
                        runner.scope = out_scope;
                        result
                    }
                )))
            }
            Expr::ImplicitArg => {
                let index = self.program_data.implicit_arg_index[&ExprRef(expr.clone())];
                Ok(self.scope.implicit_args[index].clone())
            }
            Expr::Typed(inner, _) => self.eval(inner.clone()),
            Expr::BinOp(_, _, _) => unreachable!(),
            Expr::UnOp(_, _) => unreachable!(),
            Expr::Member(_, _) => todo!(),
        }
    }
    fn assign_pattern(&mut self, pat: Rc<Pattern>, obj: Rc<Object>) -> errors::Result<()> {
        match &*pat {
            Pattern::Ident(_) => {
                let var_id = self.program_data.pat_var_ids[&PatternRef(pat.clone())];
                self.scope.vars.insert(var_id, Variable::Var(obj));
                Ok(())
            }
            Pattern::Pair(l, r) => {
                let Object::Comma(left, right) = &*obj else {
                    panic!("expected comma object for comma pattern")
                };
                self.assign_pattern(l.clone(), left.clone())?;
                self.assign_pattern(r.clone(), right.clone())?;
                Ok(())
            }
            Pattern::Unit => {
                if let Object::Unit = &*obj {
                    Ok(())
                } else {
                    panic!("expected unit for unit pattern")
                }
            }
            Pattern::Wildcard => Ok(()),
        }
    }
    pub fn call(&mut self, func: &Func, param: Rc<Object>) -> errors::Result<Rc<Object>> {
        match &func {
            Func::NativeFunc(inner) => inner(self, param),
            Func::UserDefFunc(pat, body, def_scope) => {
                let out_scope = self.scope.clone();
                self.scope = def_scope.clone();
                self.assign_pattern(pat.clone(), param)?;
                let result = self.eval(body.clone());
                self.scope = out_scope;
                result
            }
            Func::PartialApp(expr, scope, arg_count, args) => {
                let mut new_args = args.clone();
                new_args.push_back(param);
                if new_args.len() == *arg_count {
                    let out_scope = self.scope.clone();
                    self.scope = scope.clone();
                    self.scope.implicit_args = new_args;
                    let Expr::Brace(stmts) = &**expr else {
                        panic!("expected brace expression for partial app")
                    };
                    let mut result = Rc::new(Object::Unit);
                    for stmt in stmts {
                        result = self.eval(stmt.clone())?;
                    }
                    self.scope = out_scope;
                    Ok(result)
                } else {
                    Ok(Rc::new(Object::Func(Func::PartialApp(
                        expr.clone(),
                        scope.clone(),
                        *arg_count,
                        new_args,
                    ))))
                }
            }
        }
    }
    pub fn replace_instance(&self, instance_ref: &mut InstanceRef) {
        match instance_ref {
            InstanceRef::Given(constraint_id) => {
                if let Some(repl) = self.scope.instance_replace.get(constraint_id) {
                    *instance_ref = repl.clone();
                } else {
                    panic!("instance not found in replace map")
                }
            }
            InstanceRef::Def(_, constraint_assign) => {
                let mut constraint_assign = constraint_assign.clone();
                for (_, to) in constraint_assign.iter_mut() {
                    self.replace_instance(to);
                }
            }
        }
    }
    pub fn get_instance_body(&mut self, mut instance_ref: InstanceRef) -> Rc<InstanceBody> {
        self.replace_instance(&mut instance_ref);
        if let Some(body) = self.instance_body_cache.get(&instance_ref) {
            return body.clone();
        }
        let InstanceRef::Def(def_id, constraint_assign) = &instance_ref else {
            panic!("expected InstanceRef::Def")
        };
        let definer = &self.instance_body_definers[def_id];
        let body = match definer {
            InstanceDefiner::Just(body) => body.clone(),
            InstanceDefiner::WithConstraintAssign(f) => f.clone()(self, constraint_assign.clone()),
        };
        self.instance_body_cache.insert(instance_ref, body.clone());
        body
    }
}
