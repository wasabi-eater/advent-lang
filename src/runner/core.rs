use super::{errors, obj::Object};
use std::rc::Rc;

use fxhash::FxHashMap;
use itertools::Itertools;

use crate::{
    analysis::program_data::{
        ConstraintAssign, ExprRef, IdentRef, InstanceDefId, InstanceRef, ProgramData, VarId,
    },
    ast::Expr,
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

macro_rules! curry {
    ([$($captured:ident),*], $runner_ident: ident, $p:pat => $body:expr) => {
        native_func!(_runner_ident,
            arg0 => {
                let arg0 = arg0.clone();
                $(let $captured = $captured.clone();)*
                Ok(Rc::new(native_func!($runner_ident,
                    arg1 => {
                        let arg0 = arg0.clone();
                        let arg1 = arg1.clone();
                        match (arg0, arg1) {
                            $p => $body,
                            #[allow(unreachable_patterns)]
                            _ => panic!("invalid argument types for curried native function"),
                        }
                    }
                )))
            }
        )
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
            Expr::Ident(_) => {
                let ident_ref = self.program_data.expr_ident_ref[&ExprRef(expr.clone())].clone();

                let (data, mut given_instance) = match ident_ref {
                    IdentRef::Var(var_id, given_instance) => {
                        let data = self.scope.vars[&var_id].clone();
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
            Expr::Brace(statements) => {
                let old_scope = self.scope.clone();
                let result = statements.iter().map(|expr| self.eval(expr.clone())).last();
                self.scope = old_scope;
                match result {
                    Some(result) => result,
                    None => Ok(Rc::new(Object::Unit)),
                }
            }
            Expr::Let(_, assigned_expr, _) => {
                let obj = self.eval(assigned_expr.clone())?;
                let var_id = self.program_data.let_var_ids[&ExprRef(expr.clone())];
                self.scope.vars.insert(var_id, Variable::Var(obj));
                Ok(Rc::new(Object::Unit))
            }
            Expr::Def(_, assigned_expr, _) => {
                let scope = self.scope.clone();
                let var_id = self.program_data.let_var_ids[&ExprRef(expr.clone())];
                let assigned_expr = assigned_expr.clone();
                self.scope.vars.insert(
                    var_id,
                    Variable::Def(Rc::new(move |runner: &mut Runner, instance_replace| {
                        let old_scope = runner.scope.clone();
                        runner.scope = scope.clone();
                        runner.scope.instance_replace.extend(instance_replace);
                        let result = runner.eval(assigned_expr.clone());
                        runner.scope = old_scope;
                        result
                    })),
                );
                Ok(Rc::new(Object::Unit))
            }
            Expr::UnOp(Token::Apostrophe, expr) => {
                let expr = expr.clone();
                Ok(Rc::new(native_func!(runner,
                    Object::Unit => {
                        runner.eval(expr.clone())
                    }
                )))
            }
            Expr::BinOp(_, _, _) => unreachable!(),
            Expr::UnOp(_, _) => unreachable!(),
            Expr::Member(_, _) => todo!(),
        }
    }
    pub fn call(&mut self, func: &Func, param: Rc<Object>) -> errors::Result<Rc<Object>> {
        match &func {
            Func::NativeFunc(inner) => inner(self, param),
            Func::UserDefFunc(_, _) => todo!(),
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
