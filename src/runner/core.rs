use super::{errors, obj::Object};
use std::rc::Rc;

use fxhash::FxHashMap;
use itertools::Itertools;

use crate::{
    analysis::{
        program_data::{ExprRef, IdentRef, ProgramData, VarId},
        types::Instance,
    },
    ast::Expr,
    runner::obj::Func,
    std_lib,
};

pub struct Runner {
    program_data: ProgramData,
    scope: Scope,
    pub instance_methods: FxHashMap<Rc<Instance>, FxHashMap<Rc<str>, Variable>>,
}
pub type DefInner = Rc<
    dyn Fn(
        &mut Runner,
        im_rc::HashMap<Rc<Instance>, Rc<Instance>, fxhash::FxBuildHasher>,
    ) -> errors::Result<Rc<Object>>,
>;
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

#[derive(Default, Clone)]
pub struct Scope {
    vars: im_rc::HashMap<VarId, Variable, fxhash::FxBuildHasher>,
    instance_replace: im_rc::HashMap<Rc<Instance>, Rc<Instance>, fxhash::FxBuildHasher>,
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
                instance_replace: im_rc::HashMap::default(),
            },
            instance_methods: std_lib.instance_methods,
        }
    }
    pub fn read_var(
        &mut self,
        variable: &Variable,
        given_instance: im_rc::HashMap<Rc<Instance>, Rc<Instance>, fxhash::FxBuildHasher>,
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
                    IdentRef::Method(instance, method_name, given_instance) => {
                        let data = self.instance_methods[&instance][&method_name].clone();
                        (data, given_instance)
                    }
                };
                for (_, to) in given_instance.iter_mut() {
                    if let Some(repl) = self.scope.instance_replace.get(&to.clone()) {
                        *to = repl.clone();
                    }
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
    pub fn replace_instance(&self, mut instance: Rc<Instance>) -> Rc<Instance> {
        while let Some(repl) = self.scope.instance_replace.get(&instance) {
            instance = repl.clone();
        }
        instance
    }
}
