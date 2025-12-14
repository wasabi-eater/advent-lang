use super::{errors, obj::Object};
use std::rc::Rc;

use fxhash::FxHashMap;
use itertools::Itertools;

use crate::{
    analysis::{types::{TypeScheme}, program_data::{ExprRef, ProgramData, VarId}},
    ast::Expr,
    runner::obj::Func,
};

pub struct Runner {
    program_data: ProgramData,
    scope: Scope,
}
#[derive(Default)]
pub struct Scope {
    parent: Option<Box<Scope>>,
    vars: FxHashMap<VarId, Rc<Object>>,
}
impl Scope {
    fn get(&self, var_id: VarId) -> errors::Result<Rc<Object>> {
        match self.vars.get(&var_id) {
            Some(obj) => Ok(obj.clone()),
            None => self.parent.as_ref().unwrap().get(var_id),
        }
    }
    fn with_parent(parent: Scope) -> Self {
        Self {
            parent: Some(Box::new(parent)),
            vars: FxHashMap::default(),
        }
    }
}

impl Runner {
    pub fn new(
        program_data: ProgramData,
        extern_funcs: FxHashMap<VarId, (Rc<str>, TypeScheme, Rc<Object>)>,
    ) -> Self {
        Self {
            program_data,
            scope: Scope {
                parent: None,
                vars: extern_funcs
                    .into_iter()
                    .map(|(var_id, (_, _, obj))| (var_id, obj))
                    .collect(),
            },
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
                let var_id = self.program_data.expr_var_id[&ExprRef(expr.clone())];
                self.scope.get(var_id)
            }
            Expr::Brace(statements) => {
                self.scope = Scope::with_parent(std::mem::take(&mut self.scope));
                let result = statements.iter().map(|expr| self.eval(expr.clone())).last();
                self.scope = *std::mem::take(&mut self.scope).parent.unwrap();
                match result {
                    Some(result) => result,
                    None => Ok(Rc::new(Object::Unit)),
                }
            }
            Expr::Let(_, assigned_expr, _) => {
                let obj = self.eval(assigned_expr.clone())?;
                let var_id = self.program_data.expr_var_id[&ExprRef(expr.clone())];
                self.scope.vars.insert(var_id, obj);
                Ok(Rc::new(Object::Unit))
            }
            Expr::BinOp(_, _, _) => unreachable!(),
            Expr::UnOp(_, _) => unreachable!(),
            Expr::Member(_, _) => todo!(),
        }
    }
    pub fn call(&mut self, func: &Func, param: Rc<Object>) -> errors::Result<Rc<Object>> {
        match func {
            Func::NativeFunc(inner) => inner(self, param),
            Func::UserDefFunc(_, _) => todo!(),
        }
    }
}
