use std::{rc::Rc, hash::Hash};
use super::types::{Type, TypeScheme, TyVarBody, Instance};
use fxhash::FxHashMap;
use im_rc::Vector;
use crate::ast::Expr;
#[derive(Clone)]
pub struct VarData {
    pub name: Rc<str>,
    pub ty: TypeScheme,
}
pub type VarId = id_arena::Id<VarData>;
pub struct ProgramData {
    pub tyvar_arena: id_arena::Arena<TyVarBody>,
    pub var_arena: id_arena::Arena<VarData>,
    pub expr_ty: FxHashMap<ExprRef, Rc<Type>>,
    pub expr_var_id: FxHashMap<ExprRef, VarId>,
    pub desugaered: FxHashMap<ExprRef, Rc<Expr>>,
    pub extern_funcs: FxHashMap<Rc<str>, Vector<(TypeScheme, VarId, Option<Rc<Instance>>)>>, // name -> (type_scheme, var_id, instance)
}

#[derive(Clone, Debug)]
pub struct ExprRef(pub Rc<Expr>);
impl Hash for ExprRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (self.0.as_ref() as *const _ as usize).hash(state);
    }
}
impl PartialEq for ExprRef {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0.as_ref(), other.0.as_ref())
    }
}
impl Eq for ExprRef {}
