use super::types::{Instance, TyVarBody, Type, TypeScheme};
use crate::{analysis::types::TypeClassRef, ast::Expr};
use fxhash::FxHashMap;
use im_rc::Vector;
use std::{hash::Hash, rc::Rc};
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
    pub expr_ident_ref: FxHashMap<ExprRef, IdentRef>,
    pub let_var_ids: FxHashMap<ExprRef, VarId>,
    pub desugaered: FxHashMap<ExprRef, Rc<Expr>>,
    pub extern_funcs: FxHashMap<Rc<str>, (TypeScheme, VarId)>, // name -> (type_scheme, var_id)
    pub type_classes: FxHashMap<Rc<str>, TypeClassRef>,
    pub instances: FxHashMap<TypeClassRef, Vector<Rc<Instance>>>,
    pub method_classes: FxHashMap<Rc<str>, TypeClassRef>,
}
#[derive(Clone, Debug)]
pub enum IdentRef {
    Var(
        VarId,
        im_rc::HashMap<Rc<Instance>, Rc<Instance>, fxhash::FxBuildHasher>,
    ),
    Method(
        Rc<Instance>,
        Rc<str>,
        im_rc::HashMap<Rc<Instance>, Rc<Instance>, fxhash::FxBuildHasher>,
    ),
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
