use super::types::{Instance, TyVarBody, Type, TypeScheme};
use crate::{
    analysis::types::{InstanceScheme, TypeClassRef},
    ast::Expr,
};
use fxhash::FxHashMap;
use im_rc::Vector;
use std::{hash::Hash, rc::Rc};
#[derive(Clone)]
pub struct VarData {
    pub name: Rc<str>,
    pub ty: TypeScheme,
    pub constraints: Vector<ConstraintId>,
}
pub type VarId = id_arena::Id<VarData>;
pub struct ProgramData {
    pub tyvar_arena: id_arena::Arena<TyVarBody>,
    pub var_arena: id_arena::Arena<VarData>,
    pub expr_ty: FxHashMap<ExprRef, Rc<Type>>,
    pub expr_ident_ref: FxHashMap<ExprRef, IdentRef>,
    pub def_var_ids: FxHashMap<ExprRef, VarId>,
    pub pat_var_ids: FxHashMap<PatternRef, VarId>,
    pub desugaered: FxHashMap<ExprRef, Rc<Expr>>,
    pub extern_funcs: FxHashMap<Rc<str>, (TypeScheme, VarId)>, // name -> (type_scheme, var_id)
    pub type_classes: FxHashMap<Rc<str>, TypeClassRef>,
    pub instances: FxHashMap<TypeClassRef, Vector<InstanceDefId>>,
    pub instance_arena: InstanceArena,
    pub method_classes: FxHashMap<Rc<str>, TypeClassRef>,
    pub implicit_arg_index: FxHashMap<ExprRef, usize>,
    pub partial_app_arg_types: FxHashMap<ExprRef, Vector<Rc<Type>>>,
}

pub type ConstraintAssign = im_rc::HashMap<ConstraintId, InstanceRef, fxhash::FxBuildHasher>;

#[derive(Clone, Debug)]
pub enum IdentRef {
    Var(VarId, ConstraintAssign),
    Method(InstanceRef, Rc<str>, ConstraintAssign),
}
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum InstanceRef {
    Given(ConstraintId),
    Def(InstanceDefId, ConstraintAssign),
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
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for ExprRef {}

#[derive(Clone, Debug)]
pub struct PatternRef(pub Rc<crate::ast::Pattern>);
impl Hash for PatternRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (self.0.as_ref() as *const _ as usize).hash(state);
    }
}
impl PartialEq for PatternRef {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for PatternRef {}

pub struct InstanceDef {
    pub scheme: InstanceScheme,
    pub constraints: Vec<ConstraintId>,
}
pub struct Constraint {
    pub instance: Rc<Instance>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InstanceDefId(usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ConstraintId(usize);
pub struct InstanceArena {
    instance_def: Vec<InstanceDef>,
    constraints: Vec<Constraint>,
}
impl InstanceArena {
    pub fn new() -> Self {
        Self {
            instance_def: Vec::new(),
            constraints: Vec::new(),
        }
    }
    pub fn insert_def(&mut self, instance: InstanceDef) -> InstanceDefId {
        let id = InstanceDefId(self.instance_def.len());
        self.instance_def.push(instance);
        id
    }
    pub fn get_def(&self, id: InstanceDefId) -> &InstanceDef {
        &self.instance_def[id.0]
    }
    pub fn insert_constraint(&mut self, constraint: Constraint) -> ConstraintId {
        let id = ConstraintId(self.constraints.len());
        self.constraints.push(constraint);
        id
    }
    pub fn get_constraint(&self, id: ConstraintId) -> &Constraint {
        &self.constraints[id.0]
    }
    pub fn get_instance(&self, inst_ref: &InstanceRef) -> Rc<Instance> {
        match inst_ref {
            InstanceRef::Given(id) => self.get_constraint(*id).instance.clone(),
            InstanceRef::Def(def_id, constraints) => {
                let mut subst = FxHashMap::default();
                for (constraint_id, assigned) in constraints {
                    let constraint = self.get_constraint(*constraint_id);
                    let assigned = self.get_instance(assigned);
                    assert!(constraint.instance.assume_subst(&assigned, &mut subst));
                }
                let def = self.get_def(*def_id);
                Rc::new(def.scheme.instance.subst(&subst))
            }
        }
    }
    pub fn get_class_of_ref(&self, inst_ref: &InstanceRef) -> TypeClassRef {
        match inst_ref {
            InstanceRef::Given(id) => {
                let instance = &self.get_constraint(*id).instance;
                instance.class.clone()
            }
            InstanceRef::Def(def_id, _) => {
                let def = self.get_def(*def_id);
                def.scheme.instance.class.clone()
            }
        }
    }
}
impl Default for InstanceArena {
    fn default() -> Self {
        Self::new()
    }
}
