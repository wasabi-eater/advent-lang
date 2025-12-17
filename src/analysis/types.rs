use fxhash::FxHashMap;
use im_rc::Vector;
use std::{fmt::Debug, rc::Rc};

use crate::analysis::program_data::ConstraintId;

#[derive(Clone, PartialEq, Eq)]
pub struct TyVarBody {
    pub name: Option<String>,
}
impl TyVarBody {
    pub fn new(name: impl Into<String>) -> Self {
        TyVarBody {
            name: Some(name.into()),
        }
    }
}
pub type TyVar = id_arena::Id<TyVarBody>;
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Float,
    String,
    Bool,
    Unit,
    Var(TyVar),
    List(Rc<Type>),
    Arrow(Rc<Type>, Rc<Type>),
    Comma(Rc<Type>, Rc<Type>),
}
impl Type {
    pub fn subst(&self, subst: &FxHashMap<TyVar, Type>) -> Type {
        match self {
            Type::Int | Type::Float | Type::String | Type::Bool | Type::Unit => self.clone(),
            &Type::Var(v) if subst.contains_key(&v) => subst.get(&v).unwrap().clone(),
            Type::Var(_) => self.clone(),
            Type::List(inner) => Type::List(Rc::new(inner.subst(subst))),
            Type::Arrow(l, r) => Type::Arrow(Rc::new(l.subst(subst)), Rc::new(r.subst(subst))),
            Type::Comma(l, r) => Type::Comma(Rc::new(l.subst(subst)), Rc::new(r.subst(subst))),
        }
    }
    pub fn list(inner: impl Into<Rc<Type>>) -> Self {
        Type::List(inner.into())
    }
    pub fn arrow(param: impl Into<Rc<Type>>, ret: impl Into<Rc<Type>>) -> Self {
        Type::Arrow(param.into(), ret.into())
    }
    pub fn comma(left: impl Into<Rc<Type>>, right: impl Into<Rc<Type>>) -> Self {
        Type::Comma(left.into(), right.into())
    }

    fn assume_subst_inner(&self, r: &Type, subst: &mut FxHashMap<TyVar, Type>) -> bool {
        match (self, r) {
            (Type::Unit, Type::Unit)
            | (Type::Int, Type::Int)
            | (Type::Float, Type::Float)
            | (Type::String, Type::String)
            | (Type::Bool, Type::Bool) => true,
            (Type::Var(left), Type::Var(right)) if left == right => true,
            (Type::Var(var), _) => {
                if let Some(l) = subst.get(var) {
                    Self::assume_subst_inner(&l.clone(), r, subst)
                } else {
                    subst.insert(*var, r.clone());
                    true
                }
            }
            (Type::Arrow(lp, lr), Type::Arrow(rp, rr)) => {
                Self::assume_subst_inner(lp, rp, subst) && Self::assume_subst_inner(lr, rr, subst)
            }
            (Type::Comma(ll, lr), Type::Comma(rl, rr)) => {
                Self::assume_subst_inner(ll, rl, subst) && Self::assume_subst_inner(lr, rr, subst)
            }
            (Type::List(l_inner), Type::List(r_inner)) => {
                Self::assume_subst_inner(l_inner, r_inner, subst)
            }
            _ => false,
        }
    }
    pub fn assume_subst(&self, r: &Type) -> Option<FxHashMap<TyVar, Type>> {
        let mut subst = FxHashMap::default();
        if Self::assume_subst_inner(self, r, &mut subst) {
            Some(subst)
        } else {
            None
        }
    }
}
impl Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => f.write_str("Int"),
            Type::Float => f.write_str("Float"),
            Type::String => f.write_str("String"),
            Type::Bool => f.write_str("Bool"),
            Type::Unit => f.write_str("()"),
            Type::Var(var) => write!(f, "var{:?}", var.index()),
            Type::List(inner) => write!(f, "[{inner:?}]"),
            Type::Arrow(l, r) => write!(f, "{l:?} -> {r:?}"),
            Type::Comma(l, r) => write!(f, "({l:?}, {r:?})"),
        }
    }
}
#[derive(Clone)]
pub struct TypeScheme {
    pub bound_vars: Vector<TyVar>,
    pub ty: Rc<Type>,
    pub constraints: Vector<Rc<Instance>>,
}
impl Debug for TypeScheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("forall ")?;
        let mut is_first = true;
        for &var in &self.bound_vars {
            if is_first {
                write!(f, "{var:?}")?;
            } else {
                write!(f, ", {var:?}")?;
            }
            is_first = false;
        }
        f.write_str(". ")?;
        write!(f, "{:?}", self.ty)
    }
}
impl From<Type> for TypeScheme {
    fn from(ty: Type) -> Self {
        TypeScheme {
            bound_vars: Vector::new(),
            ty: Rc::new(ty),
            constraints: Vector::new(),
        }
    }
}
impl TypeScheme {
    pub fn assume_bound_vars_subst(&self, ty: &Type) -> Option<FxHashMap<TyVar, Type>> {
        let mut subst = FxHashMap::default();
        if self.ty.assume_subst_inner(ty, &mut subst)
            && subst.keys().all(|k| self.bound_vars.contains(k))
        {
            Some(subst)
        } else {
            None
        }
    }
    pub fn forall(
        bound_vars: impl IntoIterator<Item = TyVar>,
        ty: impl Into<Rc<Type>>,
    ) -> TypeScheme {
        TypeScheme {
            bound_vars: bound_vars.into_iter().collect(),
            ty: ty.into(),
            constraints: Vector::new(),
        }
    }
    pub fn forall_with_constraints(
        bound_vars: impl IntoIterator<Item = TyVar>,
        ty: impl Into<Rc<Type>>,
        constraints: impl IntoIterator<Item = Rc<Instance>>,
    ) -> TypeScheme {
        TypeScheme {
            bound_vars: bound_vars.into_iter().collect(),
            ty: ty.into(),
            constraints: constraints.into_iter().collect(),
        }
    }
    pub fn subst(&self, subst: &FxHashMap<TyVar, Type>) -> TypeScheme {
        TypeScheme {
            bound_vars: self.bound_vars.clone(),
            ty: Rc::new(self.ty.subst(subst)),
            constraints: self
                .constraints
                .iter()
                .map(|instance| Rc::new(instance.subst(subst)))
                .collect(),
        }
    }
}
#[derive(Debug)]
pub struct TypeClass {
    pub name: Rc<str>,
    pub bound_vars: Vec<TyVar>,
    pub methods: FxHashMap<Rc<str>, TypeScheme>,
    pub method_constraint_ids: FxHashMap<Rc<str>, Vec<ConstraintId>>,
}
impl TypeClass {
    pub fn method_type_assume_bound_vars_subst(
        &self,
        method_name: &Rc<str>,
        ty: &Type,
    ) -> Option<FxHashMap<TyVar, Type>> {
        let type_scheme = self.methods.get(method_name)?;
        if let Some(subst) = type_scheme.ty.assume_subst(ty)
            && subst
                .keys()
                .all(|k| self.bound_vars.contains(k) || type_scheme.bound_vars.contains(k))
        {
            Some(subst)
        } else {
            None
        }
    }
}
#[derive(Clone)]
pub struct TypeClassRef(pub Rc<TypeClass>);
impl PartialEq for TypeClassRef {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for TypeClassRef {}
impl std::hash::Hash for TypeClassRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (&*self.0 as *const TypeClass as usize).hash(state);
    }
}
impl Debug for TypeClassRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Instance {
    pub class: TypeClassRef,
    pub assigned_types: Vector<Type>,
}

impl Instance {
    pub fn assigned_types_map(&self) -> FxHashMap<TyVar, Type> {
        let mut map = FxHashMap::default();
        for (var, ty) in self
            .class
            .0
            .bound_vars
            .iter()
            .cloned()
            .zip(self.assigned_types.iter().cloned())
        {
            map.insert(var, ty);
        }
        map
    }
    pub fn subst(&self, subst: &FxHashMap<TyVar, Type>) -> Instance {
        let assigned_types = self
            .assigned_types
            .iter()
            .map(|ty| ty.subst(subst))
            .collect();
        Instance {
            class: self.class.clone(),
            assigned_types,
        }
    }
    pub fn method_type_scheme(&self, method_name: &Rc<str>) -> Option<TypeScheme> {
        Some(
            self.class
                .0
                .methods
                .get(method_name)?
                .clone()
                .subst(&self.assigned_types_map()),
        )
    }
    pub fn method_type_schemes(&self) -> FxHashMap<Rc<str>, TypeScheme> {
        let mut map = FxHashMap::default();
        for (name, type_scheme) in &self.class.0.methods {
            map.insert(name.clone(), type_scheme.subst(&self.assigned_types_map()));
        }
        map
    }
    pub fn assume_subst(&self, other: &Instance, subst: &mut FxHashMap<TyVar, Type>) -> bool {
        if self.class != other.class {
            return false;
        }
        for (l_ty, r_ty) in self.assigned_types.iter().zip(other.assigned_types.iter()) {
            if !l_ty.assume_subst_inner(r_ty, subst) {
                return false;
            }
        }
        true
    }
}

#[derive(Debug, Clone)]
pub struct InstanceScheme {
    pub bound_vars: Vector<TyVar>,
    pub instance: Rc<Instance>,
    pub constraints: Vector<Rc<Instance>>,
}
impl InstanceScheme {
    pub fn subst(&self, subst: &FxHashMap<TyVar, Type>) -> InstanceScheme {
        InstanceScheme {
            bound_vars: self.bound_vars.clone(),
            instance: Rc::new(self.instance.subst(subst)),
            constraints: self
                .constraints
                .iter()
                .map(|instance| Rc::new(instance.subst(subst)))
                .collect(),
        }
    }
    pub fn assume_subst(&self, instance: &Instance) -> Option<FxHashMap<TyVar, Type>> {
        let mut subst = FxHashMap::default();
        if InstanceScheme::assume_subst_inner(&self.instance, instance, &mut subst)
            && subst.keys().all(|k| self.bound_vars.contains(k))
        {
            Some(subst)
        } else {
            None
        }
    }
    fn assume_subst_inner(l: &Instance, r: &Instance, subst: &mut FxHashMap<TyVar, Type>) -> bool {
        if l.class != r.class {
            return false;
        }
        for (l_ty, r_ty) in l.assigned_types.iter().zip(r.assigned_types.iter()) {
            if !l_ty.assume_subst_inner(r_ty, subst) {
                return false;
            }
        }
        true
    }
    pub fn method_type_assume_subst(
        &self,
        method_name: &Rc<str>,
        ty: &Type,
    ) -> Option<FxHashMap<TyVar, Type>> {
        let type_scheme = self.instance.method_type_scheme(method_name)?;
        if let Some(subst) = type_scheme.ty.assume_subst(ty)
            && subst
                .keys()
                .all(|k| self.bound_vars.contains(k) || type_scheme.bound_vars.contains(k))
        {
            Some(subst)
        } else {
            None
        }
    }
}
