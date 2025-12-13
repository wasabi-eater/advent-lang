use crate::ast::Expr;
use fxhash::FxHashMap;
use im_rc::Vector;
use std::{fmt::Debug, hash::Hash, rc::Rc};

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
#[derive(Clone, PartialEq, Eq)]
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
    pub fn subst(&self, var: TyVar, ty: &Type) -> Type {
        match self {
            Type::Int | Type::Float | Type::String | Type::Bool | Type::Unit => self.clone(),
            &Type::Var(v) if v == var => ty.clone(),
            Type::Var(_) => self.clone(),
            Type::List(inner) => Type::List(Rc::new(inner.subst(var, ty))),
            Type::Arrow(l, r) => Type::Arrow(Rc::new(l.subst(var, ty)), Rc::new(r.subst(var, ty))),
            Type::Comma(l, r) => Type::Comma(Rc::new(l.subst(var, ty)), Rc::new(r.subst(var, ty))),
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
}
impl Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => f.write_str("Int"),
            Type::Float => f.write_str("Float"),
            Type::String => f.write_str("String"),
            Type::Bool => f.write_str("Bool"),
            Type::Unit => f.write_str("()"),
            Type::Var(var) => write!(f, "{var:?}"),
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
        }
    }
}
impl TypeScheme {
    pub fn assume_subst(&self, ty: &Type) -> Option<FxHashMap<TyVar, Type>> {
        let mut subst = FxHashMap::default();
        if Self::assume_subst_inner(&self.ty, ty, &mut subst) {
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
        }
    }
    fn assume_subst_inner(l: &Type, r: &Type, subst: &mut FxHashMap<TyVar, Type>) -> bool {
        match (l, r) {
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
}

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
