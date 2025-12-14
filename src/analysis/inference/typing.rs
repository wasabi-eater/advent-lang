use super::*;

#[derive(Clone, PartialEq, Eq)]
pub enum Typing {
    Int,
    Float,
    String,
    Bool,
    Unit,
    Var(TyVar),
    List(Rc<Typing>),
    Arrow(Rc<Typing>, Rc<Typing>),
    Comma(Rc<Typing>, Rc<Typing>),
    TmpTyVar(TmpTyVarId),
}
impl Typing {
    pub fn from(ty: &Type, subst: &FxHashMap<TyVar, Typing>) -> Typing {
        match ty {
            Type::Int => Typing::Int,
            Type::Float => Typing::Float,
            Type::Bool => Typing::Bool,
            Type::String => Typing::String,
            Type::Unit => Typing::Unit,
            &Type::Var(var) => match subst.get(&var) {
                Some(typing) => typing.clone(),
                None => Typing::Var(var),
            },
            Type::List(inner) => Typing::List(Rc::new(Typing::from(inner, subst))),
            Type::Arrow(l, r) => {
                let l: Typing = Typing::from(l, subst);
                let r = Typing::from(r, subst);
                Typing::Arrow(Rc::new(l), Rc::new(r))
            }
            Type::Comma(l, r) => {
                let l = Typing::from(l, subst);
                let r = Typing::from(r, subst);
                Typing::Comma(Rc::new(l), Rc::new(r))
            }
        }
    }
    pub fn try_to_type(&self, arena: &mut TmpTyVarArena) -> errors::Result<Type> {
        match self {
            Typing::Int => Ok(Type::Int),
            Typing::Float => Ok(Type::Float),
            Typing::Bool => Ok(Type::Bool),
            Typing::String => Ok(Type::String),
            Typing::Unit => Ok(Type::Unit),
            &Typing::Var(ty_var) => Ok(Type::Var(ty_var)),
            Typing::List(inner) => Ok(Type::List(Rc::new(inner.try_to_type(arena)?))),
            Typing::Arrow(l, r) => Ok(Type::Arrow(
                Rc::new(l.try_to_type(arena)?),
                Rc::new(r.try_to_type(arena)?),
            )),
            Typing::Comma(l, r) => Ok(Type::Comma(
                Rc::new(l.try_to_type(arena)?),
                Rc::new(r.try_to_type(arena)?),
            )),
            &Typing::TmpTyVar(tmp_ty_var_id) => {
                arena.take_or_err(tmp_ty_var_id)?.try_to_type(arena)
            }
        }
    }
    pub fn display_with(&self, arena: &TmpTyVarArena, f: &mut impl fmt::Write) -> fmt::Result {
        match self {
            Typing::Bool => f.write_str("Bool"),
            Typing::Int => f.write_str("Int"),
            Typing::Float => f.write_str("Float"),
            Typing::String => f.write_str("String"),
            Typing::Unit => f.write_str("()"),
            Typing::Var(var) => write!(f, "var{}", var.index()),
            Typing::Arrow(l, r) => {
                f.write_str("(")?;
                l.display_with(arena, f)?;
                f.write_str(" -> ")?;
                r.display_with(arena, f)?;
                f.write_str(")")
            }
            Typing::Comma(l, r) => {
                f.write_str("(")?;
                l.display_with(arena, f)?;
                f.write_str(", ")?;
                r.display_with(arena, f)?;
                f.write_str(")")
            }
            Typing::List(inner) => {
                f.write_str("[")?;
                inner.display_with(arena, f)?;
                f.write_str("]")
            }
            Typing::TmpTyVar(tmp) => {
                if let Some(ty) = arena.take(*tmp) {
                    ty.display_with(arena, f)
                } else {
                    write!(f, "{tmp:?}")
                }
            }
        }
    }
}
impl Debug for Typing {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Typing::Bool => f.write_str("Bool"),
            Typing::Int => f.write_str("Int"),
            Typing::Float => f.write_str("Float"),
            Typing::String => f.write_str("String"),
            Typing::Unit => f.write_str("()"),
            Typing::Var(var) => write!(f, "{var:?}"),
            Typing::Arrow(l, r) => write!(f, "({:?} -> {:?})", l, r),
            Typing::Comma(l, r) => write!(f, "({:?}, {:?})", l, r),
            Typing::List(inner) => write!(f, "[{:?}]", inner),
            Typing::TmpTyVar(tmp) => write!(f, "?{}", tmp.0),
        }
    }
}
