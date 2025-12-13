use crate::{
    analysis::inference::{TmpTyVarArena, TmpTyVarId, Typing},
    ast::Expr,
};
use std::{fmt::Debug, rc::Rc};

pub enum Error {
    UndefiedIdent(Rc<str>),
    TypeMismatch {
        expr: Rc<Expr>,
        expected: Typing,
        actual: Typing,
        arena: TmpTyVarArena,
    },
    UnknownType {
        tmp_id: TmpTyVarId,
        arena: TmpTyVarArena,
    },
    AmbigiousOverload {
        tys: Vec<Typing>,
        tmp_id: TmpTyVarId,
        arena: TmpTyVarArena,
    },
    IntegerOutOfSize(Rc<Expr>),
}
pub type Result<T> = std::result::Result<T, Error>;

impl Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UndefiedIdent(name) => write!(f, "undefined ident: {name}!"),
            Self::UnknownType { tmp_id, .. } => write!(f, "{:?} is unspecified!", tmp_id),
            Self::AmbigiousOverload { tys, tmp_id, arena } => {
                write!(f, "overload unspecified of {tmp_id:?}: (")?;
                for (i, ty) in tys.iter().enumerate() {
                    if i == 0 {
                        ty.display_with(arena, f)?;
                    } else {
                        ty.display_with(arena, f)?;
                    }
                }
                write!(f, ")")
            }
            Self::TypeMismatch {
                expr,
                expected,
                actual,
                arena,
            } => {
                writeln!(f, "type mismatch of {expr:?}")?;
                writeln!(f, "expected: ")?;
                expected.display_with(arena, f)?;
                write!(f, "\nactual: ")?;
                actual.display_with(arena, f)
            }
            Self::IntegerOutOfSize(expr) => {
                write!(f, "int {expr:?} is out of size")
            }
        }
    }
}
