use crate::{
    analysis::{
        inference::{TmpTyVarArena, TmpTyVarId, typing::Typing},
        types::Instance,
    },
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
    AmbiguousInstance {
        instance: Rc<Instance>,
    },
    IntegerOutOfSize(Rc<Expr>),
    MissingInstance {
        instance: Rc<Instance>,
    },
}
pub type Result<T> = std::result::Result<T, Error>;

impl Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UndefiedIdent(name) => write!(f, "undefined ident: {name}!"),
            Self::UnknownType { tmp_id, .. } => write!(f, "{:?} is unspecified!", tmp_id),
            Self::AmbiguousInstance { instance } => {
                write!(f, "overload unspecified of {}: (", instance.class.0.name)?;
                for ty in &instance.assigned_types {
                    write!(f, "{ty:?}, ")?;
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
            Self::MissingInstance { instance } => {
                write!(
                    f,
                    "missing instance: {}({:?})",
                    instance.class.0.name, instance.assigned_types
                )
            }
        }
    }
}
