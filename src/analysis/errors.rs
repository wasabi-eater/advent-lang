use crate::{
    analysis::{
        inference::TmpTyVarArena,
        types::{Instance, TypeClassRef, TmpTyVarId, Typing},
    },
    ast::Expr,
};
use std::fmt;
use std::rc::Rc;


#[derive(Debug)]
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
    ImperfectInstanceParam {
        type_class: TypeClassRef,
        shortage_param_count: usize,
    },
    TooManyInstanceParam {
        type_class: TypeClassRef,
    },
    UnknownTypeClassName {
        type_class_name: Rc<str>,
    },
    EscapingImplicitArg,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UndefiedIdent(name) => write!(f, "undefined ident: {name}"),
            Self::UnknownType { tmp_id, .. } => write!(f, "{:?} is unspecified", tmp_id),
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
            Self::ImperfectInstanceParam {
                type_class,
                shortage_param_count,
            } => {
                write!(
                    f,
                    "imperfect instance param count for {}: shortage {} param(s)",
                    type_class.0.name, shortage_param_count
                )
            }
            Self::UnknownTypeClassName { type_class_name } => {
                write!(f, "unknown type class name: {}", type_class_name)
            }
            Self::TooManyInstanceParam { type_class } => {
                write!(f, "too many instance param count for {}", type_class.0.name)
            }
            Self::EscapingImplicitArg => {
                write!(f, "implicit argument escapes its scope")
            }
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;
