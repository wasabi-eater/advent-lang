use super::core::Runner;
use crate::{ast::Expr, runner::errors};
use im_rc::Vector;
use std::{fmt::Debug, rc::Rc};

#[derive(Clone)]
pub enum Object {
    Int(i64),
    Float(f64),
    String(Rc<String>),
    Bool(bool),
    Unit,
    Comma(Rc<Object>, Rc<Object>),
    List(Vector<Rc<Object>>),
    Func(Func),
}

#[derive(Clone)]
pub enum Func {
    UserDefFunc(Rc<str>, Rc<Expr>),
    StdFunc(Rc<dyn for<'a> Fn(&'a mut Runner, Rc<Object>) -> errors::Result<Rc<Object>>>),
}

impl Debug for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::Int(n) => write!(f, "Int({n})"),
            Object::Float(n) => write!(f, "Float({n})"),
            Object::String(s) => write!(f, "String({s})"),
            Object::Bool(b) => write!(f, "Bool({b})"),
            Object::Unit => write!(f, "()"),
            Object::Comma(l, r) => write!(f, "({l:?}, {r:?})"),
            Object::List(elems) => {
                write!(f, "[")?;
                for (i, elem) in elems.iter().enumerate() {
                    if i == 0 {
                        write!(f, "{elem:?}")?;
                    } else {
                        write!(f, ", {elem:?}")?;
                    }
                }
                write!(f, "]")
            }
            Object::Func(_) => write!(f, "Func(...)"),
        }
    }
}