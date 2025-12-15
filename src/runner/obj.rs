use super::core::Runner;
use crate::{analysis::types::Instance, ast::Expr, runner::errors};
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
    NativeFunc(Rc<dyn for<'a> Fn(&'a mut Runner, Rc<Object>) -> errors::Result<Rc<Object>>>),
}

impl Debug for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::Int(n) => write!(f, "{n}"),
            Object::Float(n) => write!(f, "{n}f"),
            Object::String(s) => write!(f, "\"{}\"", s.escape_debug()),
            Object::Bool(b) => write!(f, "{b}"),
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

impl Func {
    pub fn composition(self, g: Self) -> Self {
        Self::NativeFunc(Rc::new(move |runner: &mut Runner, obj| {
            let obj = runner.call(&self, obj)?;
            runner.call(&g, obj)
        }))
    }
}
