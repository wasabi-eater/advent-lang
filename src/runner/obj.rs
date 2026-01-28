use super::core::Runner;
use crate::{
    ast::{Expr, Pattern},
    runner::{core::Scope, errors},
};
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
    /// User-defined function: (parameter pattern, body expression, captured scope)
    /// The Scope is wrapped in Rc to avoid deep cloning on each function call
    UserDefFunc(Rc<Pattern>, Rc<Expr>, Rc<Scope>),
    /// Partial application: (body expression, captured scope, argument count, captured args)
    /// Scope sharing reduces memory overhead when storing partial applications
    PartialApp(Rc<Expr>, Rc<Scope>, usize, Vector<Rc<Object>>),
    NativeFunc(NativeFuncInner),
}
pub type NativeFuncInner = Rc<dyn Fn(&mut Runner, Rc<Object>) -> errors::Result<Rc<Object>>>;

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
