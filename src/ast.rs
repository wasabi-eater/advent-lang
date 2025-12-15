use std::fmt::Debug;
use std::rc::Rc;

use crate::lexer::Token;

#[derive(Clone, PartialEq)]
pub enum Expr {
    LitInt(Rc<str>),
    LitFloat(Rc<str>),
    LitStr(Rc<str>),
    LitList(Vec<Rc<Expr>>),
    AppFun(Rc<Expr>, Rc<Expr>),
    BinOp(Rc<Expr>, Token, Rc<Expr>),
    UnOp(Token, Rc<Expr>),
    Member(Rc<Expr>, Rc<str>),
    Ident(Rc<str>),
    Brace(Vec<Rc<Expr>>),
    Unit,
    Let(Rc<str>, Rc<Expr>, Option<Rc<Kind>>),
    Def(Rc<str>, Rc<Expr>, KindLike),
}
#[derive(Clone, PartialEq, Eq)]
pub enum Kind {
    Ident(Rc<str>),
    App(Rc<Kind>, Rc<Kind>),
    Arrow(Rc<Kind>, Rc<Kind>),
    Unit,
    Comma(Rc<Kind>, Rc<Kind>),
    List(Rc<Kind>),
}

#[derive(Clone, PartialEq, Eq)]
pub struct KindLike {
    pub bound_vars: Vec<Rc<str>>,
    pub kind: Rc<Kind>,
}

impl Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::LitInt(i) => write!(f, "{i}"),
            Expr::LitFloat(fl) => write!(f, "{fl}"),
            Expr::LitStr(s) => write!(f, "\"{s}\""),
            Expr::LitList(list) => {
                f.write_str("[")?;
                let mut is_first = true;
                for item in list {
                    if is_first {
                        write!(f, "{item:?}")?;
                    } else {
                        write!(f, ", {item:?}")?;
                    }
                    is_first = false;
                }
                f.write_str("]")
            }
            Expr::BinOp(l, op, r) => write!(f, "({l:?} {op:?} {r:?})"),
            Expr::UnOp(op, e) => write!(f, "({op:?}{e:?})"),
            Expr::AppFun(fun, p) => write!(f, "({fun:?} {p:?})"),
            Expr::Member(e, name) => write!(f, "({e:?}.{name})"),
            Expr::Ident(name) => f.write_str(name),
            Expr::Brace(statements) => {
                f.write_str("{")?;
                for statement in statements {
                    write!(f, "{statement:?}; ")?;
                }
                f.write_str("}")?;
                Ok(())
            }
            Expr::Unit => f.write_str("()"),
            Expr::Let(name, expr, Some(kind)) => write!(f, "{name}: {kind:?} = {expr:?}"),
            Expr::Let(name, expr, None) => write!(f, "{name} = {expr:?}"),
            Expr::Def(name, expr, kind_like) => write!(f, "{name}: {kind_like:?} = {expr:?}"),
        }
    }
}

impl Debug for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ident(name) => f.write_str(name),
            Self::App(fu, p) => write!(f, "({fu:?} {p:?})"),
            Self::Arrow(l, r) => write!(f, "({l:?} -> {r:?})"),
            Self::Comma(l, r) => write!(f, "({l:?}, {r:?})"),
            Self::List(inner) => write!(f, "[{inner:?}]"),
            Self::Unit => f.write_str("()"),
        }
    }
}

impl Debug for KindLike {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("forall ")?;
        let mut is_first = true;
        for var in &self.bound_vars {
            if is_first {
                f.write_str(var)?;
            } else {
                write!(f, ", {var}")?;
            }
            is_first = false;
        }
        write!(f, ". {:?}", self.kind)
    }
}