use std::fmt::Debug;
use std::rc::Rc;

use crate::lexer::Token;

/// Source code location information for error reporting
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Create a dummy span for testing or when position is unknown
    pub fn dummy() -> Self {
        Self { start: 0, end: 0 }
    }

    /// Merge two spans into one that covers both
    pub fn merge(&self, other: &Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

impl Default for Span {
    fn default() -> Self {
        Self::dummy()
    }
}

#[derive(Clone)]
pub enum Expr {
    LitInt(Rc<str>, Span),
    LitFloat(Rc<str>, Span),
    LitStr(Rc<str>, Span),
    LitList(Vec<Rc<Expr>>, Span),
    LitBool(bool, Span),
    AppFun(Rc<Expr>, Rc<Expr>, Span),
    BinOp(Rc<Expr>, Token, Rc<Expr>, Span),
    UnOp(Token, Rc<Expr>, Span),
    Member(Rc<Expr>, Rc<str>, Span),
    Ident(Rc<str>, Span),
    Brace(Vec<Rc<Expr>>, Span),
    Unit(Span),
    Let(Rc<Pattern>, Rc<Expr>, Option<Rc<Kind>>, Span),
    Def(Rc<str>, Rc<Expr>, Option<KindLike>, Span),
    Lambda(Rc<Pattern>, Rc<Expr>, Span),
    ImplicitArg(Span),
    Typed(Rc<Expr>, Rc<Kind>, Span),
}

impl Expr {
    /// Get the span of this expression
    pub fn span(&self) -> &Span {
        match self {
            Expr::LitInt(_, span)
            | Expr::LitFloat(_, span)
            | Expr::LitStr(_, span)
            | Expr::LitList(_, span)
            | Expr::LitBool(_, span)
            | Expr::AppFun(_, _, span)
            | Expr::BinOp(_, _, _, span)
            | Expr::UnOp(_, _, span)
            | Expr::Member(_, _, span)
            | Expr::Ident(_, span)
            | Expr::Brace(_, span)
            | Expr::Unit(span)
            | Expr::Let(_, _, _, span)
            | Expr::Def(_, _, _, span)
            | Expr::Lambda(_, _, span)
            | Expr::ImplicitArg(span)
            | Expr::Typed(_, _, span) => span,
        }
    }
}

// Custom PartialEq that ignores Span for easier testing
impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Expr::LitInt(a, _), Expr::LitInt(b, _)) => a == b,
            (Expr::LitFloat(a, _), Expr::LitFloat(b, _)) => a == b,
            (Expr::LitStr(a, _), Expr::LitStr(b, _)) => a == b,
            (Expr::LitList(a, _), Expr::LitList(b, _)) => a == b,
            (Expr::LitBool(a, _), Expr::LitBool(b, _)) => a == b,
            (Expr::AppFun(a1, a2, _), Expr::AppFun(b1, b2, _)) => a1 == b1 && a2 == b2,
            (Expr::BinOp(a1, at, a2, _), Expr::BinOp(b1, bt, b2, _)) => {
                a1 == b1 && at == bt && a2 == b2
            }
            (Expr::UnOp(at, a, _), Expr::UnOp(bt, b, _)) => at == bt && a == b,
            (Expr::Member(a1, a2, _), Expr::Member(b1, b2, _)) => a1 == b1 && a2 == b2,
            (Expr::Ident(a, _), Expr::Ident(b, _)) => a == b,
            (Expr::Brace(a, _), Expr::Brace(b, _)) => a == b,
            (Expr::Unit(_), Expr::Unit(_)) => true,
            (Expr::Let(ap, ae, ak, _), Expr::Let(bp, be, bk, _)) => ap == bp && ae == be && ak == bk,
            (Expr::Def(an, ae, ak, _), Expr::Def(bn, be, bk, _)) => an == bn && ae == be && ak == bk,
            (Expr::Lambda(ap, ae, _), Expr::Lambda(bp, be, _)) => ap == bp && ae == be,
            (Expr::ImplicitArg(_), Expr::ImplicitArg(_)) => true,
            (Expr::Typed(ae, ak, _), Expr::Typed(be, bk, _)) => ae == be && ak == bk,
            _ => false,
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Kind {
    Ident(Rc<str>),
    App(Rc<Kind>, Rc<Kind>),
    Arrow(Rc<Kind>, Rc<Kind>),
    Unit,
    Pair(Rc<Kind>, Rc<Kind>),
    List(Rc<Kind>),
}
#[derive(Clone, PartialEq, Eq)]
pub struct Constraint {
    pub type_class: Rc<str>,
    pub args: Vec<Rc<Kind>>,
}
#[derive(Clone, PartialEq, Eq)]
pub struct KindLike {
    pub bound_vars: Vec<Rc<str>>,
    pub constraints: Vec<Constraint>,
    pub kind: Rc<Kind>,
}
#[derive(Clone, PartialEq, Eq)]
pub enum Pattern {
    Ident(Rc<str>),
    Pair(Rc<Pattern>, Rc<Pattern>),
    Wildcard,
    Unit,
}

impl Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::LitInt(i, _) => write!(f, "{i}"),
            Expr::LitFloat(fl, _) => write!(f, "{fl}"),
            Expr::LitStr(s, _) => write!(f, "\"{s}\""),
            Expr::LitBool(b, _) => write!(f, "{b}"),
            Expr::LitList(list, _) => {
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
            Expr::BinOp(l, op, r, _) => write!(f, "({l:?} {op:?} {r:?})"),
            Expr::UnOp(op, e, _) => write!(f, "({op:?}{e:?})"),
            Expr::AppFun(fun, p, _) => write!(f, "({fun:?} {p:?})"),
            Expr::Member(e, name, _) => write!(f, "({e:?}.{name})"),
            Expr::Ident(name, _) => f.write_str(name),
            Expr::Brace(statements, _) => {
                f.write_str("{")?;
                for statement in statements {
                    write!(f, "{statement:?}; ")?;
                }
                f.write_str("}")?;
                Ok(())
            }
            Expr::Unit(_) => f.write_str("()"),
            Expr::Let(pat, expr, Some(kind), _) => write!(f, "let {pat:?}: {kind:?} = {expr:?}"),
            Expr::Let(pat, expr, None, _) => write!(f, "let {pat:?} = {expr:?}"),
            Expr::Def(name, expr, kind_like, _) => write!(f, "def {name}: {kind_like:?} = {expr:?}"),
            Expr::Lambda(pat, body, _) => write!(f, "(\\{pat:?} -> {body:?})"),
            Expr::ImplicitArg(_) => write!(f, "_"),
            Expr::Typed(inner, kind, _) => write!(f, "({inner:?} : {kind:?})"),
        }
    }
}

impl Debug for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ident(name) => f.write_str(name),
            Self::App(fu, p) => write!(f, "({fu:?} {p:?})"),
            Self::Arrow(l, r) => write!(f, "({l:?} -> {r:?})"),
            Self::Pair(l, r) => write!(f, "({l:?}, {r:?})"),
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
        f.write_str(". ")?;
        if !self.constraints.is_empty() {
            f.write_str("(")?;
            let mut is_first = true;
            for constraint in &self.constraints {
                if is_first {
                    write!(f, "{constraint:?}")?;
                } else {
                    write!(f, ", {constraint:?}")?;
                }
                is_first = false;
            }
            f.write_str(") => ")?;
        }
        write!(f, "{:?}", self.kind)
    }
}

impl Debug for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.type_class)?;
        for arg in self.args.iter() {
            write!(f, " {arg:?}")?;
        }
        Ok(())
    }
}

impl Debug for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Ident(name) => f.write_str(name),
            Pattern::Pair(l, r) => write!(f, "({l:?}, {r:?})"),
            Pattern::Unit => f.write_str("()"),
            Pattern::Wildcard => f.write_str("_"),
        }
    }
}
