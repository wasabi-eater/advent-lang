use crate::{
    ast::{Expr, Kind, KindLike},
    lexer::Token,
};
use chumsky::prelude::*;
use std::rc::Rc;

#[cfg(test)]
mod expr_test;
#[cfg(test)]
mod statement_test;

pub fn program<'stream>() -> impl Parser<'stream, &'stream [Token], Rc<Expr>> {
    statement()
        .separated_by(just(Token::Semicolon).repeated().at_least(1))
        .allow_leading()
        .allow_trailing()
        .collect::<Vec<Rc<Expr>>>()
        .then_ignore(end())
        .map(|stmts| Rc::new(Expr::Brace(stmts)))
}
fn statement<'stream>() -> impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone {
    recursive(|statement| {
        let expr = expr(statement);
        let ident = select! {
            Token::Ident(s) => s
        };
        choice((
            ident
                .then(just(Token::Colon).ignore_then(kind_like()).or_not())
                .then_ignore(just(Token::Equal))
                .then(expr.clone())
                .map(move |((name, kind_like), e)| Rc::new(Expr::Let(name, e, kind_like))),
            expr,
        ))
    })
}
fn expr<'stream>(
    statement: impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone + 'stream,
) -> impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone {
    recursive(move |expr: Recursive<dyn Parser<'_, &[Token], Rc<Expr>>>| {
        let literal = select! {
            Token::Int(n) => Expr::LitInt(n),
            Token::Float(n) => Expr::LitFloat(n),
            Token::Str(s) => Expr::LitStr(s),
        }
        .map(Rc::new);
        let ident = select! {
            Token::Ident(s) => s
        };
        let var = ident.map(move |name| Rc::new(Expr::Ident(name)));
        let unit = just(Token::ParenOpen)
            .then(just(Token::ParenClose))
            .to(Expr::Unit)
            .map(Rc::new);
        let paren = infixr(expr.clone(), just(Token::Comma))
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .or(unit);
        let statements = statement
            .separated_by(just(Token::Semicolon).repeated().at_least(1))
            .allow_leading()
            .allow_trailing()
            .collect::<Vec<Rc<Expr>>>();
        let brace = statements
            .delimited_by(just(Token::BraceOpen), just(Token::BraceClose))
            .map(move |stmts| Rc::new(Expr::Brace(stmts)));
        let list = expr
            .separated_by(just(Token::Comma))
            .collect::<Vec<_>>()
            .delimited_by(just(Token::BracketOpen), just(Token::BracketClose))
            .map(move |list| Rc::new(Expr::LitList(list)));
        let expr0 = choice((literal, var, paren, brace, list));
        let expr1 = expr0.foldl(
            just(Token::Dot).ignore_then(ident).repeated(),
            move |e, name| Rc::new(Expr::Member(e, name)),
        );
        let expr2 = expr1.clone().foldl(expr1.repeated(), move |f, param| {
            Rc::new(Expr::AppFun(f, param))
        });
        let expr3 = choice((
            just(Token::Minus),
            just(Token::Exclamation),
            just(Token::Apostrophe),
        ))
        .repeated()
        .foldr(expr2, move |op, e| Rc::new(Expr::UnOp(op, e)));
        bin_ops(expr3)
    })
}
fn bin_ops<'stream>(
    term: impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone + 'stream,
) -> impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone {
    let expr3 = infixl(term, just(Token::CompositionLeft));
    let expr4 = infixl(expr3, just(Token::CompositionRight));
    let expr5 = infixl(
        expr4,
        choice((just(Token::Mul), just(Token::Div), just(Token::Mod))),
    );
    let expr6 = infixl(expr5, choice((just(Token::Plus), just(Token::Minus))));
    let expr7 = infixl(expr6, just(Token::ShiftLeft).or(just(Token::ShiftRight)));
    let expr8 = infixl(expr7, just(Token::Amp));
    let expr9 = infixl(expr8, just(Token::Pipe));
    let expr10 = infix(
        expr9,
        choice((
            just(Token::Greater),
            just(Token::Less),
            just(Token::GreaterEqual),
            just(Token::LessEqual),
        )),
    );
    let expr11 = infix(
        expr10,
        choice((just(Token::DoubleEqual), just(Token::NotEqual))),
    );
    let expr12 = infixl(expr11, just(Token::DoubleAmp));
    let expr13 = infixl(expr12, just(Token::DoublePipe));
    let expr14 = infixr(expr13, just(Token::PipeLeft));
    let expr15 = infixl(expr14, just(Token::PipeRight));
    expr15
}
fn infixl<'stream>(
    expr: impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone + 'stream,
    op: impl Parser<'stream, &'stream [Token], Token> + Clone + 'stream,
) -> impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone {
    expr.clone()
        .foldl(op.then(expr).repeated(), |l, (op, r)| {
            Rc::new(Expr::BinOp(l, op, r))
        })
        .boxed()
}
fn infixr<'stream>(
    expr: impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone + 'stream,
    op: impl Parser<'stream, &'stream [Token], Token> + Clone + 'stream,
) -> impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone {
    expr.clone()
        .then(op)
        .repeated()
        .foldr(expr, |(l, op), r| Rc::new(Expr::BinOp(l, op, r)))
        .boxed()
}
fn infix<'stream>(
    expr: impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone + 'stream,
    op: impl Parser<'stream, &'stream [Token], Token> + Clone + 'stream,
) -> impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone {
    expr.clone()
        .then(op.then(expr).or_not())
        .map(move |(l, succ)| match succ {
            Some((op, r)) => Rc::new(Expr::BinOp(l, op, r)),
            None => l,
        })
        .boxed()
}
fn kind<'stream>() -> impl Parser<'stream, &'stream [Token], Rc<Kind>> + Clone {
    recursive(|kind| {
        let ident = select! {
            Token::Ident(name) => Rc::new(Kind::Ident(name))
        };
        let paren = kind
            .clone()
            .then_ignore(just(Token::Comma))
            .repeated()
            .foldr(kind.clone(), |l, r| Rc::new(Kind::Comma(l, r)))
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose));
        let list = kind
            .delimited_by(just(Token::BracketOpen), just(Token::BracketClose))
            .map(|inner| Rc::new(Kind::List(inner)));
        let term = choice((ident, paren, list));
        let app = term
            .clone()
            .foldl(term.repeated(), |f, p| Rc::new(Kind::App(f, p)));
        let arrow = app
            .clone()
            .then_ignore(just(Token::SmallArrow))
            .repeated()
            .foldr(app, |l, r| Rc::new(Kind::Arrow(l, r)));
        arrow
    })
}
fn kind_like<'a: 'stream, 'stream, 's: 'a + 'stream>()
-> impl Parser<'stream, &'stream [Token], KindLike> + Clone {
    let var = select! {
        Token::Ident(name) => name
    };
    let bound_vars = var
        .separated_by(just(Token::Comma))
        .collect::<Vec<_>>()
        .delimited_by(just(Token::Forall), just(Token::Dot))
        .or_not()
        .map(|opt| opt.unwrap_or(Vec::default()));
    bound_vars
        .then(kind())
        .map(|(bound_vars, kind)| KindLike { bound_vars, kind })
}
