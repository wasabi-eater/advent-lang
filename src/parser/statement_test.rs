use super::*;
use std::rc::Rc;
fn parser<'stream>() -> impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone {
    statement().then_ignore(end())
}
fn parser_statements<'stream>() -> impl Parser<'stream, &'stream [Token], Vec<Rc<Expr>>> + Clone {
    statement()
        .separated_by(just(Token::Semicolon).repeated().at_least(1))
        .allow_leading()
        .allow_trailing()
        .collect::<Vec<Rc<Expr>>>()
        .then_ignore(end())
}
#[test]
fn expr_test() {
    let input = [Token::Int("34".into()), Token::Plus, Token::Int("2".into())];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::BinOp(
            Expr::LitInt("34".into()).into(),
            Token::Plus,
            Expr::LitInt("2".into()).into()
        )
        .into())
    );
}
#[test]
fn var_test() {
    let input = [Token::Ident("v".into())];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Ident("v".into()).into())
    );
}

#[test]
fn let_test() {
    let input = [
        Token::Let,
        Token::Ident("v".into()),
        Token::Equal,
        Token::Int("23".into()),
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Let(
            Pattern::Ident("v".into()).into(),
            Expr::LitInt("23".into()).into(),
            None
        )
        .into())
    );
}
#[test]
fn type_declaration_test() {
    let input = [
        Token::Let,
        Token::Ident("x".into()),
        Token::Colon,
        Token::Ident("Int".into()),
        Token::Equal,
        Token::Int("5".into()),
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Let(
            Pattern::Ident("x".into()).into(),
            Expr::LitInt("5".into()).into(),
            Some(Kind::Ident("Int".into()).into())
        )
        .into())
    );
    let input = [
        Token::Let,
        Token::Ident("x".into()),
        Token::Colon,
        Token::Ident("Int".into()),
        Token::SmallArrow,
        Token::Ident("Int".into()),
        Token::Equal,
        Token::Ident("id".into()),
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Let(
            Pattern::Ident("x".into()).into(),
            Expr::Ident("id".into()).into(),
            Some(
                Kind::Arrow(
                    Kind::Ident("Int".into()).into(),
                    Kind::Ident("Int".into()).into()
                )
                .into()
            )
        )
        .into())
    );
    let input = [
        Token::Def,
        Token::Ident("unknown".into()),
        Token::Colon,
        Token::Forall,
        Token::Ident("a".into()),
        Token::Dot,
        Token::Ident("a".into()),
        Token::Equal,
        Token::Ident("panic".into()),
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Def(
            "unknown".into(),
            Expr::Ident("panic".into()).into(),
            KindLike {
                bound_vars: vec!["a".into()],
                constraints: vec![],
                kind: Kind::Ident("a".into()).into()
            }
        )
        .into())
    );

    let input = [
        Token::Def,
        Token::Ident("print".into()),
        Token::Colon,
        Token::Forall,
        Token::Ident("a".into()),
        Token::Dot,
        Token::Ident("Show".into()),
        Token::Ident("a".into()),
        Token::BigArrow,
        Token::Ident("a".into()),
        Token::SmallArrow,
        Token::ParenOpen,
        Token::ParenClose,
        Token::Equal,
        Token::Ident("unimplemented".into()),
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Def(
            "print".into(),
            Expr::Ident("unimplemented".into()).into(),
            KindLike {
                bound_vars: vec!["a".into()],
                constraints: vec![Constraint {
                    type_class: "Show".into(),
                    args: vec![Kind::Ident("a".into()).into()]
                }],
                kind: Kind::Arrow(Kind::Ident("a".into()).into(), Kind::Unit.into()).into()
            }
        )
        .into())
    );
}
#[test]
fn statements_test() {
    let input = [];
    assert_eq!(parser_statements().parse(&input).into_result(), Ok(vec![]));
    let input = [
        Token::Semicolon,
        Token::Float("5.0".into()),
        Token::Plus,
        Token::Ident("x".into()),
        Token::Semicolon,
        Token::Ident("x".into()),
        Token::Semicolon,
    ];
    assert_eq!(
        parser_statements().parse(&input).into_result(),
        Ok(vec![
            Expr::BinOp(
                Expr::LitFloat("5.0".into()).into(),
                Token::Plus,
                Expr::Ident("x".into()).into()
            )
            .into(),
            Expr::Ident("x".into()).into()
        ])
    );

    let input = [
        Token::Let,
        Token::Ident("x".into()),
        Token::Equal,
        Token::Float("2.3".into()),
        Token::Semicolon,
        Token::Float("5.0".into()),
        Token::Plus,
        Token::Ident("x".into()),
    ];
    assert_eq!(
        parser_statements().parse(&input).into_result(),
        Ok(vec![
            Expr::Let(
                Pattern::Ident("x".into()).into(),
                Expr::LitFloat("2.3".into()).into(),
                None
            )
            .into(),
            Expr::BinOp(
                Expr::LitFloat("5.0".into()).into(),
                Token::Plus,
                Expr::Ident("x".into()).into()
            )
            .into()
        ])
    )
}

#[test]
fn constraint_test() {
    let input = [Token::Ident("Show".into()), Token::Ident("a".into())];
    assert_eq!(
        constraint().parse(&input).into_result(),
        Ok(Constraint {
            type_class: "Show".into(),
            args: vec![Kind::Ident("a".into()).into()]
        })
    );
}

#[test]
fn constraints_test() {
    let input = [
        Token::ParenOpen,
        Token::Ident("Show".into()),
        Token::Ident("a".into()),
        Token::Comma,
        Token::Ident("Eq".into()),
        Token::Ident("a".into()),
        Token::ParenClose,
    ];
    assert_eq!(
        constraints().parse(&input).into_result(),
        Ok(vec![
            Constraint {
                type_class: "Show".into(),
                args: vec![Kind::Ident("a".into()).into()]
            },
            Constraint {
                type_class: "Eq".into(),
                args: vec![Kind::Ident("a".into()).into()]
            },
        ])
    );
    let input = [Token::Ident("Show".into()), Token::Ident("a".into())];
    assert_eq!(
        constraints().parse(&input).into_result(),
        Ok(vec![Constraint {
            type_class: "Show".into(),
            args: vec![Kind::Ident("a".into()).into()]
        },])
    );
}
