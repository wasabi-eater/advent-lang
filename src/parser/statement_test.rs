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
        Token::Ident("v".into()),
        Token::Equal,
        Token::Int("23".into()),
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Let("v".into(), Expr::LitInt("23".into()).into(), None).into())
    );
}
#[test]
fn type_declaration_test() {
    let input = [
        Token::Ident("x".into()),
        Token::Colon,
        Token::Ident("Int".into()),
        Token::Equal,
        Token::Int("5".into()),
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Let(
            "x".into(),
            Expr::LitInt("5".into()).into(),
            Some(KindLike {
                bound_vars: vec![],
                kind: Kind::Ident("Int".into()).into()
            })
        )
        .into())
    );
    let input = [
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
            "x".into(),
            Expr::Ident("id".into()).into(),
            Some(KindLike {
                bound_vars: vec![],
                kind: Kind::Arrow(
                    Kind::Ident("Int".into()).into(),
                    Kind::Ident("Int".into()).into()
                )
                .into()
            })
        )
        .into())
    );
    let input = [
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
        Ok(Expr::Let(
            "unknown".into(),
            Expr::Ident("panic".into()).into(),
            Some(KindLike {
                bound_vars: vec!["a".into()],
                kind: Kind::Ident("a".into()).into()
            })
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
            Expr::Let("x".into(), Expr::LitFloat("2.3".into()).into(), None).into(),
            Expr::BinOp(
                Expr::LitFloat("5.0".into()).into(),
                Token::Plus,
                Expr::Ident("x".into()).into()
            )
            .into()
        ])
    )
}
