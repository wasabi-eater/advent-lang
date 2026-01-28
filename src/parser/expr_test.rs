use super::*;
use crate::lexer::*;
use crate::ast::Span;
fn parser<'stream>() -> impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone {
    expr(statement()).then_ignore(end())
}
#[test]
fn lit_test() {
    let input = [Token::Int("34".into())];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::LitInt("34".into(), Span::dummy()).into())
    );

    let input = [Token::Float("3.4".into())];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::LitFloat("3.4".into(), Span::dummy()).into())
    );

    let input = [Token::Str("Hoge".into())];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::LitStr("Hoge".into(), Span::dummy()).into())
    );

    let input = [Token::Ident("Hoge".into())];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Ident("Hoge".into(), Span::dummy()).into())
    );

    let input = [Token::ParenOpen, Token::Int("23".into()), Token::ParenClose];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::LitInt("23".into(), Span::dummy()).into())
    );
}
#[test]
fn member_test() {
    let input = [
        Token::Ident("a".into()),
        Token::Dot,
        Token::Ident("len".into()),
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Member(Expr::Ident("a".into(), Span::dummy()).into(), "len".into(), Span::dummy()).into())
    );

    let input = [
        Token::Ident("a".into()),
        Token::Dot,
        Token::Ident("len".into()),
        Token::Dot,
        Token::Ident("hoge".into()),
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Member(
            Expr::Member(Expr::Ident("a".into(), Span::dummy()).into(), "len".into(), Span::dummy()).into(),
            "hoge".into(),
            Span::dummy()
        )
        .into())
    );
}
#[test]
fn app_fun_test() {
    let input = [
        Token::Ident("f".into()),
        Token::Ident("x".into()),
        Token::Ident("y".into()),
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::AppFun(
            Expr::AppFun(
                Expr::Ident("f".into(), Span::dummy()).into(),
                Expr::Ident("x".into(), Span::dummy()).into(),
                Span::dummy()
            )
            .into(),
            Expr::Ident("y".into(), Span::dummy()).into(),
            Span::dummy()
        )
        .into())
    );
}
#[test]
fn un_op_test() {
    let input = [Token::Minus, Token::Exclamation, Token::Int("34".into())];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::UnOp(
            Token::Minus,
            Expr::UnOp(Token::Exclamation, Expr::LitInt("34".into(), Span::dummy()).into(), Span::dummy()).into(),
            Span::dummy()
        )
        .into())
    );
}
#[test]
fn bin_op_test() {
    let input = [
        Token::Int("34".into()),
        Token::Plus,
        Token::Int("2".into()),
        Token::Mul,
        Token::Int("23".into()),
        Token::Minus,
        Token::Int("4".into()),
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::BinOp(
            Expr::BinOp(
                Expr::LitInt("34".into(), Span::dummy()).into(),
                Token::Plus,
                Expr::BinOp(
                    Expr::LitInt("2".into(), Span::dummy()).into(),
                    Token::Mul,
                    Expr::LitInt("23".into(), Span::dummy()).into(),
                    Span::dummy()
                )
                .into(),
                Span::dummy()
            )
            .into(),
            Token::Minus,
            Expr::LitInt("4".into(), Span::dummy()).into(),
            Span::dummy()
        )
        .into())
    )
}
#[test]
fn term_test() {
    let input = [
        Token::Ident("f".into()),
        Token::ParenOpen,
        Token::Int("2".into()),
        Token::Plus,
        Token::Int("5".into()),
        Token::ParenClose,
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::AppFun(
            Expr::Ident("f".into(), Span::dummy()).into(),
            Expr::BinOp(
                Expr::LitInt("2".into(), Span::dummy()).into(),
                Token::Plus,
                Expr::LitInt("5".into(), Span::dummy()).into(),
                Span::dummy()
            )
            .into(),
            Span::dummy()
        )
        .into())
    );
    let input = [Token::BraceOpen, Token::BraceClose];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Brace(vec![], Span::dummy()).into())
    );
    let input = [Token::BraceOpen, Token::Int("2".into()), Token::BraceClose];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Brace(vec![Expr::LitInt("2".into(), Span::dummy()).into()], Span::dummy()).into())
    );
    let input = [
        Token::BraceOpen,
        Token::Let,
        Token::Ident("x".into()),
        Token::Equal,
        Token::Int("32".into()),
        Token::Semicolon,
        Token::Ident("x".into()),
        Token::BraceClose,
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Brace(vec![
            Expr::Let(
                Pattern::Ident("x".into()).into(),
                Expr::LitInt("32".into(), Span::dummy()).into(),
                None,
                Span::dummy()
            )
            .into(),
            Expr::Ident("x".into(), Span::dummy()).into()
        ],
        Span::dummy())
        .into())
    );
}

#[test]
fn lambda_test() {
    let input = [
        Token::BraceOpen,
        Token::Backslash,
        Token::Ident("x".into()),
        Token::SmallArrow,
        Token::Ident("x".into()),
        Token::Plus,
        Token::Int("1".into()),
        Token::BraceClose,
    ];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Lambda(
            Pattern::Ident("x".into()).into(),
            Expr::Brace(vec![
                Expr::BinOp(
                    Expr::Ident("x".into(), Span::dummy()).into(),
                    Token::Plus,
                    Expr::LitInt("1".into(), Span::dummy()).into(),
                    Span::dummy()
                )
                .into()
            ],
            Span::dummy())
            .into(),
            Span::dummy()
        )
        .into())
    );
}
