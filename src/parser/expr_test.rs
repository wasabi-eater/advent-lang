use super::*;
use crate::lexer::*;
fn parser<'stream>() -> impl Parser<'stream, &'stream [Token], Rc<Expr>> + Clone {
    expr(statement()).then_ignore(end())
}
#[test]
fn lit_test() {
    let input = [Token::Int("34".into())];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::LitInt("34".into()).into())
    );

    let input = [Token::Float("3.4".into())];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::LitFloat("3.4".into()).into())
    );

    let input = [Token::Str("Hoge".into())];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::LitStr("Hoge".into()).into())
    );

    let input = [Token::Ident("Hoge".into())];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Ident("Hoge".into()).into())
    );

    let input = [Token::ParenOpen, Token::Int("23".into()), Token::ParenClose];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::LitInt("23".into()).into())
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
        Ok(Expr::Member(Expr::Ident("a".into()).into(), "len".into()).into())
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
            Expr::Member(Expr::Ident("a".into()).into(), "len".into()).into(),
            "hoge".into()
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
                Expr::Ident("f".into()).into(),
                Expr::Ident("x".into()).into()
            )
            .into(),
            Expr::Ident("y".into()).into()
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
            Expr::UnOp(Token::Exclamation, Expr::LitInt("34".into()).into()).into()
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
                Expr::LitInt("34".into()).into(),
                Token::Plus,
                Expr::BinOp(
                    Expr::LitInt("2".into()).into(),
                    Token::Mul,
                    Expr::LitInt("23".into()).into()
                )
                .into()
            )
            .into(),
            Token::Minus,
            Expr::LitInt("4".into()).into()
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
            Expr::Ident("f".into()).into(),
            Expr::BinOp(
                Expr::LitInt("2".into()).into(),
                Token::Plus,
                Expr::LitInt("5".into()).into()
            )
            .into()
        )
        .into())
    );
    let input = [Token::BraceOpen, Token::BraceClose];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Brace(vec![]).into())
    );
    let input = [Token::BraceOpen, Token::Int("2".into()), Token::BraceClose];
    assert_eq!(
        parser().parse(&input).into_result(),
        Ok(Expr::Brace(vec![Expr::LitInt("2".into()).into()]).into())
    );
    let input = [
        Token::BraceOpen,
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
            Expr::Let("x".into(), Expr::LitInt("32".into()).into(), None).into(),
            Expr::Ident("x".into()).into()
        ])
        .into())
    );
}
