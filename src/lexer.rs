use itertools::Itertools;
use logos::Logos;
use std::rc::Rc;

#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(skip r"\s+")]
pub enum Token {
    #[regex("[0-9]+", |lex| Rc::from(lex.slice()))]
    Int(Rc<str>),
    #[regex(r"[0-9]+\.[0-9]+", |lex| Rc::from(lex.slice()))]
    Float(Rc<str>),
    #[regex(r#""([^"\\\x00-\x1F]|\\(["\\bnfrt/]|u[a-fA-F0-9]{4}))*""#, |lex| Rc::from(&lex.slice()[1..lex.slice().len()-1]))]
    Str(Rc<str>),
    #[token("(")]
    ParenOpen,
    #[token(")")]
    ParenClose,
    #[token("[")]
    BracketOpen,
    #[token("]")]
    BracketClose,
    #[token("{")]
    BraceOpen,
    #[token("}")]
    BraceClose,
    #[token("=>")]
    BigArrow,
    #[token("->")]
    SmallArrow,
    #[token(".>")]
    CompositionRight,
    #[token("<.")]
    CompositionLeft,
    #[token("|>")]
    PipeRight,
    #[token("<|")]
    PipeLeft,
    #[token("<<")]
    ShiftLeft,
    #[token(">>")]
    ShiftRight,
    #[token("||")]
    DoublePipe,
    #[token("|")]
    Pipe,
    #[token("&&")]
    DoubleAmp,
    #[token("&")]
    Amp,
    #[token(">=")]
    GreaterEqual,
    #[token("<=")]
    LessEqual,
    #[token(">")]
    Greater,
    #[token("<")]
    Less,
    #[token("==")]
    DoubleEqual,
    #[token("!=")]
    NotEqual,
    #[token("=")]
    Equal,
    #[token(";")]
    Semicolon,
    #[token(":")]
    Colon,
    #[token(",")]
    Comma,
    #[token(".")]
    Dot,
    #[token("#")]
    Sharp,
    #[token("!")]
    Exclamation,
    #[token("'")]
    Apostrophe,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Mul,
    #[token("/")]
    Div,
    #[token("%")]
    Mod,
    #[token("\\")]
    Backslash,
    #[regex(r"([[:alpha:]]|_)([[:alnum:]]|_)*", |lex| Rc::from(lex.slice()))]
    Ident(Rc<str>),
    Forall,
    Let,
    Def,
    True,
    False,
    Underscore,
}

pub fn tokenize(src: &str) -> Option<Vec<Token>> {
    Token::lexer(src)
        .map_ok(|token| match token {
            Token::Ident(word) if &*word == "forall" => Token::Forall,
            Token::Ident(word) if &*word == "def" => Token::Def,
            Token::Ident(word) if &*word == "let" => Token::Let,
            Token::Ident(word) if &*word == "true" => Token::True,
            Token::Ident(word) if &*word == "false" => Token::False,
            Token::Ident(word) if &*word == "_" => Token::Underscore,
            other => other,
        })
        .try_collect()
        .ok()
}

impl Token {
    pub fn binop_to_str(&self) -> &'static str {
        match self {
            Token::Plus => "+",
            Token::Minus => "-",
            Token::Mul => "*",
            Token::Div => "/",
            Token::Mod => "%",
            Token::Comma => ",",
            Token::Exclamation => "!",
            Token::Greater => ">",
            Token::Less => "<",
            Token::GreaterEqual => ">=",
            Token::LessEqual => "<=",
            Token::Amp => "&",
            Token::DoubleAmp => "&&",
            Token::Pipe => "|",
            Token::DoublePipe => "||",
            Token::PipeLeft => "<|",
            Token::PipeRight => "|>",
            Token::ShiftLeft => "<<",
            Token::ShiftRight => ">>",
            Token::CompositionRight => ".>",
            Token::CompositionLeft => "<.",
            Token::DoubleEqual => "==",
            Token::NotEqual => "!=",
            _ => panic!(),
        }
    }
    pub fn unop_to_str(&self) -> &'static str {
        match self {
            Token::Minus => "-_",
            Token::Exclamation => "!_",
            _ => panic!(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    pub fn op_test() {
        let source = r"
        x = 23 + 3 | 4;
        y = 5 + 34 > 6 |> f .> g |> h;
        ";
        for token in Token::lexer(source) {
            println!("{token:?}");
        }
    }
}
