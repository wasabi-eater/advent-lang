use advent_lang::{
    analysis::inference::InferencePool, lexer, parser, runner::core::Runner, std_lib::StdLibDefiner,
};
use chumsky::Parser;
use indoc::indoc;

fn main() {
    let src = indoc! {r#"
    3 != 3 |> show |> print;
    "#};
    let tokens = lexer::tokenize(src).expect("Tokenize failed!");
    println!("tokens: {tokens:?}");
    let result = parser::program().parse(&tokens).into_result();
    let ast = match result {
        Ok(expr) => expr,
        Err(e) => panic!("error: {e:?}"),
    };
    println!("{ast:?}");
    let mut inference_pool = InferencePool::new();
    let std_lib = StdLibDefiner::new(&mut inference_pool).build();
    let infered = inference_pool.infer(ast.clone()).unwrap();
    println!("infered: {}", inference_pool.display(infered));
    let program_data = inference_pool.create_program_data(ast.clone()).unwrap();
    println!("run!");
    let mut runner = Runner::new(program_data, std_lib);
    println!("{:?}", runner.eval(ast).unwrap());
}
