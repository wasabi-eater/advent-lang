use std::{fs::File, io::Read};

use advent_lang::{
    analysis::inference::InferencePool, lexer, parser, runner::core::Runner, std_lib::StdLibDefiner,
};
use chumsky::Parser;

#[derive(clap::Parser)]
struct Arg {
    file_name: String,
}

fn main() {
    let args = <Arg as clap::Parser>::parse();
    let mut buffer = String::new();
    File::open(&args.file_name)
        .expect("File open failed!")
        .read_to_string(&mut buffer)
        .expect("File read failed!");
    let tokens = lexer::tokenize(&buffer).expect("Tokenize failed!");
    buffer.clear();
    println!("tokens: {tokens:?}");
    let result = parser::program().parse(&tokens).into_result();
    let ast = match result {
        Ok(expr) => expr,
        Err(e) => {
            eprintln!("error: {e:?}");
            return;
        }
    };
    println!("{ast:?}");
    let mut inference_pool = InferencePool::new();
    let std_lib = StdLibDefiner::new(&mut inference_pool).build();
    let infered = match inference_pool.infer(ast.clone()) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("inference error: {e:?}");
            return;
        }
    };
    println!("infered: {}", inference_pool.display(infered));
    let program_data = match inference_pool.create_program_data(ast.clone()) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("program data creation error: {e:?}");
            return;
        }
    };
    println!("run!");
    let mut runner = Runner::new(program_data, std_lib);
    match runner.eval(ast) {
        Ok(_) => {}
        Err(e) => {
            eprintln!("runtime error: {e:?}");
        }
    }
}
#[test]
fn test() {
    use indoc::indoc;
    let src = indoc! {r#"
    def print: forall a. Show a => (a) -> () = show .> putStrLn;
    
    let (x, y) = (4, 5);
    print (x + y);
    let _ = 34;
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
