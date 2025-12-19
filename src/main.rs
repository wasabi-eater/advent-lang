use std::{fs::File, io::Read};

use advent_lang::{
    analysis::inference::InferencePool, lexer, parser, runner::core::Runner, std_lib::StdLibDefiner,
};
use chumsky::Parser;
use std::thread;

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
    let builder = thread::Builder::new().stack_size(1024 * 1024 * 16);
    let handler = builder
        .spawn(move || {
            build_and_run(&buffer);
        })
        .expect("Thread spawn failed!");
    handler.join().expect("Thread join failed!");
}

fn build_and_run(src: &str) {
    let tokens = lexer::tokenize(src).expect("Tokenize failed!");
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
    def printTwice: forall a. Show a => a -> () = {\x ->
        print x;
        print x;
    }; -- hoge hoge

    printTwice 34;
    printTwice 3.4;
    printTwice "Hoge";
    printTwice [[0, 1, 2], [3, 4, 5]];
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
#[test]
fn test2() {
    use indoc::indoc;
    let src = indoc! {r#"
    34: Int;
    3.4: Float;
    "Hoge": String;
    [0, 1, 2]: [Int];
    [[0, 1, 2], [3, 4, 5]]: [[Int]];
    23 + 34: Int;
    3.4 + 5.6: Float;
    "Hello, " + "world!": String;
    {\x -> x}: Int -> Int;
    def id: forall a. a -> a = {\x -> x}: a -> a;
    id: Int -> Int;
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
