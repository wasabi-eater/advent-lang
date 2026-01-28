use advent_lang::pipeline::Pipeline;
use indoc::indoc;

fn run_test(src: &str) -> Result<(), String> {
    Pipeline::compile_and_run(src)
        .map(|_| ())
        .map_err(|e| format!("{e}"))
}

#[test]
fn test_print_twice() {
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

    assert!(run_test(src).is_ok(), "test_print_twice failed");
}

#[test]
fn test_type_inference() {
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

    foldl {_ + _} 0 [1, 2, 3, 4, 5] |> print;
    foldr {_ + _} 0 [1, 2, 3, 4, 5] |> print;
    "#};

    assert!(run_test(src).is_ok(), "test_type_inference failed");
}
