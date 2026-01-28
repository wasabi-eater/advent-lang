use std::{fs::File, io::Read};

use advent_lang::pipeline::Pipeline;
use std::thread;

#[derive(clap::Parser)]
struct Arg {
    file_name: String,
}

fn main() {
    env_logger::init();

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
    match Pipeline::compile_and_run(src) {
        Ok(_) => {}
        Err(e) => {
            log::error!("{e}");
        }
    }
}
