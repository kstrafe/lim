use std::{
    env, fs,
    io::{self, Read},
    process::ExitCode,
};

fn main() -> ExitCode {
    let mut input = String::new();
    if let Some(path) = env::args().nth(1) {
        input = match fs::read_to_string(&path) {
            Ok(source) => source,
            Err(error) => {
                eprintln!("lim: {path}: {error}");
                return ExitCode::FAILURE;
            }
        };
    } else if let Err(error) = io::stdin().read_to_string(&mut input) {
        eprintln!("lim: stdin: {error}");
        return ExitCode::FAILURE;
    }

    match lim::parse(&input) {
        Ok(expressions) => {
            for expression in expressions {
                println!("{expression:?}");
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("lim: {error}");
            ExitCode::FAILURE
        }
    }
}
