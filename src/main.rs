use std::{
    env, fs,
    io::{self, Read},
    path::Path,
    process::ExitCode,
};

fn main() -> ExitCode {
    let arguments: Vec<String> = env::args().collect();
    if arguments.get(1).map(String::as_str) == Some("--emit-asm") {
        let (Some(input_path), Some(output_path)) = (arguments.get(2), arguments.get(3)) else {
            eprintln!("usage: lim --emit-asm INPUT OUTPUT");
            return ExitCode::FAILURE;
        };
        let input = match fs::read_to_string(input_path) {
            Ok(source) => source,
            Err(error) => {
                eprintln!("lim: {input_path}: {error}");
                return ExitCode::FAILURE;
            }
        };
        let generated_directory = Path::new(input_path)
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .join(".lim");
        if let Err(error) = lim::write_generated_sources(&input, &generated_directory) {
            eprintln!("lim: {error}");
            return ExitCode::FAILURE;
        }
        let program = match lim::parse_program(&input) {
            Ok(program) => program,
            Err(error) => {
                eprintln!("lim: {error}");
                return ExitCode::FAILURE;
            }
        };
        let assembly = match lim::generate_assembly(&program) {
            Ok(assembly) => assembly,
            Err(error) => {
                eprintln!("lim: {error}");
                return ExitCode::FAILURE;
            }
        };
        if let Err(error) = fs::write(output_path, assembly) {
            eprintln!("lim: {output_path}: {error}");
            return ExitCode::FAILURE;
        }
        return ExitCode::SUCCESS;
    }

    let mut input = String::new();
    if let Some(path) = arguments.get(1) {
        input = match fs::read_to_string(path) {
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

    match lim::parse_program(&input) {
        Ok(program) => {
            println!("{program:#?}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("lim: {error}");
            ExitCode::FAILURE
        }
    }
}
