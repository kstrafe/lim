use std::{
    env, fs,
    path::{Path, PathBuf},
    process::{Command, ExitCode},
};

fn main() -> ExitCode {
    let arguments: Vec<String> = env::args().skip(1).collect();
    if matches!(arguments.first().map(String::as_str), Some("-h" | "--help")) {
        println!("usage: lim INPUT [-o OUTPUT]\n       lim --emit-asm INPUT OUTPUT\n\nCompiles Lim source to a native binary by default.");
        return ExitCode::SUCCESS;
    }
    if arguments.first().map(String::as_str) == Some("--emit-asm") {
        let (Some(input_path), Some(output_path)) = (arguments.get(1), arguments.get(2)) else {
            eprintln!("usage: lim --emit-asm INPUT OUTPUT");
            return ExitCode::FAILURE;
        };
        if arguments.len() != 3 {
            eprintln!("usage: lim --emit-asm INPUT OUTPUT");
            return ExitCode::FAILURE;
        }
        return compile(input_path, Path::new(output_path), true);
    }

    let (input_path, output_path) = match binary_arguments(&arguments) {
        Ok(arguments) => arguments,
        Err(error) => {
            eprintln!("lim: {error}");
            eprintln!("usage: lim INPUT [-o OUTPUT]  (default output: INPUT without extension)");
            eprintln!("       lim --emit-asm INPUT OUTPUT");
            return ExitCode::FAILURE;
        }
    };
    compile(&input_path, &output_path, false)
}

fn binary_arguments(arguments: &[String]) -> Result<(String, PathBuf), String> {
    let mut input = None;
    let mut output = None;
    let mut index = 0;
    while index < arguments.len() {
        match arguments[index].as_str() {
            "-o" | "--output" => {
                index += 1;
                let path = arguments
                    .get(index)
                    .ok_or_else(|| "-o requires an output path".to_owned())?;
                output = Some(PathBuf::from(path));
            }
            "-h" | "--help" => return Err("help must be requested as the first argument".into()),
            value if value.starts_with('-') => {
                return Err(format!("unknown option '{value}'"));
            }
            value => {
                if input.replace(value.to_owned()).is_some() {
                    return Err("expected one input file".into());
                }
            }
        }
        index += 1;
    }

    let input = input.ok_or_else(|| "an input file is required".to_owned())?;
    let output = output.unwrap_or_else(|| {
        let path = Path::new(&input);
        let stem = path.file_stem().unwrap_or_default();
        let mut result = path
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .to_path_buf();
        result.push(stem);
        result
    });
    Ok((input, output))
}

fn compile(input_path: &str, output_path: &Path, emit_assembly: bool) -> ExitCode {
    let input = match fs::read_to_string(input_path) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("lim: {input_path}: {error}");
            return ExitCode::FAILURE;
        }
    };
    let input_file = Path::new(input_path);
    let generated_directory = input_file
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join(".lim");
    if let Err(error) =
        lim::write_generated_sources_from_path(&input, input_file, &generated_directory)
    {
        eprintln!("lim: {error}");
        return ExitCode::FAILURE;
    }
    let program = match lim::parse_program_from_path(&input, input_file) {
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

    if emit_assembly {
        return match fs::write(output_path, assembly) {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("lim: {}: {error}", output_path.display());
                ExitCode::FAILURE
            }
        };
    }

    let assembly_path = env::temp_dir().join(format!("lim-{}-output.s", std::process::id()));
    if let Err(error) = fs::write(&assembly_path, assembly) {
        eprintln!("lim: {}: {error}", assembly_path.display());
        return ExitCode::FAILURE;
    }
    let result = Command::new("clang")
        .arg("-Qunused-arguments")
        .arg(&assembly_path)
        .arg("-o")
        .arg(output_path)
        .status();
    let _ = fs::remove_file(&assembly_path);
    match result {
        Ok(status) if status.success() => ExitCode::SUCCESS,
        Ok(status) => {
            eprintln!("lim: clang failed with status {status}");
            ExitCode::FAILURE
        }
        Err(error) => {
            eprintln!("lim: could not run clang: {error}");
            ExitCode::FAILURE
        }
    }
}
