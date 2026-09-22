use std::{
    env, fs,
    path::{Path, PathBuf},
    process::{Command, ExitCode},
};

fn main() -> ExitCode {
    let arguments: Vec<String> = env::args().skip(1).collect();
    if matches!(arguments.first().map(String::as_str), Some("-h" | "--help")) {
        println!("usage: lim INPUT [-o OUTPUT] [--cfg KEY=VALUE]...\n       lim --emit-asm INPUT OUTPUT [--cfg KEY=VALUE]...\n       lim --collect-cfgs INPUT\n\nCompiles Lim source to a native binary by default.");
        return ExitCode::SUCCESS;
    }
    if arguments.first().map(String::as_str) == Some("--collect-cfgs") {
        if arguments.len() != 2 {
            eprintln!("usage: lim --collect-cfgs INPUT");
            return ExitCode::FAILURE;
        }
        return match lim::collect_cfg_keys_from_path(Path::new(&arguments[1])) {
            Ok(keys) => {
                for key in keys {
                    println!("{key}");
                }
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("lim: {error}");
                ExitCode::FAILURE
            }
        };
    }
    if arguments.first().map(String::as_str) == Some("--emit-asm") {
        let (Some(input_path), Some(output_path)) = (arguments.get(1), arguments.get(2)) else {
            eprintln!("usage: lim --emit-asm INPUT OUTPUT");
            return ExitCode::FAILURE;
        };
        let mut config = lim::CompileConfig::default();
        let mut index = 3;
        while index < arguments.len() {
            if arguments[index] != "--cfg" {
                eprintln!("lim: expected --cfg KEY=VALUE after assembly output path");
                return ExitCode::FAILURE;
            }
            index += 1;
            let Some(value) = arguments.get(index) else {
                eprintln!("lim: --cfg requires KEY=VALUE");
                return ExitCode::FAILURE;
            };
            if let Err(error) = apply_cfg_argument(&mut config, value) {
                eprintln!("lim: {error}");
                return ExitCode::FAILURE;
            }
            index += 1;
        }
        return compile(input_path, Path::new(output_path), true, &config);
    }

    let (input_path, output_path, config) = match binary_arguments(&arguments) {
        Ok(arguments) => arguments,
        Err(error) => {
            eprintln!("lim: {error}");
            eprintln!("usage: lim INPUT [-o OUTPUT]  (default output: INPUT without extension)");
            eprintln!("       lim INPUT --cfg KEY=VALUE ...");
            eprintln!("       lim --emit-asm INPUT OUTPUT [--cfg KEY=VALUE ...]");
            eprintln!("       lim --collect-cfgs INPUT");
            return ExitCode::FAILURE;
        }
    };
    compile(&input_path, &output_path, false, &config)
}

fn apply_cfg_argument(config: &mut lim::CompileConfig, value: &str) -> Result<(), String> {
    let (key, value) = value
        .split_once('=')
        .ok_or_else(|| "cfg values must have the form KEY=VALUE".to_owned())?;
    if key.is_empty() || value.is_empty() {
        return Err("cfg keys and values must not be empty".into());
    }
    config.set(key, value);
    Ok(())
}

fn binary_arguments(arguments: &[String]) -> Result<(String, PathBuf, lim::CompileConfig), String> {
    let mut input = None;
    let mut output = None;
    let mut config = lim::CompileConfig::default();
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
            "--cfg" => {
                index += 1;
                let value = arguments
                    .get(index)
                    .ok_or_else(|| "--cfg requires KEY=VALUE".to_owned())?;
                apply_cfg_argument(&mut config, value)?;
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
    Ok((input, output, config))
}

fn compile(
    input_path: &str,
    output_path: &Path,
    emit_assembly: bool,
    config: &lim::CompileConfig,
) -> ExitCode {
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
    let generator_cache_directory = generated_directory.join("cache");
    if let Err(error) = lim::write_generated_sources_from_path_with_config_and_cache(
        &input,
        input_file,
        &generated_directory,
        config,
        &generator_cache_directory,
    ) {
        eprintln!("lim: {error}");
        return ExitCode::FAILURE;
    }
    let program = match lim::parse_program_from_path_with_config_and_cache(
        &input,
        input_file,
        config,
        &generator_cache_directory,
    ) {
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
