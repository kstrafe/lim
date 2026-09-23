use std::{
    env, fs,
    path::{Path, PathBuf},
    process::{Command, ExitCode},
};

fn main() -> ExitCode {
    let arguments: Vec<String> = env::args().skip(1).collect();
    if matches!(arguments.first().map(String::as_str), Some("-h" | "--help")) {
        println!("usage: lim INPUT [-o OUTPUT] [--target TARGET] [--cfg KEY=VALUE]...\n       lim --emit-asm INPUT OUTPUT [--target TARGET] [--cfg KEY=VALUE]...\n       lim --format INPUT [OUTPUT]\n       lim --collect-cfgs INPUT\n       lim --check-examples [DIRECTORY]\n\nCompiles Lim source to a native binary by default.");
        return ExitCode::SUCCESS;
    }
    if arguments.first().map(String::as_str) == Some("--format") {
        let Some(input) = arguments.get(1) else {
            eprintln!("usage: lim --format INPUT [OUTPUT]");
            return ExitCode::FAILURE;
        };
        if arguments.len() > 3 {
            eprintln!("usage: lim --format INPUT [OUTPUT]");
            return ExitCode::FAILURE;
        }
        let source = match fs::read_to_string(input) {
            Ok(source) => source,
            Err(error) => {
                eprintln!("lim: {input}: {error}");
                return ExitCode::FAILURE;
            }
        };
        let formatted = match lim::format_source(&source) {
            Ok(formatted) => formatted,
            Err(error) => {
                eprintln!("lim: {error}");
                return ExitCode::FAILURE;
            }
        };
        return match arguments.get(2) {
            Some(output) => match fs::write(output, formatted) {
                Ok(()) => ExitCode::SUCCESS,
                Err(error) => {
                    eprintln!("lim: {output}: {error}");
                    ExitCode::FAILURE
                }
            },
            None => {
                print!("{formatted}");
                ExitCode::SUCCESS
            }
        };
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
        let mut target = match lim::TargetDescription::host() {
            Ok(target) => target,
            Err(error) => {
                eprintln!("lim: {error}");
                return ExitCode::FAILURE;
            }
        };
        let mut index = 3;
        while index < arguments.len() {
            match arguments[index].as_str() {
                "--target" => {
                    index += 1;
                    let Some(value) = arguments.get(index) else {
                        eprintln!("lim: --target requires a target name");
                        return ExitCode::FAILURE;
                    };
                    target = match lim::TargetDescription::parse(value) {
                        Ok(target) => target,
                        Err(error) => {
                            eprintln!("lim: {error}");
                            return ExitCode::FAILURE;
                        }
                    };
                    index += 1;
                }
                "--cfg" => {
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
                "--module-path" => {
                    index += 1;
                    let Some(value) = arguments.get(index) else {
                        eprintln!("lim: --module-path requires a directory");
                        return ExitCode::FAILURE;
                    };
                    config.add_module_path(value);
                    index += 1;
                }
                _ => {
                    eprintln!("lim: expected --target, --cfg, or --module-path after assembly output path");
                    return ExitCode::FAILURE;
                }
            }
        }
        return compile(input_path, Path::new(output_path), true, &config, target);
    }
    if arguments.first().map(String::as_str) == Some("--check-examples") {
        if arguments.len() > 2 {
            eprintln!("usage: lim --check-examples [DIRECTORY]");
            return ExitCode::FAILURE;
        }
        let directory = arguments
            .get(1)
            .map_or_else(|| PathBuf::from("examples"), PathBuf::from);
        return check_examples(&directory);
    }

    let (input_path, output_path, config, target) = match binary_arguments(&arguments) {
        Ok(arguments) => arguments,
        Err(error) => {
            eprintln!("lim: {error}");
            eprintln!("usage: lim INPUT [-o OUTPUT] [--target TARGET]  (default output: INPUT without extension)");
            eprintln!("       lim INPUT --cfg KEY=VALUE ...");
            eprintln!("       lim --emit-asm INPUT OUTPUT [--cfg KEY=VALUE ...]");
            eprintln!("       lim --collect-cfgs INPUT");
            eprintln!("       lim --check-examples [DIRECTORY]");
            return ExitCode::FAILURE;
        }
    };
    compile(&input_path, &output_path, false, &config, target)
}

fn check_examples(directory: &Path) -> ExitCode {
    let mut paths = Vec::new();
    if let Err(error) = collect_lim_files(directory, &mut paths) {
        eprintln!("lim: {}: {error}", directory.display());
        return ExitCode::FAILURE;
    }
    paths.sort();
    if paths.is_empty() {
        eprintln!("lim: no .lim examples found under {}", directory.display());
        return ExitCode::FAILURE;
    }

    let mut failures = 0;
    for path in &paths {
        match check_example(path) {
            Ok(()) => println!("ok   {}", path.display()),
            Err(error) => {
                println!("FAIL {}", path.display());
                eprintln!("  {error}");
                failures += 1;
            }
        }
    }
    println!(
        "checked {} example{}: {} passed, {} failed",
        paths.len(),
        if paths.len() == 1 { "" } else { "s" },
        paths.len() - failures,
        failures
    );
    if failures == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn collect_lim_files(directory: &Path, paths: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in fs::read_dir(directory)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_lim_files(&path, paths)?;
        } else if path.extension().is_some_and(|extension| extension == "lim") {
            paths.push(path);
        }
    }
    Ok(())
}

fn check_example(path: &Path) -> Result<(), String> {
    let input = fs::read_to_string(path).map_err(|error| error.to_string())?;
    let config = lim::CompileConfig::default();
    let generated_directory = path.parent().unwrap_or_else(|| Path::new(".")).join(".lim");
    let cache_directory = generated_directory.join("cache");
    lim::write_generated_sources_from_path_with_config_and_cache(
        &input,
        path,
        &generated_directory,
        &config,
        &cache_directory,
    )?;
    let program = lim::parse_program_from_path_with_config_and_cache(
        &input,
        path,
        &config,
        &cache_directory,
    )?;
    lim::generate_assembly(&program).map(|_| ())
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

fn binary_arguments(
    arguments: &[String],
) -> Result<(String, PathBuf, lim::CompileConfig, lim::TargetDescription), String> {
    let mut input = None;
    let mut output = None;
    let mut config = lim::CompileConfig::default();
    let mut target = lim::TargetDescription::host()?;
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
            "--module-path" => {
                index += 1;
                let value = arguments
                    .get(index)
                    .ok_or_else(|| "--module-path requires a directory".to_owned())?;
                config.add_module_path(value);
            }
            "--target" => {
                index += 1;
                let value = arguments
                    .get(index)
                    .ok_or_else(|| "--target requires a target name".to_owned())?;
                target = lim::TargetDescription::parse(value)?;
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
    let manifest = Path::new(&input)
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join("lim.project");
    if manifest.is_file() {
        let metadata = lim::read_project(&manifest)?;
        for path in metadata.module_paths {
            config.add_module_path(path);
        }
    }
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
    Ok((input, output, config, target))
}

fn compile(
    input_path: &str,
    output_path: &Path,
    emit_assembly: bool,
    config: &lim::CompileConfig,
    target: lim::TargetDescription,
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
        report_source_error(&input, input_path, &error);
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
            report_source_error(&input, input_path, &error);
            return ExitCode::FAILURE;
        }
    };
    let assembly = match lim::generate_assembly_for_target(&program, target) {
        Ok(assembly) => assembly,
        Err(error) => {
            report_source_error(&input, input_path, &error);
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
    let object_path = env::temp_dir().join(format!("lim-{}-output.o", std::process::id()));
    let native_start = "\n.section .text\n.globl _start\n.type _start, @function\n_start:\n    xor ebp, ebp\n    and rsp, -16\n    call main\n    mov edi, eax\n    mov eax, 60\n    syscall\n    ud2\n.size _start, .-_start\n";
    if let Err(error) = fs::write(&assembly_path, format!("{assembly}{native_start}")) {
        eprintln!("lim: {}: {error}", assembly_path.display());
        return ExitCode::FAILURE;
    }
    let assemble = Command::new("as")
        .arg("--64")
        .arg(&assembly_path)
        .arg("-o")
        .arg(&object_path)
        .status();
    if !assemble.as_ref().is_ok_and(|status| status.success()) {
        let _ = fs::remove_file(&assembly_path);
        let _ = fs::remove_file(&object_path);
        return match assemble {
            Ok(status) => {
                eprintln!("lim: assembler failed with status {status}");
                ExitCode::FAILURE
            }
            Err(error) => {
                eprintln!("lim: could not run assembler: {error}");
                ExitCode::FAILURE
            }
        };
    }
    let dynamic_linker = native_dynamic_linker();
    let result = Command::new("ld")
        .arg("-o")
        .arg(output_path)
        .arg("-e")
        .arg("_start")
        .arg("--dynamic-linker")
        .arg(dynamic_linker)
        .arg(&object_path)
        .arg("-lc")
        .arg("-lpthread")
        .status();
    let _ = fs::remove_file(&assembly_path);
    let _ = fs::remove_file(&object_path);
    match result {
        Ok(status) if status.success() => ExitCode::SUCCESS,
        Ok(status) => {
            eprintln!("lim: linker failed with status {status}");
            ExitCode::FAILURE
        }
        Err(error) => {
            eprintln!("lim: could not run linker: {error}");
            ExitCode::FAILURE
        }
    }
}

fn report_source_error(source: &str, filename: &str, error: &str) {
    eprintln!("{}", lim::render_error(source, filename, error));
}

fn native_dynamic_linker() -> String {
    Command::new("cc")
        .arg("-print-file-name=ld-linux-x86-64.so.2")
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_owned())
        .filter(|path| !path.is_empty() && Path::new(path).is_absolute())
        .unwrap_or_else(|| "/lib64/ld-linux-x86-64.so.2".to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compiles_and_runs_binary_pipeline() {
        let directory = env::temp_dir().join(format!("lim-binary-pipeline-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("program.lim");
        let output = directory.join("program");
        fs::write(&input, "(#fn main () u64 (#return 42))").unwrap();

        let config = lim::CompileConfig::default();
        assert_eq!(
            compile(
                input.to_str().unwrap(),
                &output,
                false,
                &config,
                lim::TargetDescription::X86_64_SYSTEM_V,
            ),
            ExitCode::SUCCESS
        );
        let status = Command::new(&output).status().unwrap();
        assert_eq!(status.code(), Some(42));
        fs::remove_dir_all(directory).unwrap();
    }
}
