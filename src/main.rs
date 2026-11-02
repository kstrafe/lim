mod cli_proof_budget;

use std::{
    env, fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

static JSON_DIAGNOSTICS: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

fn emit_diagnostic(diagnostic: &lim::Diagnostic, source: &str, filename: &str) {
    if JSON_DIAGNOSTICS.load(std::sync::atomic::Ordering::Relaxed) {
        std::eprintln!("{}", lim::render_diagnostic_json(diagnostic, filename));
    } else {
        std::eprintln!("{}", lim::render_diagnostic(diagnostic, source, filename));
    }
}

// Non-source CLI failures must use the same stream format as source failures.
macro_rules! eprintln {
    ($($argument:tt)*) => {{
        if JSON_DIAGNOSTICS.load(std::sync::atomic::Ordering::Relaxed) {
            emit_diagnostic(&lim::Diagnostic::new(lim::DiagnosticCode::Cli, format!($($argument)*)), "", "");
        } else { std::eprintln!($($argument)*); }
    }};
}

fn main() -> ExitCode {
    // Artifact lookup is an introspection command, not an unused-code check.
    // The LSP owns its warning sessions so stdout remains protocol-only.
    let command = env::args()
        .skip(1)
        .find(|arg| !arg.starts_with("--diagnostic-format=") && arg != "--timings");
    if matches!(command.as_deref(), Some("lsp" | "--lsp"))
        || env::args().skip(1).any(|arg| arg == "--locate-generated")
    {
        return run_command();
    }
    let (status, warnings) = lim::with_warnings(run_command);
    if status == ExitCode::SUCCESS {
        for warning in warnings {
            emit_diagnostic(&warning, "", "");
        }
    }
    status
}

fn run_command() -> ExitCode {
    let mut arguments: Vec<String> = env::args().skip(1).collect();
    let timings = arguments.iter().any(|arg| arg == "--timings");
    arguments.retain(|arg| arg != "--timings");
    let json = arguments
        .iter()
        .any(|arg| arg == "--diagnostic-format=json");
    JSON_DIAGNOSTICS.store(json, std::sync::atomic::Ordering::Relaxed);
    if timings {
        let command = arguments
            .iter()
            .find(|arg| !arg.starts_with("--diagnostic-format="))
            .map(String::as_str);
        let supported = matches!(
            command,
            Some("--check" | "--check-theorem" | "--check-lean-export" | "--emit-asm")
        ) || command
            .is_some_and(|command| !command.starts_with('-') && !matches!(command, "fmt" | "lsp"));
        if !supported {
            eprintln!("lim: --timings is supported for compile, --check, --check-theorem, --check-lean-export, and --emit-asm commands");
            return ExitCode::FAILURE;
        }
    }
    if timings {
        let session = lim::TimingSession::start();
        let status = run_main(arguments);
        std::eprintln!(
            "{}",
            lim::render_timings(&session.finish(), arguments_json_mode())
        );
        return status;
    }
    run_main(arguments)
}

fn arguments_json_mode() -> bool {
    JSON_DIAGNOSTICS.load(std::sync::atomic::Ordering::Relaxed)
}

fn output_identity(path: &Path) -> PathBuf {
    if let Ok(path) = path.canonicalize() {
        return path;
    }
    if let (Some(parent), Some(name)) = (path.parent(), path.file_name()) {
        if let Ok(parent) = parent.canonicalize() {
            return parent.join(name);
        }
    }
    let absolute = env::current_dir().unwrap_or_default().join(path);
    let mut normalized = PathBuf::new();
    for part in absolute.components() {
        match part {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                normalized.pop();
            }
            other => normalized.push(other.as_os_str()),
        }
    }
    normalized
}

fn run_main(mut arguments: Vec<String>) -> ExitCode {
    let mut destination = None;
    let mut index = 0;
    while index < arguments.len() {
        if arguments[index] == "--write-lsp-config" {
            if destination.is_some() || index + 1 >= arguments.len() {
                eprintln!("lim: --write-lsp-config requires one output path");
                return ExitCode::FAILURE;
            }
            destination = Some(PathBuf::from(arguments.remove(index + 1)));
            arguments.remove(index);
        } else {
            index += 1;
        }
    }
    let Some(destination) = destination else {
        return run_main_inner(arguments);
    };
    let mut settings = arguments.clone();
    settings.retain(|arg| !arg.starts_with("--diagnostic-format="));
    if let Some(index) = settings.iter().position(|arg| arg == "--locate-generated") {
        settings.remove(index);
        if index >= settings.len() || settings[index].starts_with('-') {
            eprintln!("lim: --locate-generated requires a source selection");
            return ExitCode::FAILURE;
        }
        settings.remove(index);
    }
    let (mut settings, proof_budget) = match cli_proof_budget::parse(&settings) {
        Ok(parsed) => parsed,
        Err(error) => {
            eprintln!("lim: {error}");
            return ExitCode::FAILURE;
        }
    };
    match settings.first().map(String::as_str) {
        Some("--check") => {
            settings.remove(0);
        }
        Some("--emit-asm") if settings.len() >= 3 => {
            settings.remove(0);
            settings.insert(1, "-o".into());
        }
        Some(command) if !command.starts_with('-') && !matches!(command, "lsp" | "fmt") => {}
        _ => {
            eprintln!("lim: --write-lsp-config is supported for compile, --check, and --emit-asm");
            return ExitCode::FAILURE;
        }
    }
    let (entry, output, mut config, target, _) = match binary_arguments(&settings) {
        Ok(settings) => settings,
        Err(error) => {
            eprintln!("lim: {error}");
            return ExitCode::FAILURE;
        }
    };
    if output_identity(&destination) == output_identity(&output) {
        eprintln!("lim: LSP context must not replace compilation output");
        return ExitCode::FAILURE;
    }
    config.set_proof_budget(proof_budget);
    let context = lim::lsp_context::LspContext {
        entry: entry.into(),
        target,
        config,
    };
    if destination
        .extension()
        .is_none_or(|extension| extension != "lsp")
    {
        eprintln!("lim: LSP context output must have a .lsp extension");
        return ExitCode::FAILURE;
    }
    if output.exists() {
        if let Err(error) = lim::reject_source_output_collision(&output, &destination) {
            eprintln!("lim: {error}");
            return ExitCode::FAILURE;
        }
    }
    if let Err(error) = lim::reject_source_output_collision(&context.entry, &destination) {
        eprintln!("lim: {error}");
        return ExitCode::FAILURE;
    }
    let status = run_main_inner(arguments);
    if status == ExitCode::SUCCESS {
        if output.exists() {
            if let Err(error) = lim::reject_source_output_collision(&output, &destination) {
                eprintln!("lim: {error}");
                return ExitCode::FAILURE;
            }
        }
        if let Err(error) = context.record(&destination) {
            eprintln!("lim: {error}");
            return ExitCode::FAILURE;
        }
    }
    status
}

fn run_main_inner(mut arguments: Vec<String>) -> ExitCode {
    let json = arguments
        .iter()
        .any(|arg| arg == "--diagnostic-format=json");
    JSON_DIAGNOSTICS.store(json, std::sync::atomic::Ordering::Relaxed);
    arguments.retain(|arg| arg != "--diagnostic-format=json" && arg != "--diagnostic-format=human");
    if matches!(arguments.first().map(String::as_str), Some("-h" | "--help")) {
        println!("usage: lim INPUT [-o OUTPUT] [--target TARGET] [--cfg KEY=VALUE]... [--link-lib NAME]... [--link-object PATH]... [--timings]\n       lim --check INPUT [--cfg KEY=VALUE]... [--target TARGET] [PROOF-BUDGET] [--timings]\n       lim --check-theorem INPUT NAME [--cfg KEY=VALUE]... [--module-path PATH]... [--target TARGET] [PROOF-BUDGET] [--timings]\n       lim --check-lean-export INPUT TARGET [--report PATH] [--emit-proof PATH] [--lean-foundations] [PROOF-BUDGET] [--timings]\n       PROOF-BUDGET: [--proof-work N] [--proof-phase-bytes N] [--proof-total-bytes N]\n       lim --emit-asm INPUT OUTPUT [--target TARGET] [--cfg KEY=VALUE]... [--timings]\n       lim --stack-usage INPUT [--target TARGET] [--cfg KEY=VALUE]...\n       lim fmt INPUT\n       lim --format INPUT [OUTPUT]\n       lim --collect-cfgs INPUT\n       lim --check-examples [DIRECTORY]\n\nCompiles Lim source to a native binary by default.");
        println!("Language server: lim lsp [--cfg KEY=VALUE]... [--module-path PATH]...\nUse --diagnostic-format=json for structured diagnostics on stderr.");
        println!("Add --write-lsp-config PATH to compile, --check, or --emit-asm to record the effective entry and compilation settings for the language server. Distinct entries or settings accumulate in the same file; identical contexts are not rewritten.");
        println!("Locate generated sources: lim INPUT --locate-generated FILE:LINE[:COLUMN]\n                         lim INPUT --locate-generated FILE:STARTLINE:STARTCOL-ENDLINE:ENDCOL\n                         lim INPUT --locate-generated FILE:STARTLINE-ENDLINE\nColumns are one-based Unicode scalar positions; explicit range ends are exclusive. Prints direct/nested labels, generator names, and artifact paths without producing a binary.");
        return ExitCode::SUCCESS;
    }
    if arguments
        .iter()
        .any(|argument| argument == "--locate-generated")
    {
        return locate_generated_command(arguments);
    }
    if matches!(
        arguments.first().map(String::as_str),
        Some("--stack-usage" | "--explain-cache")
    ) {
        return stack_usage_command(&arguments);
    }
    if matches!(
        arguments.first().map(String::as_str),
        Some("--check" | "--check-theorem")
    ) {
        return check_command(&arguments);
    }
    if arguments.first().map(String::as_str) == Some("--check-lean-export") {
        return check_lean_export_command(&arguments);
    }
    if arguments.first().map(String::as_str) == Some("fmt") {
        if arguments.len() != 2 {
            eprintln!("usage: lim fmt INPUT");
            return ExitCode::FAILURE;
        }
        return match lim::format_project_from_path(Path::new(&arguments[1])) {
            Ok(paths) => {
                for path in paths {
                    println!("formatted {}", path.display());
                }
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("lim: {error}");
                ExitCode::FAILURE
            }
        };
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
            Some(output) => {
                match lim::reject_source_output_collision(Path::new(input), Path::new(output))
                    .and_then(|()| lim::write_output_atomic(Path::new(output), formatted))
                {
                    Ok(()) => ExitCode::SUCCESS,
                    Err(error) => {
                        eprintln!("lim: {output}: {error}");
                        ExitCode::FAILURE
                    }
                }
            }
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
    if matches!(arguments.first().map(String::as_str), Some("lsp" | "--lsp")) {
        let mut config = lim::CompileConfig::default();
        let mut index = 1;
        while index < arguments.len() {
            let option = &arguments[index];
            let Some(value) = arguments.get(index + 1) else {
                eprintln!("lim: {option} requires a value");
                return ExitCode::FAILURE;
            };
            match option.as_str() {
                "--cfg" => {
                    if let Err(error) = apply_cfg_argument(&mut config, value) {
                        eprintln!("lim: {error}");
                        return ExitCode::FAILURE;
                    }
                }
                "--module-path" => config.add_module_path(value),
                _ => {
                    eprintln!("usage: lim lsp [--cfg KEY=VALUE]... [--module-path PATH]...");
                    return ExitCode::FAILURE;
                }
            }
            index += 2;
        }
        return match lim::lsp::run(&config) {
            Ok(0) => ExitCode::SUCCESS,
            Ok(_) => ExitCode::FAILURE,
            Err(error) => {
                eprintln!("lim: language server: {error}");
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
        let mut target_explicit = false;
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
                    target_explicit = true;
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
        let metadata = match project_for_input(input_path) {
            Ok(metadata) => metadata,
            Err(error) => {
                eprintln!("lim: {error}");
                return ExitCode::FAILURE;
            }
        };
        if let Some(metadata) = metadata {
            config.add_module_path(&metadata.source_root);
            for path in metadata.module_paths {
                config.add_module_path(path);
            }
            if !target_explicit {
                if let Some(project_target) = metadata.target {
                    target = project_target;
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

    let (input_path, output_path, config, target, links) = match binary_arguments(&arguments) {
        Ok(arguments) => arguments,
        Err(error) => {
            eprintln!("lim: {error}");
            eprintln!("usage: lim INPUT [-o OUTPUT] [--target TARGET]  (default output: INPUT without extension)");
            eprintln!("       lim INPUT --cfg KEY=VALUE ...");
            eprintln!("       lim --emit-asm INPUT OUTPUT [--cfg KEY=VALUE ...]");
            eprintln!("       lim fmt INPUT");
            eprintln!("       lim --collect-cfgs INPUT");
            eprintln!("       lim --check-examples [DIRECTORY]");
            return ExitCode::FAILURE;
        }
    };
    compile_with_links(&input_path, &output_path, false, &config, target, &links)
}

fn check_lean_export_command(arguments: &[String]) -> ExitCode {
    let usage = "usage: lim --check-lean-export INPUT TARGET [--report PATH] [--emit-proof PATH] [--lean-foundations] [--proof-work N] [--proof-phase-bytes N] [--proof-total-bytes N]";
    let (arguments, budget) = match cli_proof_budget::parse(arguments) {
        Ok(parsed) => parsed,
        Err(error) => {
            eprintln!("lim: {error}");
            eprintln!("{usage}");
            return ExitCode::FAILURE;
        }
    };
    let arguments = arguments.as_slice();
    if arguments.len() < 3 {
        eprintln!("{usage}");
        return ExitCode::FAILURE;
    }
    if arguments[1].is_empty() || arguments[1].starts_with('-') {
        eprintln!("lim: INPUT must be a nonempty path, not an option");
        return ExitCode::FAILURE;
    }
    let input = Path::new(&arguments[1]);
    let target = &arguments[2];
    if target.is_empty() || target.starts_with('-') {
        eprintln!("lim: TARGET must be a nonempty theorem name");
        return ExitCode::FAILURE;
    }

    let mut report_path: Option<&Path> = None;
    let mut proof_path: Option<&Path> = None;
    let mut lean_foundations = false;
    let mut index = 3;
    while index < arguments.len() {
        let option = arguments[index].as_str();
        if option == "--lean-foundations" {
            if lean_foundations {
                eprintln!("lim: duplicate --lean-foundations option");
                eprintln!("{usage}");
                return ExitCode::FAILURE;
            }
            lean_foundations = true;
            index += 1;
            continue;
        }
        let slot = match option {
            "--report" if report_path.is_none() => &mut report_path,
            "--emit-proof" if proof_path.is_none() => &mut proof_path,
            "--report" | "--emit-proof" => {
                eprintln!("lim: duplicate {option} option");
                eprintln!("{usage}");
                return ExitCode::FAILURE;
            }
            _ => {
                eprintln!("lim: unknown Lean export option '{option}'");
                eprintln!("{usage}");
                return ExitCode::FAILURE;
            }
        };
        let Some(value) = arguments.get(index + 1) else {
            eprintln!("lim: {option} requires a nonempty path");
            return ExitCode::FAILURE;
        };
        if value.is_empty() || value.starts_with('-') {
            eprintln!("lim: {option} requires a nonempty path, not an option");
            return ExitCode::FAILURE;
        }
        *slot = Some(Path::new(value));
        index += 2;
    }

    if let (Some(proof), Some(report)) = (proof_path, report_path) {
        if same_output_path(proof, report) {
            eprintln!("lim: proof and report outputs refer to the same file");
            return ExitCode::FAILURE;
        }
        if proof.exists() {
            if let Err(error) = lim::reject_source_output_collision(proof, report) {
                eprintln!("lim: proof and report outputs refer to the same file: {error}");
                return ExitCode::FAILURE;
            }
        } else if report.exists() {
            if let Err(error) = lim::reject_source_output_collision(report, proof) {
                eprintln!("lim: proof and report outputs refer to the same file: {error}");
                return ExitCode::FAILURE;
            }
        }
    }
    for output in [report_path, proof_path].into_iter().flatten() {
        if let Err(error) = lim::reject_source_output_collision(input, output) {
            eprintln!("lim: {}: {error}", output.display());
            return ExitCode::FAILURE;
        }
    }

    let file = match fs::File::open(input) {
        Ok(file) => file,
        Err(error) => {
            eprintln!("lim: {}: {error}", input.display());
            return ExitCode::FAILURE;
        }
    };
    let (report, emitted) = if proof_path.is_some() {
        match lim::translate_lean_export_with_budget(
            std::io::BufReader::new(file),
            target,
            if lean_foundations {
                lim::LeanFoundationPolicy::Lean4
            } else {
                lim::LeanFoundationPolicy::Constructive
            },
            budget,
        ) {
            Ok(translation) => (
                translation.report,
                Some((translation.target, translation.source)),
            ),
            Err(error) => {
                eprintln!("lim: {}: {error}", input.display());
                return ExitCode::FAILURE;
            }
        }
    } else {
        match lim::check_lean_export_with_budget(
            std::io::BufReader::new(file),
            target,
            if lean_foundations {
                lim::LeanFoundationPolicy::Lean4
            } else {
                lim::LeanFoundationPolicy::Constructive
            },
            budget,
        ) {
            Ok(report) => (report, None),
            Err(error) => {
                eprintln!("lim: {}: {error}", input.display());
                return ExitCode::FAILURE;
            }
        }
    };
    if let (Some(path), Some((_, source))) = (proof_path, emitted.as_ref()) {
        if let Err(error) = lim::write_output_atomic(path, source.as_bytes()) {
            eprintln!("lim: {}: {error}", path.display());
            return ExitCode::FAILURE;
        }
    }
    if let Some(path) = report_path {
        if let Err(error) = lim::write_output_atomic(path, report.render_json()) {
            eprintln!("lim: {}: {error}", path.display());
            return ExitCode::FAILURE;
        }
    }
    println!(
        "checked Lean export theorem {} ({} declarations)",
        target,
        report.declarations.len()
    );
    if !cli_proof_budget::is_default(budget) {
        println!(
            "proof budget: work={} phase-bytes={} total-bytes={}",
            budget.work(),
            budget.phase_bytes(),
            budget.total_bytes()
        );
    }
    if !report.axioms.is_empty() {
        println!("declared Lean axioms: {}", report.axioms.join(", "));
        println!(
            "target logical foundations: {}",
            if report.target_axioms.is_empty() {
                "none".to_owned()
            } else {
                report.target_axioms.join(", ")
            }
        );
    }
    if let (Some(path), Some((target, _))) = (proof_path, emitted) {
        println!("emitted native theorem {target} to {}", path.display());
    }
    ExitCode::SUCCESS
}

fn same_output_path(left: &Path, right: &Path) -> bool {
    if output_identity(left) == output_identity(right) {
        return true;
    }
    #[cfg(unix)]
    if let (Ok(left), Ok(right)) = (fs::metadata(left), fs::metadata(right)) {
        use std::os::unix::fs::MetadataExt;
        return left.dev() == right.dev() && left.ino() == right.ino();
    }
    false
}

#[derive(Debug, PartialEq)]
enum GeneratedSelection {
    Lines(usize, usize),
    Range((usize, usize), (usize, usize)),
}

fn selection_number(value: &str) -> Result<usize, String> {
    value
        .parse::<usize>()
        .ok()
        .filter(|number| *number > 0 && value.bytes().all(|byte| byte.is_ascii_digit()))
        .ok_or_else(|| "selection lines and columns must be positive integers".to_owned())
}

fn parse_generated_selection(value: &str) -> Result<(PathBuf, GeneratedSelection), String> {
    let usage = "--locate-generated requires FILE:LINE, FILE:LINE:COLUMN, FILE:STARTLINE:STARTCOL-ENDLINE:ENDCOL, or FILE:STARTLINE-ENDLINE";
    let (prefix, last) = value.rsplit_once(':').ok_or(usage)?;
    let (path, selection) = if let Some((start, end)) = last.split_once('-') {
        (
            prefix,
            GeneratedSelection::Lines(selection_number(start)?, selection_number(end)?),
        )
    } else if let Some((path, previous)) = prefix.rsplit_once(':') {
        if let Some((start_column, end_line)) = previous
            .split_once('-')
            .filter(|(start, end)| selection_number(start).is_ok() && selection_number(end).is_ok())
        {
            let (path, start_line) = path.rsplit_once(':').ok_or(usage)?;
            (
                path,
                GeneratedSelection::Range(
                    (
                        selection_number(start_line)?,
                        selection_number(start_column)?,
                    ),
                    (selection_number(end_line)?, selection_number(last)?),
                ),
            )
        } else if previous.bytes().all(|byte| byte.is_ascii_digit()) {
            let point = (selection_number(previous)?, selection_number(last)?);
            (path, GeneratedSelection::Range(point, point))
        } else {
            let line = selection_number(last)?;
            (prefix, GeneratedSelection::Lines(line, line))
        }
    } else {
        let line = selection_number(last)?;
        (prefix, GeneratedSelection::Lines(line, line))
    };
    if path.is_empty() {
        return Err(usage.to_owned());
    }
    Ok((PathBuf::from(path), selection))
}

impl GeneratedSelection {
    fn byte_offsets(&self, source: &str) -> Result<(usize, usize), String> {
        // Keep a final empty line and exclude CRLF terminators from column counts.
        let mut offset = 0;
        let lines: Vec<_> = source
            .split('\n')
            .map(|line| {
                let start = offset;
                offset += line.len() + 1;
                (start, line.strip_suffix('\r').unwrap_or(line))
            })
            .collect();
        let line_at = |number: usize| {
            number
                .checked_sub(1)
                .and_then(|index| lines.get(index))
                .copied()
                .ok_or_else(|| format!("selection line {number} is outside the selected file"))
        };
        let position = |(line, column): (usize, usize)| -> Result<usize, String> {
            let (start, text) = line_at(line)?;
            let byte = column.checked_sub(1).and_then(|index| {
                text.char_indices()
                    .map(|(byte, _)| byte)
                    .chain(std::iter::once(text.len()))
                    .nth(index)
            });
            byte.map(|byte| start + byte).ok_or_else(|| {
                format!("selection column {column} is outside line {line} of the selected file")
            })
        };
        let (start, end) = match *self {
            Self::Lines(start, end) => {
                let (start, _) = line_at(start)?;
                let (end_start, end_text) = line_at(end)?;
                if start > end_start {
                    return Err("selection end precedes its start".into());
                }
                let end = lines
                    .get(end)
                    .map_or(end_start + end_text.len(), |(start, _)| *start);
                (start, end)
            }
            Self::Range(start, end) => (position(start)?, position(end)?),
        };
        if end < start {
            return Err("selection end precedes its start".into());
        }
        Ok((start, end))
    }
}

fn locate_generated_command(mut arguments: Vec<String>) -> ExitCode {
    let index = arguments
        .iter()
        .position(|argument| argument == "--locate-generated")
        .expect("locate command has its option");
    arguments.remove(index);
    if index >= arguments.len() || arguments[index].starts_with('-') {
        eprintln!("lim: --locate-generated requires a source selection");
        return ExitCode::FAILURE;
    }
    let selection = arguments.remove(index);
    let result = (|| {
        let (selected_path, selection) = parse_generated_selection(&selection)?;
        let (entry, _, config, _, _) = binary_arguments(&arguments)?;
        let selected_source = fs::read_to_string(&selected_path)
            .map_err(|error| format!("{}: {error}", selected_path.display()))?;
        let (start, end) = selection.byte_offsets(&selected_source)?;
        let source = fs::read_to_string(&entry).map_err(|error| format!("{entry}: {error}"))?;
        Ok::<_, String>((entry, config, selected_path, start, end, source))
    })();
    let (entry, config, selected_path, start, end, source) = match result {
        Ok(selection) => selection,
        Err(error) => {
            eprintln!("lim: {error}");
            return ExitCode::FAILURE;
        }
    };
    match lim::locate_generated_details(
        &source,
        Path::new(&entry),
        &config,
        &selected_path,
        start,
        end,
    ) {
        Ok(artifacts) => {
            for artifact in artifacts {
                let relationship = if artifact.nested { "nested" } else { "direct" };
                println!(
                    "{relationship} #generate {} -> {}",
                    artifact.generator,
                    artifact.path.display()
                );
            }
            ExitCode::SUCCESS
        }
        Err(diagnostic) => {
            emit_diagnostic(&diagnostic, &source, &entry);
            ExitCode::FAILURE
        }
    }
}

fn check_command(arguments: &[String]) -> ExitCode {
    let (arguments, budget) = match cli_proof_budget::parse(arguments) {
        Ok(parsed) => parsed,
        Err(error) => {
            eprintln!("lim: {error}");
            return ExitCode::FAILURE;
        }
    };
    let arguments = arguments.as_slice();
    let budget_usage = "[--proof-work N] [--proof-phase-bytes N] [--proof-total-bytes N]";
    let Some(input_path) = arguments.get(1) else {
        eprintln!("usage: lim --check INPUT [--cfg KEY=VALUE]... [--target TARGET] {budget_usage}");
        return ExitCode::FAILURE;
    };
    if input_path.starts_with('-') {
        eprintln!(
            "lim: an input file must immediately follow {}",
            arguments[0]
        );
        return ExitCode::FAILURE;
    }
    let theorem = if arguments[0] == "--check-theorem" {
        match arguments.get(2) {
            Some(name) if !name.is_empty() && !name.starts_with('-') => Some(name.as_str()),
            _ => {
                eprintln!("usage: lim --check-theorem INPUT NAME [--cfg KEY=VALUE]... [--module-path PATH]... [--target TARGET] {budget_usage}");
                return ExitCode::FAILURE;
            }
        }
    } else {
        None
    };
    let mut config = lim::CompileConfig::default();
    config.set_proof_budget(budget);
    let mut selected_target = None;
    let mut index = if theorem.is_some() { 3 } else { 2 };
    while index < arguments.len() {
        match arguments[index].as_str() {
            "--cfg" => {
                index += 1;
                let Some(value) = arguments.get(index).filter(|value| !value.starts_with('-'))
                else {
                    eprintln!("lim: --cfg requires KEY=VALUE");
                    return ExitCode::FAILURE;
                };
                if let Err(error) = apply_cfg_argument(&mut config, value) {
                    eprintln!("lim: {error}");
                    return ExitCode::FAILURE;
                }
            }
            "--target" => {
                index += 1;
                let Some(value) = arguments.get(index).filter(|value| !value.starts_with('-'))
                else {
                    eprintln!("lim: --target requires a target name");
                    return ExitCode::FAILURE;
                };
                selected_target = match lim::TargetDescription::parse(value) {
                    Ok(target) => Some(target),
                    Err(error) => {
                        eprintln!("lim: {error}");
                        return ExitCode::FAILURE;
                    }
                };
            }
            "--module-path" => {
                index += 1;
                let Some(value) = arguments.get(index).filter(|value| !value.starts_with('-'))
                else {
                    eprintln!("lim: --module-path requires a directory");
                    return ExitCode::FAILURE;
                };
                config.add_module_path(value);
            }
            other => {
                eprintln!("lim: unexpected {} argument '{other}'", arguments[0]);
                return ExitCode::FAILURE;
            }
        }
        index += 1;
    }

    let metadata = match project_for_input(input_path) {
        Ok(metadata) => metadata,
        Err(error) => {
            eprintln!("lim: {error}");
            return ExitCode::FAILURE;
        }
    };
    if let Some(metadata) = metadata {
        selected_target = selected_target.or(metadata.target);
        config.add_module_path(&metadata.source_root);
        for path in metadata.module_paths {
            config.add_module_path(path);
        }
    }

    if let Some(target) = selected_target {
        config = config.with_target(target);
    }

    let _input_timing = lim::timing_stage("input_read");
    let source = match fs::read_to_string(input_path) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("lim: {input_path}: {error}");
            return ExitCode::FAILURE;
        }
    };
    drop(_input_timing);
    let input_file = Path::new(input_path);
    if let Some(name) = theorem {
        return match lim::check_theorem_details_from_path_with_config(
            &source, input_file, &config, name,
        ) {
            Ok(checked) => {
                println!("checked theorem {name}");
                if !cli_proof_budget::is_default(budget) {
                    println!(
                        "proof budget: work={} phase-bytes={} total-bytes={}",
                        budget.work(),
                        budget.phase_bytes(),
                        budget.total_bytes()
                    );
                }
                if !checked.foundations.is_empty() {
                    println!("logical foundations: {}", checked.foundations.join(", "));
                }
                ExitCode::SUCCESS
            }
            Err(diagnostic) => {
                emit_diagnostic(&diagnostic, &source, input_path);
                ExitCode::FAILURE
            }
        };
    }
    let generated_directory = input_file
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join(".lim");
    let cache_directory = generated_directory.join("cache");
    match lim::check_source_with_generated_sources(
        &source,
        input_file,
        &config,
        &cache_directory,
        &generated_directory,
    ) {
        Ok(()) => {
            if !cli_proof_budget::is_default(budget) {
                println!(
                    "proof budget: work={} phase-bytes={} total-bytes={}",
                    budget.work(),
                    budget.phase_bytes(),
                    budget.total_bytes()
                );
            }
            ExitCode::SUCCESS
        }
        Err(diagnostic) => {
            emit_diagnostic(&diagnostic, &source, input_path);
            ExitCode::FAILURE
        }
    }
}

fn stack_usage_command(arguments: &[String]) -> ExitCode {
    let Some(input_path) = arguments.get(1) else {
        eprintln!("usage: lim --stack-usage INPUT [--target TARGET] [--cfg KEY=VALUE]...");
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
    let mut target_explicit = false;
    let mut index = 2;
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
                target_explicit = true;
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
            }
            "--module-path" => {
                index += 1;
                let Some(value) = arguments.get(index) else {
                    eprintln!("lim: --module-path requires a directory");
                    return ExitCode::FAILURE;
                };
                config.add_module_path(value);
            }
            other => {
                eprintln!("lim: unexpected --stack-usage argument '{other}'");
                return ExitCode::FAILURE;
            }
        }
        index += 1;
    }
    match project_for_input(input_path) {
        Ok(Some(metadata)) => {
            config.add_module_path(&metadata.source_root);
            for path in metadata.module_paths {
                config.add_module_path(path);
            }
            if !target_explicit {
                if let Some(project_target) = metadata.target {
                    target = project_target;
                }
            }
        }
        Ok(None) => {}
        Err(error) => {
            eprintln!("lim: {error}");
            return ExitCode::FAILURE;
        }
    }
    config = config.with_target(target);
    let source = match fs::read_to_string(input_path) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("lim: {input_path}: {error}");
            return ExitCode::FAILURE;
        }
    };
    let input_file = Path::new(input_path);
    let generated = input_file
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join(".lim");
    let cache = generated.join("cache");
    if arguments.first().map(String::as_str) == Some("--explain-cache") {
        let (result, report) = lim::with_cache_report(|| {
            lim::write_generated_sources_diagnostic(
                &source, input_file, &generated, &config, &cache,
            )?;
            lim::compile_source_to_assembly(&source, input_file, &config, &cache, target)?;
            Ok::<(), lim::Diagnostic>(())
        });
        println!("{report}");
        return match result {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                emit_diagnostic(&error, &source, input_path);
                ExitCode::FAILURE
            }
        };
    }
    if let Err(diagnostic) =
        lim::write_generated_sources_diagnostic(&source, input_file, &generated, &config, &cache)
    {
        emit_diagnostic(&diagnostic, &source, input_path);
        return ExitCode::FAILURE;
    }
    let assembly =
        match lim::compile_source_to_assembly(&source, input_file, &config, &cache, target) {
            Ok(assembly) => assembly,
            Err(diagnostic) => {
                emit_diagnostic(&diagnostic, &source, input_path);
                return ExitCode::FAILURE;
            }
        };
    let report = if target == lim::TargetDescription::AARCH64_LINUX {
        lim::aarch64::stack_usage_report(&assembly)
    } else {
        lim::stack_usage_report(&assembly)
    };
    match report {
        Ok(report) => {
            print!("{report}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("lim: stack analysis failed: {error}");
            ExitCode::FAILURE
        }
    }
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
            if !entry.file_name().to_string_lossy().starts_with('.') {
                collect_lim_files(&path, paths)?;
            }
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
) -> Result<
    (
        String,
        PathBuf,
        lim::CompileConfig,
        lim::TargetDescription,
        LinkOptions,
    ),
    String,
> {
    let mut input = None;
    let mut output = None;
    let mut config = lim::CompileConfig::default();
    let mut target = lim::TargetDescription::host()?;
    let mut target_explicit = false;
    let mut links = LinkOptions::default();
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
                target_explicit = true;
            }
            "--link-lib" => {
                index += 1;
                let value = arguments
                    .get(index)
                    .ok_or_else(|| "--link-lib requires a library name".to_owned())?;
                if value.is_empty() || value.starts_with('-') {
                    return Err("--link-lib requires a non-empty library name".into());
                }
                links.libraries.push(value.clone());
            }
            "--link-object" => {
                index += 1;
                let value = arguments
                    .get(index)
                    .ok_or_else(|| "--link-object requires an object-file path".to_owned())?;
                links.object_files.push(PathBuf::from(value));
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
    let metadata = project_for_input(&input)?;
    if let Some(metadata) = &metadata {
        config.add_module_path(&metadata.source_root);
        for path in &metadata.module_paths {
            config.add_module_path(path);
        }
        if !target_explicit {
            if let Some(project_target) = metadata.target {
                target = project_target;
            }
        }
        links
            .libraries
            .extend(metadata.link_libraries.iter().cloned());
        links
            .object_files
            .extend(metadata.link_objects.iter().cloned());
    }
    let output = output.unwrap_or_else(|| {
        if let Some(metadata) = &metadata {
            let stem = Path::new(&input).file_stem().unwrap_or_default();
            let mut result = metadata.output_directory.clone();
            result.push(stem);
            return result;
        }
        let path = Path::new(&input);
        let stem = path.file_stem().unwrap_or_default();
        let mut result = path
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .to_path_buf();
        result.push(stem);
        result
    });
    Ok((input, output, config.with_target(target), target, links))
}

fn project_for_input(input: &str) -> Result<Option<lim::ProjectMetadata>, String> {
    let mut directory = Path::new(input).parent().unwrap_or_else(|| Path::new("."));
    loop {
        let manifest = directory.join("lim.project");
        if manifest.is_file() {
            return lim::read_project(&manifest).map(Some);
        }
        let Some(parent) = directory.parent() else {
            return Ok(None);
        };
        directory = parent;
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct LinkOptions {
    libraries: Vec<String>,
    object_files: Vec<PathBuf>,
}

fn compile(
    input_path: &str,
    output_path: &Path,
    emit_assembly: bool,
    config: &lim::CompileConfig,
    target: lim::TargetDescription,
) -> ExitCode {
    compile_with_links(
        input_path,
        output_path,
        emit_assembly,
        config,
        target,
        &LinkOptions::default(),
    )
}

fn compile_with_links(
    input_path: &str,
    output_path: &Path,
    emit_assembly: bool,
    config: &lim::CompileConfig,
    target: lim::TargetDescription,
    links: &LinkOptions,
) -> ExitCode {
    let config = config.with_target(target);
    let config = &config;
    if let Err(error) = lim::reject_source_output_collision(Path::new(input_path), output_path) {
        eprintln!("lim: {error}");
        return ExitCode::FAILURE;
    }
    if let Some(parent) = output_path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        if let Err(error) = fs::create_dir_all(parent) {
            eprintln!("lim: {}: {error}", parent.display());
            return ExitCode::FAILURE;
        }
    }
    let _input_timing = lim::timing_stage("input_read");
    let input = match fs::read_to_string(input_path) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("lim: {input_path}: {error}");
            return ExitCode::FAILURE;
        }
    };
    drop(_input_timing);
    let input_file = Path::new(input_path);
    let generated_directory = input_file
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join(".lim");
    let generator_cache_directory = generated_directory.join("cache");
    // External objects/libraries may call Lim exports that are not reachable
    // from main in source. Keep all exports when those roots are opaque.
    let compile = if emit_assembly || !links.object_files.is_empty() || !links.libraries.is_empty()
    {
        lim::compile_source_with_generated_sources
    } else {
        lim::compile_executable_source_with_generated_sources
    };
    let assembly = match compile(
        &input,
        input_file,
        config,
        &generator_cache_directory,
        target,
        Some(output_path),
        &generated_directory,
    ) {
        Ok(assembly) => assembly,
        Err(diagnostic) => {
            emit_diagnostic(&diagnostic, &input, input_path);
            return ExitCode::FAILURE;
        }
    };

    if emit_assembly {
        let _output_timing = lim::timing_stage("output_write");
        return match lim::write_output_atomic(output_path, assembly) {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("lim: {}: {error}", output_path.display());
                ExitCode::FAILURE
            }
        };
    }

    match lim::link_native_binary(
        &assembly,
        output_path,
        &links.object_files,
        &links.libraries,
        target,
    ) {
        Ok(()) => ExitCode::SUCCESS,
        Err(diagnostic) => {
            let diagnostic = lim::locate_link_diagnostic(diagnostic, &input);
            emit_diagnostic(&diagnostic, &input, input_path);
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
#[path = "../tests/support/process.rs"]
mod test_process;

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::process::ExitStatusExt;
    use std::process::Command;

    use super::test_process as process;

    #[test]
    fn generated_selections_preserve_colons_and_hyphens_in_paths() {
        for path in ["main.lim", "/tmp/ns:foo-bar.lim", "C:\\some-dir\\main.lim"] {
            for (suffix, expected) in [
                ("42", GeneratedSelection::Lines(42, 42)),
                ("4-8", GeneratedSelection::Lines(4, 8)),
                ("4:2", GeneratedSelection::Range((4, 2), (4, 2))),
                ("4:2-8:3", GeneratedSelection::Range((4, 2), (8, 3))),
            ] {
                let (actual_path, selection) =
                    parse_generated_selection(&format!("{path}:{suffix}")).unwrap();
                assert_eq!(actual_path, PathBuf::from(path));
                assert_eq!(selection, expected);
            }
        }
    }

    #[test]
    fn generated_selection_offsets_use_unicode_scalars_and_handle_crlf_and_eof() {
        let source = "é😀x\r\nlast\n";
        assert_eq!(
            GeneratedSelection::Lines(1, 1)
                .byte_offsets(source)
                .unwrap(),
            (0, 9)
        );
        assert_eq!(
            GeneratedSelection::Lines(1, 2)
                .byte_offsets(source)
                .unwrap(),
            (0, 14)
        );
        assert_eq!(
            GeneratedSelection::Lines(3, 3)
                .byte_offsets(source)
                .unwrap(),
            (14, 14)
        );
        assert_eq!(
            GeneratedSelection::Range((1, 2), (1, 3))
                .byte_offsets(source)
                .unwrap(),
            (2, 6)
        );
        assert_eq!(
            GeneratedSelection::Range((1, 4), (1, 4))
                .byte_offsets(source)
                .unwrap(),
            (7, 7)
        );
        assert_eq!(
            GeneratedSelection::Lines(1, 1).byte_offsets("").unwrap(),
            (0, 0)
        );
        for selection in [
            GeneratedSelection::Lines(2, 1),
            GeneratedSelection::Lines(1, 4),
            GeneratedSelection::Range((1, 0), (1, 1)),
            GeneratedSelection::Range((1, 5), (1, 5)),
            GeneratedSelection::Range((2, 2), (1, 2)),
        ] {
            assert!(selection.byte_offsets(source).is_err(), "{selection:?}");
        }
        for selection in [
            "file",
            ":1",
            "file:0",
            "file:1:0",
            "file:1-x",
            "file:1:2-3:0",
            "file:999999999999999999999999",
        ] {
            assert!(parse_generated_selection(selection).is_err(), "{selection}");
        }
    }

    mod elf_fixture {
        include!("../tests/support/elf_fixture.rs");
    }

    #[test]
    fn compiles_and_runs_binary_pipeline() {
        let directory = env::temp_dir().join(format!("lim-binary-pipeline-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("program.lim");
        let output = directory.join("program");
        fs::write(&input, "(#fn main () #u64 (#return 42))").unwrap();

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
        let status = process::status(&mut Command::new(&output)).unwrap();
        assert_eq!(status.code(), Some(42));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn named_arguments_and_struct_fields_evaluate_in_declaration_order() {
        let directory =
            env::temp_dir().join(format!("lim-evaluation-order-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("program.lim");
        let output = directory.join("program");
        fs::write(
            &input,
            "(#struct Pair () ((slot-a #u64) (slot-b #u64)))\n\
             (#fn set-value ((target (#ref-mut #u64))) #u64 (#deref-set target 10u64) (#return 5u64))\n\
             (#fn read-value ((target (#ref #u64))) #u64 (#return (#deref target)))\n\
             (#fn ordered-call ((write-step #u64) (read-value #u64)) #u64 (#return read-value))\n\
             (#fn main () #u64\n\
               (#let-mut state #u64 0u64)\n\
               (#let call-result #u64 (#call ordered-call (: read-value (#call read-value (: target (#borrow state))) : write-step (#call set-value (: target (#borrow-mut state))))))\n\
               (#set state 0u64)\n\
               (#let pair Pair (#struct-literal Pair ((slot-b (#call read-value (: target (#borrow state)))) (slot-a (#call set-value (: target (#borrow-mut state)))))))\n\
               (#return (#u64::add-wrap call-result (#get pair slot-b))))",
        )
        .unwrap();

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
        let status = process::status(&mut Command::new(&output)).unwrap();
        assert_eq!(status.code(), Some(20));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn ranged_slices_run_with_empty_and_end_boundary_ranges() {
        let directory = env::temp_dir().join(format!("lim-ranged-slices-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("program.lim");
        let output = directory.join("program");
        fs::write(&input, "(#fn main () #u64 (#let values (#array #u64 3) (#array (#array #u64 3) 4u64 8u64 15u64)) (#let all (#slice #u64) (#slice-of (#borrow values))) (#let empty (#slice #u64) (#slice-range all 3usize 3usize)) (#let middle (#slice #u64) (#slice-range all 1usize 3usize)) (#assert (#usize::eq (#slice-len empty) 0usize)) (#return (#deref (#slice-idx middle 1usize))))").unwrap();
        assert_eq!(
            compile(
                input.to_str().unwrap(),
                &output,
                false,
                &lim::CompileConfig::default(),
                lim::TargetDescription::X86_64_SYSTEM_V
            ),
            ExitCode::SUCCESS
        );
        assert_eq!(
            process::status(&mut Command::new(&output)).unwrap().code(),
            Some(15)
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn mutable_slice_split_runs_with_disjoint_mutations() {
        let directory =
            env::temp_dir().join(format!("lim-mutable-slice-split-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("program.lim");
        let output = directory.join("program");
        fs::write(&input, "(#fn main () #u64 (#let-mut values (#array #u64 4) (#array (#array #u64 4) 1u64 2u64 3u64 4u64)) (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values))) (#let (#tuple left right) (#tuple (#slice-mut #u64) (#slice-mut #u64)) (#slice-mut-split view 2usize)) (#deref-set (#slice-mut-idx left 0usize) 17u64) (#deref-set (#slice-mut-idx right 0usize) 25u64) (#let-mut result #u64 (#u64::add-wrap (#deref (#slice-mut-idx left 0usize)) (#deref (#slice-mut-idx right 0usize)))) (#forget left) (#forget right) (#return result))").unwrap();
        assert_eq!(
            compile(
                input.to_str().unwrap(),
                &output,
                false,
                &lim::CompileConfig::default(),
                lim::TargetDescription::X86_64_SYSTEM_V,
            ),
            ExitCode::SUCCESS
        );
        assert_eq!(
            process::status(&mut Command::new(&output)).unwrap().code(),
            Some(42)
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn atomics_publish_updates_across_a_thread_spawn_and_join() {
        let directory = env::temp_dir().join(format!("lim-atomic-thread-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("program.lim");
        let output = directory.join("program");
        let source = "(#fn increment ((counter (#ref (#atomic #u64)))) #u64 (#return (#u64::add-wrap (#atomic-fetch-add counter 42u64 #memory-acq-rel) 42u64))) (#generate #thread-spawn (: task AtomicTask : worker increment)) (#generate #thread-spawn (: task AtomicTaskTwo : worker increment)) (#fn main () #u64 (#let-mut counter (#atomic #u64) (#atomic-init #u64 0u64)) (#let-mut byte (#atomic #i8) (#atomic-init #i8 -1i8)) (#atomic-fetch-add (#borrow byte) 1i8 #memory-relaxed) (#atomic-store (#borrow byte) 3i8 #memory-seq-cst) (#let first-result #u64 (#match (#call AtomicTask::spawn (: counter (#borrow counter))) (#case (AtomicTask::SpawnResult.Ok task) (#match (#call AtomicTask::join (: task task)) (#case (AtomicTask::JoinResult.Ok value) value) (#case (AtomicTask::JoinResult.Error (#tuple retry error)) (#panic)))) (#case (AtomicTask::SpawnResult.Error error) (#panic)))) (#let second-result #u64 (#match (#call AtomicTaskTwo::spawn (: counter (#borrow counter))) (#case (AtomicTaskTwo::SpawnResult.Ok task) (#match (#call AtomicTaskTwo::join (: task task)) (#case (AtomicTaskTwo::JoinResult.Ok value) value) (#case (AtomicTaskTwo::JoinResult.Error (#tuple retry error)) (#panic)))) (#case (AtomicTaskTwo::SpawnResult.Error error) (#panic)))) (#let observed #u64 (#atomic-load (#borrow counter) #memory-acquire)) (#forget byte) (#forget counter) (#return observed))";
        fs::write(&input, source).unwrap();
        assert_eq!(
            compile(
                input.to_str().unwrap(),
                &output,
                false,
                &lim::CompileConfig::default(),
                lim::TargetDescription::X86_64_SYSTEM_V,
            ),
            ExitCode::SUCCESS
        );
        assert_eq!(
            process::status(&mut Command::new(&output)).unwrap().code(),
            Some(84)
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn nested_destructured_mutable_references_run_natively() {
        let directory =
            env::temp_dir().join(format!("lim-destructure-references-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("program.lim");
        let output = directory.join("program");
        fs::write(
            &input,
            include_str!("../examples/destructure_mutable_references.lim"),
        )
        .unwrap();

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
        let status = process::status(&mut Command::new(&output)).unwrap();
        assert_eq!(status.code(), Some(44));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn large_reference_projections_run_with_indirect_storage() {
        let directory = env::temp_dir().join(format!(
            "lim-large-reference-projections-{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("program.lim");
        let output = directory.join("program");
        fs::write(
            &input,
            include_str!("../examples/large_reference_projections.lim"),
        )
        .unwrap();

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
        let status = process::status(&mut Command::new(&output)).unwrap();
        assert_eq!(status.code(), Some(42));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn thread_spawn_and_join_results_run_with_native_enum_layout() {
        let directory = env::temp_dir().join(format!("lim-thread-results-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("thread.lim");
        let output = directory.join("thread");
        fs::write(
            &input,
            "(#fn zero ((value #u64)) #u64 (#return 0)) (#generate #thread-spawn (: task ZeroTask : worker zero)) (#fn main () #u64 (#return (#match (#call ZeroTask::spawn (: value 41)) (#case (ZeroTask::SpawnResult.Ok task) (#match (#call ZeroTask::join (: task task)) (#case (ZeroTask::JoinResult.Ok value) (#if (#u64::eq value 0) 42 0)) (#case (ZeroTask::JoinResult.Error (#tuple retry error)) (#panic)))) (#case (ZeroTask::SpawnResult.Error error) (#panic)))))",
        )
        .unwrap();

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
        let status = process::status(&mut Command::new(&output)).unwrap();
        assert_eq!(status.code(), Some(42));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn thread_join_large_worker_results_use_indirect_storage() {
        let directory =
            env::temp_dir().join(format!("lim-thread-large-result-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("thread.lim");
        let output = directory.join("thread");
        fs::write(
            &input,
            "(#struct Large () ((a #u64) (b #u64) (c #u64) (d #u64) (e #u64) (f #u64) (g #u64))) (#fn identity ((value Large)) Large (#return value)) (#generate #thread-spawn (: task LargeTask : worker identity)) (#fn main () #u64 (#return (#match (#call LargeTask::spawn (: value (#struct-literal Large ((a 1) (b 2) (c 3) (d 4) (e 5) (f 6) (g 42))))) (#case (LargeTask::SpawnResult.Ok task) (#match (#call LargeTask::join (: task task)) (#case (LargeTask::JoinResult.Ok value) (#get value g)) (#case (LargeTask::JoinResult.Error (#tuple retry error)) (#panic)))) (#case (LargeTask::SpawnResult.Error error) (#panic)))))",
        )
        .unwrap();

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
        let status = process::status(&mut Command::new(&output)).unwrap();
        assert_eq!(status.code(), Some(42));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn thread_creation_failure_selects_explicit_spawn_error_variant() {
        let directory =
            env::temp_dir().join(format!("lim-thread-spawn-failure-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("thread.lim");
        let output = directory.join("thread");
        let source = "(#fn worker ((value #u64)) #u64 (#return value)) (#generate #thread-spawn (: task Task : worker worker)) (#fn main () #u64 (#return (#match (#call Task::spawn (: value 41)) (#case (Task::SpawnResult.Ok task) (#panic)) (#case (Task::SpawnResult.Error error) (#match error (#case Task::SpawnError.CreationError 43) (#case Task::SpawnError.AllocationError 0))))))";
        fs::write(&input, source).unwrap();

        let config = lim::CompileConfig::default();
        let assembly = lim::compile_source_to_assembly(
            source,
            &input,
            &config,
            &directory.join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        // Exercise the native negative-errno branch without requiring ptrace
        // in ordinary unit tests. The integration audit injects real syscalls.
        let site = "    mov eax, 56\n    syscall\n";
        assert_eq!(assembly.matches(site).count(), 1);
        let assembly = assembly.replace(site, "    mov rax, -11\n");
        assert!(lim::link_native_binary(
            &assembly,
            &output,
            &[],
            &[],
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .is_ok());
        assert_eq!(
            process::status(&mut Command::new(&output)).unwrap().code(),
            Some(43)
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn thread_allocation_failure_selects_explicit_spawn_error_variant() {
        let directory =
            env::temp_dir().join(format!("lim-thread-alloc-failure-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("thread.lim");
        let output = directory.join("thread");
        let source = "(#fn worker ((value #u64)) #u64 (#return value)) (#generate #thread-spawn (: task Task : worker worker)) (#fn main () #u64 (#return (#match (#call Task::spawn (: value 41)) (#case (Task::SpawnResult.Ok task) (#panic)) (#case (Task::SpawnResult.Error error) (#match error (#case Task::SpawnError.CreationError 0) (#case Task::SpawnError.AllocationError 44))))))";
        fs::write(&input, source).unwrap();

        let config = lim::CompileConfig::default();
        let assembly = lim::compile_source_to_assembly(
            source,
            &input,
            &config,
            &directory.join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        let start = assembly.find("    mov eax, 9\n").unwrap();
        let end = start + assembly[start..].find("    syscall\n").unwrap() + "    syscall\n".len();
        let mut assembly = assembly;
        assembly.replace_range(start..end, "    mov rax, -12\n");
        assert!(lim::link_native_binary(
            &assembly,
            &output,
            &[],
            &[],
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .is_ok());
        assert_eq!(
            process::status(&mut Command::new(&output)).unwrap().code(),
            Some(44)
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn thread_join_failure_selects_error_variant_without_freeing_task() {
        let directory =
            env::temp_dir().join(format!("lim-thread-join-failure-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("thread.lim");
        let output = directory.join("thread");
        let source = "(#extern-fn #abi-c exit ((status #i32)) ()) (#fn worker ((value #u64)) #u64 (#return value)) (#generate #thread-spawn (: task Task : worker worker)) (#fn main () #u64 (#return (#match (#call Task::spawn (: value 41)) (#case (Task::SpawnResult.Ok task) (#match (#call Task::join (: task task)) (#case (Task::JoinResult.Ok value) 42) (#case (Task::JoinResult.Error (#tuple retry error)) (#if (#i32::eq error 11) (#panic) (#block (#unsafe (#unsafe-call exit (: status 43))) (#panic)))))) (#case (Task::SpawnResult.Error error) (#panic)))))";
        fs::write(&input, source).unwrap();

        let config = lim::CompileConfig::default();
        let assembly = lim::compile_source_to_assembly(
            source,
            &input,
            &config,
            &directory.join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        let site = "    mov eax, 186\n    syscall\n";
        assert_eq!(assembly.matches(site).count(), 1);
        let assembly = assembly.replace(
            site,
            "    mov eax, 11\n    jmp .Llim_thread_join_fail_Task\n",
        );
        // A failed join must neither consume the mapping nor release borrows.
        // Make an accidental cleanup visibly different from the expected trap.
        let assembly = assembly.replace(
            "    mov eax, 11\n    syscall\n",
            "    mov eax, 231\n    mov edi, 77\n    syscall\n    ud2\n",
        );
        assert!(lim::link_native_binary(
            &assembly,
            &output,
            &[],
            &[],
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .is_ok());
        let status = process::status(&mut Command::new(&output)).unwrap();
        assert_eq!(status.signal(), Some(4));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn binary_arguments_accept_repeated_link_inputs() {
        let arguments = [
            "program.lim".to_owned(),
            "--link-lib".to_owned(),
            "m".to_owned(),
            "--link-object".to_owned(),
            "support.o".to_owned(),
            "--link-lib".to_owned(),
            "crypto".to_owned(),
        ];
        let (_, _, _, _, links) = binary_arguments(&arguments).unwrap();
        assert_eq!(links.libraries, ["m", "crypto"]);
        assert_eq!(links.object_files, [PathBuf::from("support.o")]);
    }

    #[test]
    fn project_manifest_settings_flow_into_binary_arguments() {
        let directory = env::temp_dir().join(format!("lim-project-cli-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(directory.join("src")).unwrap();
        fs::create_dir_all(directory.join("modules")).unwrap();
        fs::write(directory.join("modules/shared.lim"), "(#type Shared #u64)").unwrap();
        fs::write(directory.join("support.o"), "object").unwrap();
        let manifest = format!(
            "schema-version = 1\nname = \"demo\"\nsource-root = \"src\"\noutput-dir = \"build\"\nmodule-path = \"modules\"\ntarget = \"x86_64-sysv\"\nlink-lib = \"m\"\nlink-object = \"support.o\"\n"
        );
        fs::write(directory.join("lim.project"), manifest).unwrap();
        let input = directory.join("src/main.lim");
        fs::write(
            &input,
            "(#alias Shared = //modules/shared.lim::Shared) (#fn main () #u64 (#return 0u64))",
        )
        .unwrap();
        let arguments = vec![input.to_string_lossy().into_owned()];
        let (_, output, config, target, links) = binary_arguments(&arguments).unwrap();
        assert_eq!(output, directory.join("build/main"));
        assert_eq!(target, lim::TargetDescription::X86_64_SYSTEM_V);
        assert_eq!(links.libraries, ["m"]);
        assert_eq!(
            links.object_files,
            [directory.join("support.o").canonicalize().unwrap()]
        );
        let program = lim::parse_program_from_path_with_config(
            &fs::read_to_string(&input).unwrap(),
            &input,
            &config,
        )
        .unwrap();
        assert!(program.items.iter().any(|item| matches!(
            item,
            lim::Item::TypeAlias { name, .. } if name.ends_with("shared.lim::Shared")
        )));
        let _ = fs::remove_dir_all(directory);
    }

    #[test]
    fn links_external_object_for_extern_function() {
        let directory = env::temp_dir().join(format!("lim-link-object-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let object = directory.join("support.o");
        let input = directory.join("program.lim");
        let output = directory.join("program");
        fs::write(
            &object,
            elf_fixture::object(
                &[elf_fixture::Section {
                    name: ".text",
                    bytes: &[0xb8, 42, 0, 0, 0, 0xc3],
                    size: 6,
                    writable: false,
                    executable: true,
                }],
                &[elf_fixture::Symbol {
                    name: "provided_value",
                    section: Some(0),
                    value: 0,
                    global: true,
                }],
                &[],
            ),
        )
        .unwrap();
        fs::write(
            &input,
            "(#extern-fn #abi-c provided_value () #u64) (#fn main () #u64 (#return (#unsafe (#unsafe-call provided_value (:)))))",
        )
        .unwrap();
        let links = LinkOptions {
            libraries: Vec::new(),
            object_files: vec![object],
        };
        assert_eq!(
            compile_with_links(
                input.to_str().unwrap(),
                &output,
                false,
                &lim::CompileConfig::default(),
                lim::TargetDescription::X86_64_SYSTEM_V,
                &links,
            ),
            ExitCode::SUCCESS
        );
        assert_eq!(
            process::status(&mut Command::new(&output)).unwrap().code(),
            Some(42)
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn allocator_backed_vector_grows_and_destroys_elements() {
        let directory = env::temp_dir().join(format!("lim-vector-runtime-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("vec.lim");
        let output = directory.join("vec");
        fs::write(
            &input,
            include_str!("../examples/vec_allocator.lim").replace(
                "../library/cell.lim",
                &format!("{}/library/cell.lim", env!("CARGO_MANIFEST_DIR")),
            ),
        )
        .unwrap();

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
        let status = process::status(&mut Command::new(&output)).unwrap();
        assert_eq!(status.code(), Some(4));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn allocator_backed_vector_reports_allocation_failure_without_losing_vector() {
        let source = r#"
(#struct Arena () ((identity #u64)))
(#enum AllocError () (AllocError.OutOfMemory))
(#type Arena::Allocator::State Arena)
(#type Arena::Allocator::Error AllocError)
(#enum Arena::Allocator::Allocation ()
  ((Arena::Allocator::Allocation.Allocated (#ptr-mut #u8)) (Arena::Allocator::Allocation.AllocationFailed AllocError)))
(#generate #vec (: element #u64 : allocator Arena : name VecU64))
(#generate #vec-alloc (: element #u64 : allocator Arena::Allocator : vector VecU64 : destroy drop-u64))
(#fn Arena::Allocator::allocate ((allocator (#ref Arena)) (layout #usize) (alignment #usize)) Arena::Allocator::Allocation
  (#return (Arena::Allocator::Allocation.AllocationFailed AllocError.OutOfMemory)))
(#unsafe-fn Arena::Allocator::grow ((allocator (#ref Arena)) (pointer (#ptr-mut #u8))
                (old-layout #usize) (layout #usize) (alignment #usize)) Arena::Allocator::Allocation
  (#forget pointer)
  (#return (Arena::Allocator::Allocation.AllocationFailed AllocError.OutOfMemory)))
(#unsafe-fn Arena::Allocator::deallocate ((allocator (#ref Arena)) (pointer (#ptr-mut #u8))
                 (layout #usize) (alignment #usize)) ()
  (#forget pointer)
  (#return ()))
(#fn drop-u64 ((allocator (#ref Arena)) (value #u64)) () (#return ()))
(#fn main () #u64
  (#let-mut arena Arena (#struct-literal Arena ((identity 0u64))))
  (#let-mut vector VecU64 (#call VecU64::new (: allocator (#borrow arena))))
  (#let result VecU64::PushResult (#call VecU64::push (: vector (#borrow-mut vector) : element 42u64)))
  (#let status #u64
    (#match result
      (#case (VecU64::PushResult.Ok _) 0u64)
      (#case (VecU64::PushResult.Err _) 42u64)))
  (#call VecU64::free (: vector vector))
  (#forget arena)
  (#return status))
"#;
        let directory = env::temp_dir().join(format!("lim-vector-failure-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("vec-failure.lim");
        let output = directory.join("vec-failure");
        fs::write(&input, source).unwrap();
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
        let status = process::status(&mut Command::new(&output)).unwrap();
        assert_eq!(status.code(), Some(42));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn nested_multiword_aggregates_keep_layout_across_native_calls() {
        let directory =
            env::temp_dir().join(format!("lim-nested-aggregate-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("nested.lim");
        let output = directory.join("nested");
        fs::write(
            &input,
            include_str!("../examples/nested_multiword_aggregates.lim"),
        )
        .unwrap();
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
        let status = process::status(&mut Command::new(&output)).unwrap();
        assert_eq!(status.code(), Some(22));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn explicit_aggregate_destruction_runs_once_after_moves_and_returns() {
        let directory =
            env::temp_dir().join(format!("lim-explicit-destroy-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let input = directory.join("destroy.lim");
        let output = directory.join("destroy");
        fs::write(
            &input,
            include_str!("../examples/explicit_destruction.lim").replace(
                "../library/cell.lim",
                &format!("{}/library/cell.lim", env!("CARGO_MANIFEST_DIR")),
            ),
        )
        .unwrap();
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
        let status = process::status(&mut Command::new(&output)).unwrap();
        assert_eq!(status.code(), Some(2));
        fs::remove_dir_all(directory).unwrap();
    }
}
