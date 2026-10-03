use std::collections::{HashMap, HashSet};

#[derive(Default)]
struct Function {
    blocks: Vec<Block>,
}

#[derive(Default)]
struct Block {
    label: String,
    instructions: Vec<Instruction>,
}

#[derive(Default)]
struct Instruction {
    stack_delta: i64,
    frame: Option<FrameAction>,
    call: Option<String>,
    terminator: Option<Terminator>,
}

enum FrameAction {
    Save,
    Restore,
    Leave,
    Pop,
}

#[derive(Clone, Copy)]
struct StackState {
    depth: usize,
    frame: Option<usize>,
}

enum Terminator {
    Jump(String),
    JumpTable(Vec<String>),
    Branch(String),
    Stop,
    Return,
}

struct LocalUsage {
    peak: usize,
    calls: Vec<(String, usize)>,
}

struct PathUsage {
    bytes: usize,
    chain: Vec<String>,
    unknown: Vec<String>,
}

/// A worker stack must have a proven bound, not the partial bound printed for
/// an FFI caller. Analyze only reachable functions: unrelated inline assembly
/// elsewhere in an imported module must not affect the worker's stack.
pub(crate) fn bounded_entry_stack(assembly: &str, entry: &str) -> Result<usize, String> {
    let mut bodies = HashMap::<String, String>::new();
    let mut current = None;
    for line in assembly.lines() {
        if let Some((name, _)) = line
            .trim()
            .strip_prefix(".type ")
            .and_then(|s| s.split_once(", @function"))
        {
            current = Some(name.trim().to_owned());
        }
        if let Some(name) = &current {
            let body = bodies.entry(name.clone()).or_default();
            body.push_str(line);
            body.push('\n');
            if line.trim().starts_with(&format!(".size {name},")) {
                current = None;
            }
        }
    }
    fn visit(
        name: &str,
        bodies: &HashMap<String, String>,
        active: &mut Vec<String>,
        done: &mut HashMap<String, usize>,
    ) -> Result<usize, String> {
        if let Some(bytes) = done.get(name) {
            return Ok(*bytes);
        }
        if active.iter().any(|caller| caller == name) {
            return Err(format!("recursive thread call path through '{name}'"));
        }
        let body = bodies.get(name).ok_or_else(||
            format!("kernel thread reaches external/indirect callee '{name}'; foreign TLS and stack bounds are unsupported"))?;
        let functions = parse_functions(body)?;
        let own = analyze_function(&functions[name]).map_err(|error| format!("{name}: {error}"))?;
        active.push(name.to_owned());
        let mut peak = own.peak;
        for (callee, depth) in own.calls {
            let child = visit(&callee, bodies, active, done)?;
            peak = peak.max(
                depth
                    .checked_add(8)
                    .and_then(|n| n.checked_add(child))
                    .ok_or("thread stack bound overflow")?,
            );
        }
        active.pop();
        done.insert(name.to_owned(), peak);
        Ok(peak)
    }
    visit(entry, &bodies, &mut Vec::new(), &mut HashMap::new())
}

/// Analyze emitted x86-64 assembly. Internal control flow is evaluated as a
/// stack-depth graph; unresolved direct calls and indirect calls are reported
/// as unknown rather than assigned guessed bounds.
pub fn stack_usage_report(assembly: &str) -> Result<String, String> {
    let functions = parse_functions(assembly)?;
    if !functions.contains_key("main") {
        return Err("stack report requires a generated 'main' function".into());
    }
    let local = functions
        .iter()
        .map(|(name, function)| Ok((name.clone(), analyze_function(function)?)))
        .collect::<Result<HashMap<_, _>, String>>()?;
    let mut report =
        String::from("Lim generated-code stack usage (bytes from each entry's incoming RSP):\n");
    let mut entries = functions
        .keys()
        .filter(|name| name.as_str() == "main" || name.starts_with(".Llim_thread_entry_"))
        .cloned()
        .collect::<Vec<_>>();
    entries.sort();
    for entry in entries {
        let mut visiting = Vec::new();
        let usage = call_path_usage(&entry, &functions, &local, &mut visiting)?;
        let chain = usage.chain.join(" -> ");
        if usage.unknown.is_empty() {
            report.push_str(&format!(
                "  {entry}: at most {} bytes; limiting call chain: {chain}\n",
                usage.bytes
            ));
        } else {
            report.push_str(&format!(
                "  {entry}: at most {} bytes in generated code; limiting internal call chain: {chain}; total is unknown because {}\n",
                usage.bytes,
                usage.unknown.join(", ")
            ));
        }
    }
    report.push_str(
        "Bounds cover generated Lim frames, outgoing arguments, stack temporaries, and call return addresses. They exclude the runtime/startup caller and all unresolved external or indirect callees.\n",
    );
    Ok(report)
}

fn parse_functions(assembly: &str) -> Result<HashMap<String, Function>, String> {
    let lines = assembly
        .lines()
        .map(|line| line.split('#').next().unwrap_or("").trim())
        .collect::<Vec<_>>();
    // Tables contain only defined, table-relative code labels. Do not treat
    // rodata labels as executable blocks or assume an arbitrary indirect jump
    // has no successors.
    let mut tables = HashMap::<String, Vec<String>>::new();
    let mut invalid_tables = HashSet::new();
    let mut in_rodata = false;
    let mut table_label = None;
    for line in &lines {
        if *line == ".section .rodata" {
            in_rodata = true;
            table_label = None;
        } else if matches!(*line, ".text" | ".section .text") {
            in_rodata = false;
            table_label = None;
        } else if in_rodata {
            if let Some(label) = line.strip_suffix(':') {
                table_label = Some(label);
            } else if let Some(label) = table_label.filter(|_| !line.is_empty()) {
                let difference = line
                    .strip_prefix(".long ")
                    .and_then(|value| value.split_once('-'));
                match difference {
                    Some((target, base))
                        if base.trim() == label
                            && !target.trim().is_empty()
                            && !invalid_tables.contains(label) =>
                    {
                        tables
                            .entry(base.trim().to_owned())
                            .or_default()
                            .push(target.trim().to_owned());
                    }
                    _ => {
                        // Mixed data or padding cannot be mistaken for a table
                        // with fewer edges than the actual indirect dispatch.
                        invalid_tables.insert(label.to_owned());
                        tables.remove(label);
                    }
                }
            }
        }
    }
    let mut functions = HashMap::new();
    let mut current: Option<String> = None;
    in_rodata = false;
    for (line_index, line) in lines.iter().enumerate() {
        let line = line.trim();
        if line == ".section .rodata" {
            in_rodata = true;
            continue;
        }
        if matches!(line, ".text" | ".section .text") {
            in_rodata = false;
            continue;
        }
        if in_rodata {
            continue;
        }
        if let Some(rest) = line.strip_prefix(".type ") {
            if let Some((name, _)) = rest.split_once(", @function") {
                let name = name.trim().to_owned();
                current = Some(name.clone());
                functions.insert(
                    name.clone(),
                    Function {
                        blocks: vec![Block {
                            label: name,
                            instructions: Vec::new(),
                        }],
                    },
                );
            }
            continue;
        }
        if let Some(name) = line
            .strip_prefix(".size ")
            .and_then(|rest| rest.split(',').next())
        {
            if current.as_deref() == Some(name.trim()) {
                current = None;
            }
            continue;
        }
        let Some(function_name) = current.as_ref() else {
            continue;
        };
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(label) = line.strip_suffix(':') {
            let function = functions
                .get_mut(function_name)
                .expect("current function exists");
            if label == function_name {
                function.blocks[0].label = label.to_owned();
            } else {
                function.blocks.push(Block {
                    label: label.to_owned(),
                    instructions: Vec::new(),
                });
            }
            continue;
        }
        if line.starts_with('.') {
            continue;
        }
        let mut instruction = parse_instruction(line)?;
        if line == "jmp r11"
            && line_index >= 3
            && lines[line_index - 1] == "add r11, rax"
            && lines[line_index - 2] == "movsxd rax, DWORD PTR [r11+rax*4]"
        {
            if let Some(table) = lines[line_index - 3]
                .strip_prefix("lea r11, [rip+")
                .and_then(|line| line.strip_suffix(']'))
            {
                let targets = tables
                    .get(table)
                    .ok_or_else(|| format!("unknown assembly jump table '{table}'"))?;
                instruction.terminator = Some(Terminator::JumpTable(targets.clone()));
            }
        }
        let function = functions
            .get_mut(function_name)
            .expect("current function exists");
        if function.blocks.last().is_some_and(|block| {
            block
                .instructions
                .last()
                .is_some_and(|instruction| instruction.terminator.is_some())
        }) {
            function.blocks.push(Block {
                // Not a valid assembly identifier, so it cannot collide with a label.
                label: format!("<fallthrough {}>", function.blocks.len()),
                instructions: Vec::new(),
            });
        }
        function
            .blocks
            .last_mut()
            .expect("function has an entry block")
            .instructions
            .push(instruction);
    }
    Ok(functions)
}

fn parse_instruction(line: &str) -> Result<Instruction, String> {
    let (opcode, operands) = line.split_once(char::is_whitespace).unwrap_or((line, ""));
    let operands = operands.trim();
    let arguments = operands.split(',').map(str::trim).collect::<Vec<_>>();
    let destination = arguments.first().copied().unwrap_or("");
    let mut instruction = Instruction::default();
    match opcode {
        "push" => instruction.stack_delta = 8,
        "pop" if destination != "rsp" && destination != "esp" && destination != "sp" => {
            instruction.stack_delta = -8;
            if destination == "rbp" {
                instruction.frame = Some(FrameAction::Pop);
            }
        }
        "sub" | "add" if destination == "rsp" => {
            let amount = arguments
                .get(1)
                .ok_or_else(|| format!("missing stack adjustment in '{line}'"))?
                .parse::<i64>()
                .map_err(|_| format!("cannot determine stack adjustment in '{line}'"))?;
            instruction.stack_delta = if opcode == "sub" {
                amount
            } else {
                amount
                    .checked_neg()
                    .ok_or_else(|| format!("stack adjustment overflow in '{line}'"))?
            };
        }
        "mov" if arguments == ["rbp", "rsp"] => instruction.frame = Some(FrameAction::Save),
        "mov" if arguments == ["rsp", "rbp"] => instruction.frame = Some(FrameAction::Restore),
        "leave" => instruction.frame = Some(FrameAction::Leave),
        "ret" if operands.is_empty() => instruction.terminator = Some(Terminator::Return),
        "ud2" => instruction.terminator = Some(Terminator::Stop),
        "jmp" => {
            instruction.terminator = Some(Terminator::Jump(operands.to_owned()));
        }
        op if op.starts_with('j') && op != "jmp" => {
            instruction.terminator = Some(Terminator::Branch(operands.to_owned()));
        }
        "call" => instruction.call = Some(operands.to_owned()),
        _ => {
            let frame_register = |operand: &str| {
                matches!(
                    operand,
                    "rsp" | "esp" | "sp" | "spl" | "rbp" | "ebp" | "bp" | "bpl"
                )
            };
            if matches!(
                opcode,
                "enter" | "ret" | "iret" | "iretq" | "pushf" | "pushfq" | "popf" | "popfq"
            ) || (!matches!(opcode, "cmp" | "test") && frame_register(destination))
                || (matches!(opcode, "xchg" | "xadd")
                    && arguments.iter().any(|arg| frame_register(arg)))
            {
                return Err(format!("cannot determine stack effect of '{line}'"));
            }
        }
    }
    Ok(instruction)
}

fn analyze_function(function: &Function) -> Result<LocalUsage, String> {
    let labels = function
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.label.as_str(), index))
        .collect::<HashMap<_, _>>();
    let mut entries = vec![None::<StackState>; function.blocks.len()];
    let mut peaks = vec![0usize; function.blocks.len()];
    entries[0] = Some(StackState {
        depth: 0,
        frame: None,
    });
    let mut calls = Vec::new();
    let count = function.blocks.len();
    for iteration in 0..=count {
        let mut changed = false;
        for (index, block) in function.blocks.iter().enumerate() {
            let Some(start) = entries[index] else {
                continue;
            };
            let mut depth = i64::try_from(start.depth).map_err(|_| "stack depth exceeds i64")?;
            let mut frame = start.frame;
            let mut peak = start.depth;
            let mut last_terminator = None;
            for instruction in &block.instructions {
                match instruction.frame {
                    Some(FrameAction::Save) => {
                        frame = Some(usize::try_from(depth).map_err(|_| "invalid frame depth")?)
                    }
                    Some(FrameAction::Restore | FrameAction::Leave) => {
                        depth =
                            i64::try_from(frame.ok_or("cannot restore an unknown frame pointer")?)
                                .map_err(|_| "frame depth exceeds i64")?;
                        if matches!(instruction.frame, Some(FrameAction::Leave)) {
                            depth -= 8;
                            frame = None;
                        }
                    }
                    Some(FrameAction::Pop) => frame = None,
                    None => {}
                }
                if let Some(target) = &instruction.call {
                    calls.push((target.clone(), usize::try_from(depth).unwrap_or(usize::MAX)));
                    peak = peak.max(
                        usize::try_from(depth)
                            .map_err(|_| "invalid call depth")?
                            .checked_add(8)
                            .ok_or("call return address overflows stack depth")?,
                    );
                }
                depth = depth
                    .checked_add(instruction.stack_delta)
                    .ok_or_else(|| "stack depth arithmetic overflowed".to_owned())?;
                if depth < 0 {
                    return Err(format!(
                        "unbalanced stack adjustment in function block '{}'",
                        block.label
                    ));
                }
                peak = peak.max(usize::try_from(depth).map_err(|_| "stack depth exceeds usize")?);
                if instruction.terminator.is_some() {
                    last_terminator = instruction.terminator.as_ref();
                    break;
                }
            }
            peaks[index] = peaks[index].max(peak);
            let mut successors = Vec::new();
            let resolve = |target: &str| -> Result<usize, String> {
                if let Some((digits, direction)) =
                    target.split_at_checked(target.len().saturating_sub(1))
                {
                    if !digits.is_empty()
                        && digits.bytes().all(|c| c.is_ascii_digit())
                        && matches!(direction, "b" | "f")
                    {
                        let candidates = function.blocks.iter().enumerate().filter(|(i, block)| {
                            block.label == digits
                                && if direction == "b" {
                                    *i <= index
                                } else {
                                    *i > index
                                }
                        });
                        return if direction == "b" {
                            candidates.last()
                        } else {
                            candidates.into_iter().next()
                        }
                        .map(|(i, _)| i)
                        .ok_or_else(|| format!("unknown assembly branch target '{target}'"));
                    }
                }
                labels
                    .get(target)
                    .copied()
                    .ok_or_else(|| format!("unknown assembly branch target '{target}'"))
            };
            match last_terminator {
                Some(Terminator::Stop) => {}
                Some(Terminator::Return) => {
                    if depth != 0 {
                        return Err(format!("unbalanced stack at return in '{}'", block.label));
                    }
                }
                Some(Terminator::Jump(target)) => successors.push(resolve(target)?),
                Some(Terminator::JumpTable(targets)) => {
                    for target in targets {
                        successors.push(resolve(target)?);
                    }
                    successors.sort_unstable();
                    successors.dedup();
                }
                Some(Terminator::Branch(target)) => {
                    successors.push(resolve(target)?);
                    if index + 1 < count {
                        successors.push(index + 1);
                    }
                }
                None if index + 1 < count => successors.push(index + 1),
                None => {}
            }
            for successor in successors {
                if entries[successor].is_some_and(|previous| previous.frame != frame) {
                    return Err(format!(
                        "inconsistent frame pointer at '{}'",
                        function.blocks[successor].label
                    ));
                }
                match entries[successor] {
                    Some(previous)
                        if previous.depth >= usize::try_from(depth).unwrap_or(usize::MAX) => {}
                    _ => {
                        entries[successor] = Some(StackState {
                            depth: usize::try_from(depth)
                                .map_err(|_| "stack depth exceeds usize")?,
                            frame,
                        });
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
        if iteration == count {
            return Err("generated function has a loop with unbounded stack growth".into());
        }
    }
    calls.sort();
    calls.dedup();
    Ok(LocalUsage {
        peak: peaks.into_iter().max().unwrap_or(0),
        calls,
    })
}

fn call_path_usage(
    name: &str,
    functions: &HashMap<String, Function>,
    local: &HashMap<String, LocalUsage>,
    visiting: &mut Vec<String>,
) -> Result<PathUsage, String> {
    let own = local
        .get(name)
        .ok_or_else(|| format!("missing stack analysis for function '{name}'"))?;
    if visiting.iter().any(|active| active == name) {
        let mut cycle = visiting.clone();
        cycle.push(name.to_owned());
        return Ok(PathUsage {
            bytes: own.peak,
            chain: cycle.clone(),
            unknown: vec![format!(
                "recursive generated call cycle {}",
                cycle.join(" -> ")
            )],
        });
    }
    visiting.push(name.to_owned());
    let mut result = PathUsage {
        bytes: own.peak,
        chain: vec![name.to_owned()],
        unknown: Vec::new(),
    };
    for (callee, call_depth) in &own.calls {
        if let Some(callee_function) = functions.get(callee) {
            let child = call_path_usage(callee, functions, local, visiting)?;
            let candidate = call_depth
                .checked_add(8)
                .and_then(|depth| depth.checked_add(child.bytes))
                .ok_or_else(|| "stack call-path size overflowed usize".to_owned())?;
            if candidate > result.bytes {
                result.bytes = candidate;
                result.chain = vec![name.to_owned()];
                result.chain.extend(child.chain.iter().cloned());
            }
            for unknown in child.unknown {
                result.unknown.push(format!("{callee}: {unknown}"));
            }
            let _ = callee_function;
        } else {
            result
                .unknown
                .push(format!("external/indirect callee '{callee}'"));
        }
    }
    visiting.pop();
    result.unknown.sort();
    result.unknown.dedup();
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::stack_usage_report;

    fn table_assembly() -> &'static str {
        ".type main, @function\nmain:\n push rbp\n mov rbp, rsp\n push rax\n.Ldispatch:\n lea r11, [rip+.Ltable]\n movsxd rax, DWORD PTR [r11+rax*4]\n add r11, rax\n jmp r11\n.Lsmall:\n add rsp, 8\n leave\n ret\n.Llarge:\n sub rsp, 128\n call heavy\n add rsp, 128\n add rsp, 8\n leave\n ret\n.section .rodata\n.align 4\n.Ltable:\n .long .Lsmall-.Ltable\n .long .Llarge-.Ltable\n .long .Llarge-.Ltable\n.text\n.size main, .-main\n.type heavy, @function\nheavy:\n push rbp\n mov rbp, rsp\n sub rsp, 256\n leave\n ret\n.size heavy, .-heavy\n"
    }

    #[test]
    fn jump_table_bounds_include_every_arm_and_its_callees() {
        let assembly = table_assembly();
        let report = stack_usage_report(assembly).unwrap();
        assert!(report.contains("main: at most 416 bytes"), "{report}");
        assert!(report.contains("main -> heavy"), "{report}");
        assert!(!report.contains("unknown"));
        assert_eq!(super::bounded_entry_stack(assembly, "main").unwrap(), 416);
    }

    #[test]
    fn jump_table_unknown_targets_and_unbounded_backedges_are_rejected() {
        let unknown = table_assembly().replace(".long .Llarge-.Ltable", ".long .Lmissing-.Ltable");
        assert!(stack_usage_report(&unknown)
            .unwrap_err()
            .contains(".Lmissing"));
        let growing = table_assembly().replace(
            "sub rsp, 128\n call heavy",
            "push rax\n jmp .Ldispatch\n call heavy",
        );
        assert!(stack_usage_report(&growing)
            .unwrap_err()
            .contains("unbounded stack growth"));
        let arbitrary = table_assembly().replace("add r11, rax", "add r11, rcx");
        assert!(stack_usage_report(&arbitrary)
            .unwrap_err()
            .contains("branch target 'r11'"));
        let mixed = table_assembly().replace(".long .Llarge-.Ltable", ".long 0");
        assert!(stack_usage_report(&mixed)
            .unwrap_err()
            .contains("unknown assembly jump table"));
    }

    #[test]
    fn strict_worker_bounds_ignore_unrelated_assembly_but_reject_unknown_calls() {
        let assembly = ".type unrelated, @function\nunrelated:\n mov rsp, rax\n ret\n.size unrelated, .-unrelated\n.type worker, @function\nworker:\n push rbp\n mov rbp, rsp\n leave\n ret\n.size worker, .-worker\n";
        assert_eq!(super::bounded_entry_stack(assembly, "worker").unwrap(), 8);
        let foreign = assembly.replace(" leave", " call foreign\n leave");
        assert!(super::bounded_entry_stack(&foreign, "worker")
            .unwrap_err()
            .contains("external/indirect"));
        let recursive = assembly.replace(" leave", " call worker\n leave");
        assert!(super::bounded_entry_stack(&recursive, "worker")
            .unwrap_err()
            .contains("recursive"));
    }

    #[test]
    fn numeric_local_branches_resolve_nearest_forward_and_backward_definitions() {
        let assembly = ".type main, @function\nmain:\n push rbp\n mov rbp, rsp\n1:\n sub rsp, 16\n add rsp, 16\n jne 1b\n jmp 1f\n ud2\n1:\n sub rsp, 32\n add rsp, 32\n jne 1b\n leave\n ret\n.size main, .-main\n";
        assert_eq!(super::bounded_entry_stack(assembly, "main").unwrap(), 40);
    }

    #[test]
    fn reports_internal_call_chain_and_marks_external_usage_unknown() {
        let assembly = ".type main, @function\nmain:\n push rbp\n mov rbp, rsp\n sub rsp, 16\n call work\n leave\n ret\n.size main, .-main\n.type work, @function\nwork:\n push rbp\n mov rbp, rsp\n sub rsp, 32\n call write\n leave\n ret\n.size work, .-work\n";
        let report = stack_usage_report(assembly).unwrap();
        // main: 24, internal call return address: 8, work: 40,
        // external call return address: 8. External frames remain unknown.
        assert!(report.contains("main: at most 80 bytes"), "{report}");
        assert!(report.contains("main -> work"), "{report}");
        assert!(
            report.contains("external/indirect callee 'write'"),
            "{report}"
        );
    }

    #[test]
    fn detects_positive_stack_growth_loops() {
        let assembly =
            ".type main, @function\nmain:\n.Lloop:\n push rax\n jmp .Lloop\n.size main, .-main\n";
        assert!(stack_usage_report(assembly)
            .unwrap_err()
            .contains("unbounded stack growth"));
    }

    #[test]
    fn local_branches_keep_asymmetric_peaks_and_ignore_unreachable_code() {
        // The two paths use 8 + 16 and 8 + 64 bytes, not their sum.
        let assembly = ".type main, @function\nmain:\n push rbp\n mov rbp, rsp\n test eax, eax\n je .Llarge\n sub rsp, 16\n leave\n ret\n sub rsp, 4096\n call unreachable_external\n.Llarge:\n sub rsp, 64\n mov rsp, rbp\n pop rbp\n ret\n.size main, .-main\n";
        let report = stack_usage_report(assembly).unwrap();
        assert!(report.contains("main: at most 72 bytes"), "{report}");
        assert!(!report.contains("unknown"), "{report}");
    }

    #[test]
    fn conditional_fallthrough_and_nested_loops_preserve_calls() {
        let assembly = ".type main, @function\nmain:\n push rbp\n mov rbp, rsp\n.Louter:\n test eax, eax\n je .Ldone\n.Linner:\n sub rsp, 32\n call external_work\n add rsp, 32\n jne .Linner\n jmp .Louter\n.Ldone:\n leave\n ret\n.size main, .-main\n";
        let report = stack_usage_report(assembly).unwrap();
        assert!(report.contains("at most 48 bytes"), "{report}");
        assert!(report.contains("external_work"), "{report}");
    }

    #[test]
    fn unsupported_stack_writes_and_unknown_epilogues_are_rejected() {
        for instruction in [
            "and rsp, -16",
            "lea rsp, [rax]",
            "mov esp, eax",
            "pop rsp",
            "xchg rax, rsp",
            "enter 8, 0",
            "leave",
        ] {
            let assembly =
                format!(".type main, @function\nmain:\n {instruction}\n ret\n.size main, .-main\n");
            assert!(stack_usage_report(&assembly).is_err(), "{instruction}");
        }
    }

    #[test]
    fn generated_branches_loops_and_large_calls_have_bounded_frames() {
        for source in [
            include_str!("../examples/loop.lim"),
            include_str!("../examples/large_aggregate_parameters.lim"),
            include_str!("../examples/aggregate_loop_conditional.lim"),
            include_str!("../examples/nested_loop_break_scope.lim"),
            "(#fn leaf () u64 (#return 7u64)) (#fn main () u64 (#return (#if true (#call leaf (:)) 2u64)) (#return 3u64))",
        ] {
            let program = crate::parse_program(source).unwrap();
            let assembly = crate::generate_assembly(&program).unwrap();
            let report = stack_usage_report(&assembly).unwrap_or_else(|error| panic!("{error}\n{assembly}"));
            assert!(report.contains("main: at most"), "{report}");
            assert!(!report.contains("unknown"), "{report}");
        }
    }
}
