use std::collections::HashMap;

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
    call: Option<String>,
    terminator: Option<Terminator>,
}

enum Terminator {
    Jump(String),
    Branch(String),
    Stop,
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
    let mut functions = HashMap::new();
    let mut current: Option<String> = None;
    for line in assembly.lines() {
        let line = line.trim();
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
        if line.is_empty() || line.starts_with('.') || line.starts_with('#') {
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
        let instruction = parse_instruction(line)?;
        functions
            .get_mut(function_name)
            .expect("current function exists")
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
    let mut instruction = Instruction::default();
    match opcode {
        "push" => instruction.stack_delta = 8,
        "pop" => instruction.stack_delta = -8,
        "sub" | "add" if operands.starts_with("rsp,") => {
            let amount = operands[4..]
                .trim()
                .parse::<i64>()
                .map_err(|_| format!("cannot determine stack adjustment in '{line}'"))?;
            instruction.stack_delta = if opcode == "sub" { amount } else { -amount };
        }
        "leave" | "ret" | "ud2" => instruction.terminator = Some(Terminator::Stop),
        "jmp" => {
            instruction.terminator = Some(Terminator::Jump(operands.to_owned()));
        }
        op if op.starts_with('j') && op != "jmp" => {
            instruction.terminator = Some(Terminator::Branch(operands.to_owned()));
        }
        "call" => instruction.call = Some(operands.to_owned()),
        _ => {}
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
    let mut entries = vec![None::<usize>; function.blocks.len()];
    let mut peaks = vec![0usize; function.blocks.len()];
    entries[0] = Some(0);
    let mut calls = Vec::new();
    let count = function.blocks.len();
    for iteration in 0..=count {
        let mut changed = false;
        for (index, block) in function.blocks.iter().enumerate() {
            let Some(start) = entries[index] else {
                continue;
            };
            let mut depth = i64::try_from(start).map_err(|_| "stack depth exceeds i64")?;
            let mut peak = start;
            let mut last_terminator = None;
            for instruction in &block.instructions {
                if let Some(target) = &instruction.call {
                    calls.push((target.clone(), usize::try_from(depth).unwrap_or(usize::MAX)));
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
                }
            }
            peaks[index] = peaks[index].max(peak);
            let mut successors = Vec::new();
            match last_terminator {
                Some(Terminator::Stop) => {}
                Some(Terminator::Jump(target)) => successors.push(
                    *labels
                        .get(target.as_str())
                        .ok_or_else(|| format!("unknown assembly branch target '{target}'"))?,
                ),
                Some(Terminator::Branch(target)) => {
                    successors.push(
                        *labels
                            .get(target.as_str())
                            .ok_or_else(|| format!("unknown assembly branch target '{target}'"))?,
                    );
                    if index + 1 < count {
                        successors.push(index + 1);
                    }
                }
                None if index + 1 < count => successors.push(index + 1),
                None => {}
            }
            for successor in successors {
                match entries[successor] {
                    Some(previous) if previous >= usize::try_from(depth).unwrap_or(usize::MAX) => {}
                    _ => {
                        entries[successor] =
                            Some(usize::try_from(depth).map_err(|_| "stack depth exceeds usize")?);
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

    #[test]
    fn reports_internal_call_chain_and_marks_external_usage_unknown() {
        let assembly = ".type main, @function\nmain:\n push rbp\n mov rbp, rsp\n sub rsp, 16\n call work\n leave\n ret\n.size main, .-main\n.type work, @function\nwork:\n push rbp\n mov rbp, rsp\n sub rsp, 32\n call write\n leave\n ret\n.size work, .-work\n";
        let report = stack_usage_report(assembly).unwrap();
        assert!(report.contains("main: at most 72 bytes"), "{report}");
        assert!(report.contains("main -> work"), "{report}");
        assert!(
            report.contains("external/indirect callee 'write'"),
            "{report}"
        );
    }

    #[test]
    fn detects_positive_stack_growth_loops() {
        let assembly =
            ".type main, @function\nmain:\nloop:\n push rax\n jmp loop\n.size main, .-main\n";
        assert!(stack_usage_report(assembly)
            .unwrap_err()
            .contains("unbounded stack growth"));
    }
}
