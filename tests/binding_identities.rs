fn checked_dump(source: &str) -> String {
    let program = lim::parse_program(source).expect("valid Lim source");
    lim::CheckedProgram::validate(&program)
        .expect("source typechecks")
        .dump_typed_ir()
}

fn binding_lines(dump: &str) -> Vec<&str> {
    dump.lines()
        .map(str::trim)
        .filter(|line| line.starts_with("binding "))
        .collect()
}

#[test]
fn same_spelled_match_payloads_have_distinct_typed_bindings_and_stable_ids() {
    let source = "#enum Value () ((Value.Small #u32) (Value.Large #u64))
#fn inspect ((value Value)) #u64
          (#return (#match value
            (#case (Value.Small item) (#as item #u64))
            (#case (Value.Large item) item)))\n";

    let dump = checked_dump(source);
    let items: Vec<_> = binding_lines(&dump)
        .into_iter()
        .filter(|line| line.ends_with(" U32") || line.ends_with(" U64"))
        .collect();
    assert_eq!(
        items.len(),
        2,
        "each match arm owns an item binding: {dump}"
    );
    assert!(items.iter().any(|line| line.ends_with("U32")), "{dump}");
    assert!(items.iter().any(|line| line.ends_with("U64")), "{dump}");

    let ids: Vec<_> = items
        .iter()
        .map(|item| {
            item.strip_prefix("binding ")
                .and_then(|line| line.split(':').next())
                .unwrap()
        })
        .collect();
    assert_ne!(
        ids[0], ids[1],
        "the payload declarations need distinct IDs: {dump}"
    );
    for (id, binding) in ids.into_iter().zip(items) {
        let ty = binding.split_whitespace().last().unwrap();
        assert!(
            dump.lines()
                .any(|line| line.contains(&format!("Some({ty})"))
                    && line.contains("Symbol {")
                    && line.contains(&format!("binding: Some(BindingId({id}))"))),
            "binding {id} has no correctly typed Symbol use: {dump}"
        );
    }

    let independently_parsed_dump = checked_dump(source);
    assert_eq!(dump, independently_parsed_dump);
}

#[test]
fn unused_destructured_names_are_recorded_as_bindings() {
    let source = "#struct Pair () ((left #u32) (right #u64))
#fn main ((pair Pair)) #u64
          (#let (Pair unused_left unused_right) Pair pair)
          (#return 0u64)\n";

    let dump = checked_dump(source);
    let bindings = binding_lines(&dump);
    assert!(
        bindings
            .iter()
            .any(|line| line.ends_with(": unused_left U32")),
        "{dump}"
    );
    assert!(
        bindings
            .iter()
            .any(|line| line.ends_with(": unused_right U64")),
        "{dump}"
    );
    for name in ["unused_left", "unused_right"] {
        let line = bindings
            .iter()
            .find(|line| line.contains(&format!(": {name} ")))
            .unwrap();
        let id = line
            .strip_prefix("binding ")
            .unwrap()
            .split(':')
            .next()
            .unwrap();
        assert!(
            dump.contains(&format!("binding: Some(BindingId({id}))")),
            "{dump}"
        );
    }
}

#[test]
fn scoped_bindings_and_assignment_roots_keep_local_and_global_identity_separate() {
    let source = "#static tOTAL #u64 0u64
#fn main () #u64
          (#let-mut local #u64 1u64)
          (#set local 2u64)
          (#block (#let inside #u32 4u32) inside)
          (#loop (#let iteration #u32 5u32) (#break))
          (#return (#u64::add-wrap local (#unsafe tOTAL)))\n";

    let dump = checked_dump(source);
    let bindings = binding_lines(&dump);
    for name in ["local", "inside", "iteration"] {
        assert!(
            bindings
                .iter()
                .any(|line| line.contains(&format!(": {name} "))),
            "{dump}"
        );
    }
    assert!(
        !bindings.iter().any(|line| line.contains(": tOTAL ")),
        "static is not a local binding: {dump}"
    );
    assert!(
        !bindings.iter().any(|line| ["set", "block", "loop", "break"]
            .iter()
            .any(|label| line.contains(&format!(": {label} ")))),
        "syntax labels are not bindings: {dump}"
    );
    assert!(
        dump.contains("Local(BindingId("),
        "local assignment lacks binding identity: {dump}"
    );
    assert!(
        dump.contains("Declaration(Global(GlobalId(0)))"),
        "static reference lacks global identity: {dump}"
    );
}

#[test]
fn let_else_bindings_are_available_after_success_and_not_in_the_failure_body() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#fn success ((value Maybe)) #u64
          (#let-else (Maybe.Some payload) Maybe value (#return 0u64))
          (#return payload)
#fn failure ((value Maybe)) #u64
          (#let-else (Maybe.Some payload) Maybe value
            (#let payload #u32 7u32)
            (#return (#as payload #u64)))\n          (#return payload)\n";

    let dump = checked_dump(source);
    let function_body = |function: &str| {
        dump.split_once(&format!("function {function}\n"))
            .map(|(_, body)| body.split("\nfunction ").next().unwrap())
            .unwrap_or_else(|| panic!("missing function {function}: {dump}"))
    };
    let success = function_body("success");
    let success_bindings: Vec<_> = binding_lines(success)
        .into_iter()
        .filter(|line| line.ends_with(" U64"))
        .collect();
    assert_eq!(success_bindings.len(), 1, "{success}");

    let failure = function_body("failure");
    let failure_bindings: Vec<_> = binding_lines(failure)
        .into_iter()
        .filter(|line| line.ends_with(" U32") || line.ends_with(" U64"))
        .collect();
    assert_eq!(failure_bindings.len(), 2, "{failure}");
    assert!(failure_bindings.iter().any(|line| line.ends_with(" U32")));
    assert!(failure_bindings.iter().any(|line| line.ends_with(" U64")));
    let ids: Vec<_> = failure_bindings
        .iter()
        .map(|line| {
            line.strip_prefix("binding ")
                .unwrap()
                .split(':')
                .next()
                .unwrap()
        })
        .collect();
    assert_ne!(
        ids[0], ids[1],
        "failure and success payloads need separate identities: {failure}"
    );
    for (id, binding) in ids.into_iter().zip(failure_bindings) {
        let ty = binding.split_whitespace().last().unwrap();
        assert!(
            failure
                .lines()
                .any(|line| line.contains(&format!("Some({ty})"))
                    && line.contains("Symbol {")
                    && line.contains(&format!("binding: Some(BindingId({id}))"))),
            "payload binding {id} has no correctly typed symbol use: {failure}"
        );
    }
}
