mod support;

fn check(source: &str) -> Result<(), String> {
    lim::check_types(&lim::parse_program(source)?)
}

fn function(name: &str, effects: &str, body: &str) -> String {
    format!("#fn {name} {{ #params = (); #returns = (); {effects} #body = ( {body} (#return ()) ); }}\n")
}

const SYSCALL: &str = "(#let ignored #i64 (#unsafe (#linux-syscall #i64 39usize ())))";
const COUNTER: &str = "#static counter (#atomic #u64) (#atomic-init #u64 0u64)\n";
const LOAD: &str = "(#let value #u64 (#unsafe (#atomic-load (#borrow counter) #memory-relaxed)))";
const STORE: &str = "(#unsafe (#atomic-store (#borrow counter) 1u64 #memory-relaxed))";

#[test]
fn unannotated_pure_functions_and_compile_time_constants_remain_valid() {
    check("#const answer #u64 42u64\n#fn main { #params = (); #returns = #u64; #body = ( (#return answer) ); }").unwrap();
    check(&function("main", "#effects = ();", "")).unwrap();
    check("#static counters (#array (#atomic #usize) 2) (#array-of (#array (#atomic #usize) 2) (#atomic-init #usize 0usize) (#atomic-init #usize 0usize))").unwrap();
}

#[test]
fn unannotated_io_is_rejected_without_any_predicate_contracts() {
    let error = check(&function("main", "", SYSCALL)).unwrap_err();
    assert!(
        error.contains("explicit effect qualification #io"),
        "{error}"
    );
    let error = check(&function("main", "#effects = (#io);", SYSCALL)).unwrap_err();
    assert!(error.contains("#global-access"), "{error}");
    check(&function(
        "main",
        "#effects = (#io #global-access);",
        SYSCALL,
    ))
    .unwrap();
}

#[test]
fn input_and_output_permissions_are_checked_at_calls_without_widening_callers() {
    let input = function("input", "#effects = (#io-input);", "");
    let output = function("output", "#effects = (#io-output);", "");
    let call_input = "(#call input ())";
    let call_output = "(#call output ())";
    check(&format!(
        "{input}{}",
        function("main", "#effects = (#io-input);", call_input)
    ))
    .unwrap();
    let error = check(&format!(
        "{output}{}",
        function("main", "#effects = (#io-input);", call_output)
    ))
    .unwrap_err();
    assert!(
        error.contains("#io-output") && error.contains("call to 'output'"),
        "{error}"
    );
    for effect in ["#io", "#io-input #io-output"] {
        check(&format!(
            "{input}{output}{}",
            function(
                "main",
                &format!("#effects = ({effect});"),
                "(#call input ()) (#call output ())"
            )
        ))
        .unwrap();
    }
    let broad = function("broad", "#effects = (#io);", "");
    let error = check(&format!(
        "{broad}{}",
        function(
            "main",
            "#effects = (#io-input #io-output);",
            "(#call broad ())"
        )
    ))
    .unwrap_err();
    assert!(error.contains("qualification #io in"), "{error}");
}

#[test]
fn unknown_syscalls_cannot_be_narrowed_by_a_declaration() {
    let error = check(&function(
        "main",
        "#effects = (#io-input #global-access);",
        SYSCALL,
    ))
    .unwrap_err();
    assert!(error.contains("qualification #io in"), "{error}");
}

#[test]
fn fixed_byte_io_requires_real_input_or_output_permission() {
    let input = "#fn read { #params = (); #returns = (#tuple #i64 #u8); #effects = (#io-input); #body = ((#return (#io-input-byte 0i64))); }";
    let output = "#fn write { #params = (); #returns = #i64; #effects = (#io-output); #body = ((#return (#io-output-byte 1i64 65u8))); }";
    check(input).unwrap();
    check(output).unwrap();
    let error = check(&input.replace("#effects = (#io-input);", "")).unwrap_err();
    assert!(error.contains("#io-input"), "{error}");
    let error = check(&output.replace("#io-output);", "#io-input);")).unwrap_err();
    assert!(error.contains("qualification #io-output"), "{error}");
    let error = check(&input.replace("#io-input);", "#io-output);")).unwrap_err();
    assert!(error.contains("qualification #io-input"), "{error}");
    check(&input.replace("#io-input);", "#io);")).unwrap();
    check(&output.replace("#io-output);", "#io);")).unwrap();
}

#[test]
fn fixed_byte_io_accepts_no_raw_buffer_or_syscall_selector() {
    let source = "#fn write { #params = ((pointer (#ptr #u8))); #returns = #i64; #effects = (#io-output); #body = ((#return (#io-output-byte 1i64 pointer))); }";
    assert!(check(source).unwrap_err().contains("value must be #u8"));
    let source = "#fn read { #params = (); #returns = (#tuple #i64 #u8); #effects = (#io-input); #body = ((#return (#io-input-byte 0i64 1usize))); }";
    assert!(check(source).is_err());
}

#[test]
fn standard_byte_io_interfaces_are_actually_narrow() {
    check("#std\n#fn read { #params = (); #returns = StdReadCharResult; #effects = (#io-input); #body = ((#return (#call std-read-one-char ()))); }").unwrap();
    check("#std\n#fn write { #params = (); #returns = #i64; #effects = (#io-output); #body = ((#return (#call std-write-one-char ((value 65u8))))); }").unwrap();
    let error = check("#std\n#fn write { #params = (); #returns = #i64; #effects = (#io-input); #body = ((#return (#call std-write-one-char ((value 65u8))))); }").unwrap_err();
    assert!(error.contains("#io-output"), "{error}");
}

const BYTE_ECHO: &str = "#fn main { #params = (); #returns = #u64; #effects = (#io-input #io-output); #body = (
  (#let sample (#tuple #i64 #u8) (#io-input-byte 0i64))
  (#let written #i64 (#io-output-byte 1i64 (#get sample 1)))
  (#return (#if (#bool::and (#i64::eq (#get sample 0) 1i64) (#i64::eq written 1i64)) 0u64 1u64)) ); }";

#[test]
fn fixed_byte_io_selects_target_syscalls_in_native_lowering() {
    let program = lim::parse_program(BYTE_ECHO).unwrap();
    let x86 = lim::generate_assembly_for_target(&program, lim::TargetDescription::X86_64_SYSTEM_V)
        .unwrap();
    assert!(x86.contains("xor eax, eax\n    syscall"), "{x86}");
    assert!(x86.contains("mov eax, 1\n    syscall"), "{x86}");
    let arm =
        lim::generate_assembly_for_target(&program, lim::TargetDescription::AARCH64_LINUX).unwrap();
    assert!(arm.contains("movz x8, #63"), "{arm}");
    assert!(arm.contains("movz x8, #64"), "{arm}");
}

#[test]
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn fixed_byte_io_executes_a_real_input_output_round_trip() {
    use std::{
        fs,
        process::{Command, Stdio},
        time::Duration,
    };
    let scratch = support::Scratch::new("effect-byte-io");
    let input = scratch.path().join("input");
    let program = lim::parse_program(BYTE_ECHO).unwrap();
    let assembly =
        lim::generate_assembly_for_target(&program, lim::TargetDescription::X86_64_SYSTEM_V)
            .unwrap();
    let binary = scratch.path().join("echo");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    for bytes in [b"Q".as_slice(), b"\xff".as_slice(), b"".as_slice()] {
        fs::write(&input, bytes).unwrap();
        let (status, stdout, stderr) = support::run(
            &mut Command::new(&binary).stdin(Stdio::from(fs::File::open(&input).unwrap())),
            Duration::from_secs(3),
            1024,
        )
        .unwrap();
        assert_eq!(status.code(), Some(i32::from(bytes.is_empty())), "{stderr:?}");
        assert_eq!(stdout, if bytes.is_empty() { b"\0" } else { bytes });
        assert!(stderr.is_empty());
    }
}

#[test]
fn global_reads_require_permission_and_writes_do_not_accept_read_only() {
    let error = check(&format!("{COUNTER}{}", function("main", "", LOAD))).unwrap_err();
    assert!(error.contains("(#read-global counter)"), "{error}");
    check(&format!(
        "{COUNTER}{}",
        function("main", "#effects = ((#read-global counter));", LOAD)
    ))
    .unwrap();
    let error = check(&format!(
        "{COUNTER}{}",
        function("main", "#effects = ((#read-global counter));", STORE)
    ))
    .unwrap_err();
    assert!(error.contains("(#write-global counter)"), "{error}");
    check(&format!(
        "{COUNTER}{}",
        function(
            "main",
            "#effects = ((#write-global counter));",
            &format!("{STORE} {LOAD}")
        )
    ))
    .unwrap();
}

#[test]
fn broad_global_access_covers_specific_globals_but_specific_grants_do_not_cover_unknowns() {
    check(&format!(
        "{COUNTER}{}",
        function(
            "main",
            "#effects = (#global-access);",
            &format!("{STORE} {LOAD}")
        )
    ))
    .unwrap();
    let error = check(&format!(
        "{COUNTER}{}",
        function("main", "#effects = (#io (#write-global counter));", SYSCALL)
    ))
    .unwrap_err();
    assert!(error.contains("#global-access"), "{error}");
}

#[test]
fn naming_another_global_does_not_authorize_the_target() {
    let error = check(&format!(
        "{COUNTER}#static other (#atomic #u64) (#atomic-init #u64 0u64)\n{}",
        function("main", "#effects = ((#write-global other));", STORE)
    ))
    .unwrap_err();
    assert!(error.contains("global counter)"), "{error}");
}

#[test]
fn all_runtime_globals_including_immutable_bindings_require_access() {
    let source = "#let answer #u64 42u64\n#fn main { #params = (); #returns = #u64; #body = ( (#return answer) ); }";
    let error = check(source).unwrap_err();
    assert!(error.contains("(#read-global answer)"), "{error}");
    check(&source.replace("#body =", "#effects = ((#read-global answer)); #body =")).unwrap();
}

#[test]
fn transitive_direct_calls_require_explicit_declarations_at_every_level() {
    let leaf = function("leaf", "#effects = (#io-output);", "");
    let middle = function("middle", "", "(#call leaf ())");
    let main = function("main", "#effects = (#io);", "(#call middle ())");
    let error = check(&format!("{leaf}{middle}{main}")).unwrap_err();
    assert!(
        error.contains("function 'middle'") && error.contains("#io-output"),
        "{error}"
    );
    let middle = function(
        "middle",
        "#effects = ((#effects-of @leaf));",
        "(#call leaf ())",
    );
    let error = check(&format!(
        "{leaf}{middle}{}",
        function("main", "", "(#call middle ())")
    ))
    .unwrap_err();
    assert!(
        error.contains("function 'main'") && error.contains("#io-output"),
        "{error}"
    );
    check(&format!("{leaf}{middle}{main}")).unwrap();
}

#[test]
fn cyclic_declared_inclusions_reach_a_fixed_point_without_inventing_effects() {
    let first = function(
        "first",
        "#effects = ((#effects-of @second));",
        "(#call second ())",
    );
    let second = function(
        "second",
        "#effects = (#io-output (#effects-of @first));",
        "",
    );
    let error = check(&format!(
        "{first}{second}{}",
        function("main", "#effects = (#io-input);", "(#call first ())")
    ))
    .unwrap_err();
    assert!(error.contains("#io-output"), "{error}");
}

#[test]
fn explicit_callback_groups_support_template_sets_without_inference() {
    let input = function("input", "#effects = (#io-input);", "");
    let output = function("output", "#effects = (#io-output);", "");
    let wrapper = function(
        "wrapper",
        "#effects = ((#effects-of ((@input ()) (@output @input))));",
        "(#call input ()) (#call output ())",
    );
    check(&format!(
        "{input}{output}{wrapper}{}",
        function("main", "#effects = (#io);", "(#call wrapper ())")
    ))
    .unwrap();
    let error = check(&format!(
        "{input}{output}{wrapper}{}",
        function("main", "#effects = (#io-input);", "(#call wrapper ())")
    ))
    .unwrap_err();
    assert!(error.contains("#io-output"), "{error}");
    check(&function(
        "empty",
        "#effects = ((#effects-of (() ())));",
        "",
    ))
    .unwrap();
}

#[test]
fn generated_storage_grants_cannot_authorize_unannotated_async_source() {
    let source = format!("#generate #async-fn ((protocol WorkAwait) (waker #u64) (function (#fn work () #u64 {SYSCALL} (#return 1u64))))\n");
    let error = check(&source).unwrap_err();
    assert!(
        error.contains("explicit effect qualification") && error.contains("#io"),
        "{error}"
    );
    check(&source.replace(
        "#fn work () #u64",
        "#fn work () #u64 (#effects (#io #global-access))",
    ))
    .unwrap();
}

#[test]
fn atomic_mutation_through_a_shared_parameter_is_mapped_back_to_the_global() {
    let helper = "#fn store { #params = ((value (#ref (#atomic #u64)))); #returns = (); #body = ( (#atomic-store value 1u64 #memory-relaxed) (#return ()) ); }\n";
    let call = "(#unsafe (#call store ((value (#borrow counter)))))";
    let error = check(&format!(
        "{COUNTER}{helper}{}",
        function("main", "#effects = ((#read-global counter));", call)
    ))
    .unwrap_err();
    assert!(error.contains("(#write-global counter)"), "{error}");
    check(&format!(
        "{COUNTER}{helper}{}",
        function("main", "#effects = ((#write-global counter));", call)
    ))
    .unwrap();
}

#[test]
fn broad_effect_permissions_do_not_remove_unsafe_obligations() {
    let error = check(&format!(
        "{COUNTER}{}",
        function(
            "main",
            "#effects = (#io #global-access);",
            "(#atomic-store (#borrow counter) 1u64 #memory-relaxed)"
        )
    ))
    .unwrap_err();
    assert!(error.contains("requires an enclosing (#unsafe"), "{error}");
}

#[test]
fn foreign_boundaries_require_broad_effects_even_when_uncalled() {
    let source = "#extern-fn foreign { #abi = #abi-c; #params = (); #returns = (); }\n";
    let error = check(source).unwrap_err();
    assert!(error.contains("qualification #io"), "{error}");
    check(&source.replace(
        "#returns = ();",
        "#returns = (); #effects = (#io #global-access);",
    ))
    .unwrap();
}

#[test]
fn global_initializers_have_no_ambient_effect_permissions() {
    let source = "#fn produce { #params = (); #returns = #u64; #effects = (#io-output); #body = ( (#return 1u64) ); }\n#let value #u64 (#call produce ())";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("global initializer") && error.contains("#io-output"),
        "{error}"
    );
}

#[test]
fn raw_memory_operations_require_broad_effects() {
    let source = "#fn load { #params = ((pointer (#ptr #u64))); #returns = #u64; #body = ( (#return (#unsafe (#ptr-read pointer))) ); }";
    let error = check(source).unwrap_err();
    assert!(error.contains("qualification #io"), "{error}");
    check(&source.replace("#body =", "#effects = (#io #global-access); #body =")).unwrap();
}

#[test]
fn implicit_clone_helpers_are_calls_for_effect_authorization() {
    let helper = "#struct Value () ((number #u64))\n#fn Value::clone { #params = ((value Value)); #returns = Value; #effects = (#io-output); #body = ( (#return value) ); }\n";
    let main = function(
        "main",
        "",
        "(#let value Value (#struct-literal Value ((number 1u64)))) (#forget (#clone value))",
    );
    let error = check(&format!("{helper}{main}")).unwrap_err();
    assert!(
        error.contains("#io-output") && error.contains("Value::clone"),
        "{error}"
    );
}

#[test]
fn malformed_and_non_global_qualifications_are_rejected() {
    for value in [
        "#io",
        "(#io #io)",
        "((#read-global))",
        "((#write-global counter other))",
        "(#unexpected)",
    ] {
        assert!(
            lim::parse_program(&function("main", &format!("#effects = {value};"), "")).is_err(),
            "{value}"
        );
    }
    let error = check(&function("main", "#effects = ((#read-global absent));", "")).unwrap_err();
    assert!(error.contains("not a global declaration"), "{error}");
    let error = check(&format!(
        "{COUNTER}{}",
        function("main", "#effects = ((#effects-of @counter));", "")
    ))
    .unwrap_err();
    assert!(error.contains("not a function declaration"), "{error}");
}

#[test]
fn annotations_are_signature_metadata_and_survive_formatting() {
    let source = format!(
        "{COUNTER}{}",
        function("main", "#effects = ((#write-global counter));", STORE)
    );
    let formatted = lim::format_source(&source).unwrap();
    check(&formatted).unwrap();
    let program = lim::parse_program(&source).unwrap();
    let lim::Item::Function(main) = program.items.last().unwrap() else {
        panic!()
    };
    assert_eq!(
        main.body.len(),
        2,
        "#effects must not become a runtime statement"
    );
}

#[test]
fn authorized_io_still_invalidates_predicate_evidence() {
    let predicates = "#fn small { #params = ((value (#ref #u64))); #returns = #bool; #body = ( (#return (#u64::lt (#deref value) 100u64)) ); }\n#fn consume { #params = ((value (#ref #u64))); #returns = (); #requires = ((#call small ((value value)))); #body = ( (#return ()) ); }\n";
    let source = format!("{predicates}#fn use {{ #params = ((value (#ref #u64))); #returns = (); #effects = (#io #global-access); #requires = ((#call small ((value value)))); #body = ( {SYSCALL} (#call consume ((value value))) (#return ()) ); }}");
    let error = check(&source).unwrap_err();
    assert!(error.contains("missing evidence"), "{error}");
    check(&source.replace(SYSCALL, "")).unwrap();
    let output_only = source
        .replace(SYSCALL, "(#let ignored #i64 (#io-output-byte 1i64 65u8))")
        .replace("#io #global-access", "#io-output");
    let error = check(&output_only).unwrap_err();
    assert!(error.contains("missing evidence"), "{error}");
}

#[test]
fn authorized_global_mutation_does_not_preserve_unrelated_evidence() {
    let predicates = "#fn small { #params = ((value (#ref #u64))); #returns = #bool; #body = ( (#return (#u64::lt (#deref value) 100u64)) ); }\n#fn consume { #params = ((value (#ref #u64))); #returns = (); #requires = ((#call small ((value value)))); #body = ( (#return ()) ); }\n";
    let source = format!("{COUNTER}{predicates}#fn use {{ #params = ((value (#ref #u64))); #returns = (); #effects = ((#write-global counter)); #requires = ((#call small ((value value)))); #body = ( {STORE} (#call consume ((value value))) (#return ()) ); }}");
    let error = check(&source).unwrap_err();
    assert!(error.contains("missing evidence"), "{error}");
    check(&source.replace(STORE, "")).unwrap();
}

fn write(base: &std::path::Path, path: &str, source: &str) {
    let path = base.join(path);
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, source).unwrap();
}

#[test]
fn aliases_share_canonical_global_permissions() {
    let scratch = support::Scratch::new("effect-aliases");
    write(scratch.path(), "counter.lim", COUNTER);
    let source = "#alias first = ./counter.lim::counter\n#alias second = ./counter.lim::counter\n#fn main { #params = (); #returns = (); #effects = ((#write-global first)); #body = ( (#unsafe (#atomic-store (#borrow second) 1u64 #memory-relaxed)) (#return ()) ); }";
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    lim::check_types(&program).unwrap();
}

#[test]
fn visible_operation_effects_can_include_private_globals_without_exposing_memory() {
    let scratch = support::Scratch::new("effect-privacy");
    write(
        scratch.path(),
        "counter/lib.lim",
        "#export bump\n#alias bump = ./storage.lim::bump\n",
    );
    write(
        scratch.path(),
        "counter/storage.lim",
        &format!(
            "{COUNTER}{}",
            function("bump", "#effects = ((#write-global counter));", STORE)
        ),
    );
    let source = "#alias bump = ./counter/lib.lim::bump\n#fn main { #params = (); #returns = (); #effects = ((#effects-of @bump)); #body = ( (#call bump ()) (#return ()) ); }";
    let path = scratch.path().join("main.lim");
    let program = lim::parse_program_from_path(source, &path).unwrap();
    lim::check_types(&program).unwrap();
    let escaped = source.replace(
        "(#effects-of @bump)",
        "(#write-global ./counter/storage.lim::counter)",
    );
    let error = lim::parse_program_from_path(&escaped, &path).unwrap_err();
    assert!(error.contains("private"), "{error}");
    let escaped = source.replace(
        "(#call bump ())",
        "(#unsafe (#atomic-load (#borrow ./counter/storage.lim::counter) #memory-relaxed))",
    );
    assert!(lim::parse_program_from_path(&escaped, &path)
        .unwrap_err()
        .contains("private"));
}
