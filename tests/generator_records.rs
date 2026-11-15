mod support;

use std::{fs, path::Path};

fn check(source: &str) -> lim::Program {
    let program = lim::parse_program(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    lim::check_types(&program).unwrap();
    program
}

fn diagnostic(source: &str) -> lim::Diagnostic {
    let scratch = support::Scratch::new("generator-record-diagnostic");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err()
}

fn error_at(source: &str, message: &str, needle: &str, last: bool) {
    let error = diagnostic(source);
    assert!(error.message.contains(message), "{error:?}");
    let span = error.span.expect("authored record error has a source span");
    let start = if last {
        source.rfind(needle)
    } else {
        source.find(needle)
    }
    .unwrap();
    assert_eq!(
        (span.start, span.end),
        (start, start + needle.len()),
        "{error:?}"
    );
}

#[test]
fn record_patterns_bind_by_label_with_renames_and_puns() {
    let program = check(
        r#"
#gn make { output = name; value; }
  `((#fn ,name () #u64 (#return ,value)))
#generate make { value = 42u64; output = answer; }
#fn main { #params = (); #returns = #u64; #body = ((#return (#call answer ()))); }
"#,
    );
    assert!(program.items.iter().any(|item| matches!(item,
        lim::Item::Function(function) if function.name == "answer")));
}

#[test]
fn helper_argument_puns_reuse_existing_record_syntax() {
    check("#gn-fn emit { name; } `((#type ,name #u64))\n#gn make { name; } (#gn-call emit { name; })\n#generate make { name = Answer; }\n");
    check("#gn make { name; } `((#fn ,name () #u64 (#return 42u64)))\n#generate make { name; }\n");
}

#[test]
fn canonical_pair_lists_have_the_same_named_meaning() {
    check("#gn make ((output name) (value value)) `((#fn ,name () #u64 (#return ,value)))\n#generate make ((value 42u64) (output answer))\n");
}

#[test]
fn zero_argument_calls_require_an_explicit_empty_record() {
    check("#gn make {} `((#type Answer #u64))\n#generate make {}\n");
    let error = diagnostic("#gn make {} `()\n#generate make\n");
    assert!(
        error.message.contains("exactly one named argument record"),
        "{error:?}"
    );
}

#[test]
fn positional_user_declarations_and_invocations_are_rejected() {
    for source in [
        "#gn make (name) `()\n",
        "#gn-fn helper (value) value\n",
        "#gn make { name; } `()\n#generate make Answer\n",
        "#gn make { name; value; } `()\n#generate make Answer 42u64\n",
        "#gn-fn helper {} `()\n#gn make {} (#gn-call helper)\n#generate make {}\n",
    ] {
        assert!(lim::parse_program(source).is_err(), "{source}");
    }
}

#[test]
fn duplicate_declaration_labels_point_at_the_repeated_key() {
    error_at(
        "#gn make { item = first; item = second; } `()\n",
        "duplicate generator argument label",
        "item",
        true,
    );
}

#[test]
fn duplicate_bindings_point_at_the_bound_name() {
    error_at(
        "#gn make { first = same; second = same; } `()\n",
        "duplicate generator binding",
        "same",
        true,
    );
    error_at(
        "#gn-fn helper { first = same; second = (same Copy); } `()\n",
        "duplicate generator binding",
        "same",
        true,
    );
}

#[test]
fn duplicate_call_labels_point_at_the_second_occurrence() {
    error_at(
        "#gn make { item; } `()\n#generate make { item = 1; item = 2; }\n",
        "repeats argument 'item'",
        "item",
        true,
    );
}

#[test]
fn unknown_and_missing_labels_have_authored_record_spans() {
    error_at(
        "#gn make { item; } `()\n#generate make { other = 1; }\n",
        "has no argument 'other'",
        "other",
        false,
    );
    error_at(
        "#gn make { item; } `()\n#generate make {}\n",
        "missing argument 'item'",
        "{}",
        false,
    );
}

#[test]
fn helper_calls_bind_by_label_and_evaluate_values_once_in_written_order() {
    let program = check(
        r#"
#gn-fn emit { left; right; }
  `((#type ,left #u64) (#type ,right #u32) (#type ,(#gn-gensym "body") #u8))
#gn make {} (#gn-call emit {
  right = (#gn-gensym "right");
  left = (#gn-gensym "left");
})
#generate make {}
"#,
    );
    let names = program
        .items
        .iter()
        .filter_map(|item| match item {
            lim::Item::TypeAlias { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        names.iter().any(|name| name.ends_with("1.left")),
        "{names:?}"
    );
    assert!(
        names.iter().any(|name| name.ends_with("0.right")),
        "{names:?}"
    );
    assert!(
        names.iter().any(|name| name.ends_with("2.body")),
        "{names:?}"
    );
}

#[test]
fn helper_label_errors_precede_value_evaluation_and_keep_exact_spans() {
    error_at(
        r#"
#gn-fn emit { item; } item
#gn make {} (#gn-call emit { item = (#gn-error "must not run"); item = 2; })
#generate make {}
"#,
        "repeats argument 'item'",
        "item",
        true,
    );
}

#[test]
fn helper_unknown_and_missing_labels_keep_definition_spans() {
    error_at(
        "#gn-fn emit { item; } item\n#gn make {} (#gn-call emit { other = 1; })\n#generate make {}\n",
        "has no argument 'other'", "other", false,
    );
    error_at(
        "#gn-fn emit { item; } item\n#gn make {} (#gn-call emit {\n})\n#generate make {}\n",
        "missing argument 'item'",
        "{\n}",
        false,
    );
}

#[test]
fn helper_values_fail_in_written_order() {
    let error = diagnostic(
        r#"
#gn-fn emit { left; right; } `()
#gn make {} (#gn-call emit { right = (#gn-error "right first"); left = (#gn-error "left second"); })
#generate make {}
"#,
    );
    assert!(error.message.contains("right first"), "{error:?}");
}

#[test]
fn helper_dependencies_inside_named_values_retain_cycle_detection() {
    let error = lim::parse_program(
        "#gn-fn identity { value; } value\n#gn-fn recursive { value; } (#gn-call identity { value = (#gn-call recursive { value; }); })\n",
    ).unwrap_err();
    assert!(
        error.contains("recursive generator function calls"),
        "{error}"
    );
}

#[test]
fn generation_arguments_remain_literal_syntax() {
    let program = check(
        r#"
#gn make { value; } (#gn-if (#gn-list? value) `((#type Literal #u64)) (#gn-error "argument was evaluated"))
#generate make { value = (#gn-error "this is data"); }
"#,
    );
    assert!(program.items.iter().any(|item| matches!(item,
        lim::Item::TypeAlias { name, .. } if name == "Literal")));
}

#[test]
fn capability_descriptors_work_for_generators_and_helpers() {
    let prefix = "#fn copy-value { #params = ((value #u64)); #returns = #u64; #body = ((#return value)); }\n#capability Copy #u64 ((copy-value (#u64) #u64))\n";
    check(&format!("{prefix}#gn-fn echo {{ type = (ty Copy); }} ty\n#gn make {{ type = (ty Copy); name; }} `((#type ,name ,(#gn-call echo {{ type = ty; }})))\n#generate make {{ name = Alias; type = #u64; }}\n"));
    for pattern in [
        "#gn make { type = (ty Copy); } `()\n#generate make { type = #u32; }\n",
        "#gn-fn echo { type = (ty Copy); } ty\n#gn make {} (#gn-list (#gn-call echo { type = #u32; }))\n#generate make {}\n",
    ] {
        let error = lim::parse_program(&format!("{prefix}{pattern}")).unwrap_err();
        assert!(error.contains("requires capability 'Copy'"), "{error}");
    }
}

fn artifacts(directory: &Path) -> Vec<std::path::PathBuf> {
    let directory = if directory.file_name().is_some_and(|name| name == "cache") {
        directory.parent().unwrap().join("generated")
    } else {
        directory.join("generated")
    };
    let mut paths = fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "lim"))
        .collect::<Vec<_>>();
    paths.sort();
    paths
}

#[test]
fn reordered_named_inputs_reuse_the_same_artifact_and_real_cache_entry() {
    let scratch = support::Scratch::new("generator-record-cache");
    let path = scratch.path().join("main.lim");
    let cache = scratch.path().join("cache");
    let definition = "#gn make { name; type; } `((#type ,name ,type))\n";
    for (index, call) in [
        "#generate make { name = Answer; type = #u64; }\n",
        "#generate make { type = #u64; name = Answer; }\n",
    ]
    .iter()
    .enumerate()
    {
        let (result, report) = lim::with_cache_report(|| {
            lim::parse_program_from_path_with_config_and_cache(
                &format!("{definition}{call}"),
                &path,
                &lim::CompileConfig::default(),
                &cache,
            )
        });
        lim::check_types(&result.unwrap()).unwrap();
        assert_eq!(artifacts(&cache).len(), 1);
        if index == 1 {
            assert!(
                report.contains("\"kind\":\"syntax\"") && report.contains("\"decision\":\"hit\""),
                "{report}"
            );
        }
    }
}

#[test]
fn repeated_reordered_invocations_deduplicate_before_publication() {
    let program = check("#gn make { name; type; } `((#type ,name ,type))\n#generate make { name = Answer; type = #u64; }\n#generate make { type = #u64; name = Answer; }\n");
    assert_eq!(
        program
            .items
            .iter()
            .filter(|item| matches!(item,
        lim::Item::TypeAlias { name, .. } if name == "Answer"))
            .count(),
        1
    );
}

#[test]
fn named_patterns_keep_labels_literal_and_renamed_bindings_local() {
    let scratch = support::Scratch::new("generator-record-binding-context");
    fs::write(scratch.path().join("types.lim"), "#type Number #u64\n").unwrap();
    let source = "#alias label = ./types.lim::Number\n#gn make { label = value; } `((#type Alias ,value))\n#generate make { label = #u64; }\n";
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    lim::check_types(&program).unwrap();
}

#[test]
fn imported_definition_and_invocation_contexts_survive_cache_reordering() {
    let scratch = support::Scratch::new("generator-record-authority");
    let module = scratch.path().join("module");
    fs::create_dir(&module).unwrap();
    fs::write(module.join("lib.lim"), r#"
#export make
#fn secret { #params = (); #returns = #u64; #body = ((#return 2u64)); }
#gn-fn identity { value; } value
#gn make { name; body; } `((#fn ,name () #u64 (#return (#u64::add-wrap (#call @secret ()) ,(#gn-call identity { value = body; })))))
"#).unwrap();
    let header = "#alias make = ./module/lib.lim::make\n#fn input { #params = (); #returns = #u64; #body = ((#return 40u64)); }\n";
    for call in [
        "#generate make { name = answer; body = (#call @input ()); }\n",
        "#generate make { body = (#call @input ()); name = answer; }\n",
    ] {
        let program = lim::parse_program_from_path_with_config_and_cache(
            &format!("{header}{call}"),
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
        )
        .unwrap();
        lim::check_types(&program).unwrap();
    }
    let forbidden = format!("{header}#generate make {{ name = stolen; body = (#call @./module/lib.lim::secret ()); }}\n");
    let error =
        lim::parse_program_from_path(&forbidden, &scratch.path().join("main.lim")).unwrap_err();
    assert!(error.contains("private"), "{error}");
}

#[test]
fn builtin_named_argument_normalization_remains_unchanged() {
    check("#generate #optional { name = Maybe?; type = #u64; }\n");
}
