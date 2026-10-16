mod support;

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("type-properties");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn inline_linearity_propagates_through_struct_enum_tuple_and_array() {
    let cases = [
        (
            "nested struct",
            "value",
            "(#struct Resource (#linear) ((value #u64)))
             (#struct Nested () ((payload Resource)))
             (#fn main () #u64
               (#let resource Resource (#struct-literal Resource (: value 1u64)))
               (#let value Nested (#struct-literal Nested (: payload resource)))
               (#return 0u64))",
        ),
        (
            "enum with one linear payload variant",
            "choice",
            "(#struct Resource (#linear) ((value #u64)))
             (#enum Choice () ((Empty) (Selected (#tuple #bool Resource))))
             (#fn main () #u64
               (#let choice Choice (Empty))
               (#return 0u64))",
        ),
        (
            "tuple containing a linear aggregate",
            "value",
            "(#struct Resource (#linear) ((value #u64)))
             (#fn main () #u64
               (#let value (#tuple #u64 Resource)
                 (#tuple 3u64 (#struct-literal Resource ((value 4u64)))))
               (#return 0u64))",
        ),
        (
            "array containing a linear aggregate",
            "value",
            "(#struct Resource (#linear) ((value #u64)))
             (#fn main () #u64
               (#let value (#array Resource 1)
                 (#array-of (#array Resource 1)
                   (#struct-literal Resource ((value 5u64)))))
               (#return 0u64))",
        ),
    ];

    for (description, binding, source) in cases {
        let error = compile(source).expect_err(description);
        assert_eq!(
            error.code,
            lim::DiagnosticCode::Linear,
            "{description}: {error:?}"
        );
        let span = error
            .span
            .expect("linear rejection should identify its source");
        assert!(span.start < span.end, "{description}: {error:?}");

        let consumed = source.replacen(
            "(#return 0u64)",
            &format!("(#forget {binding}) (#return 0u64)"),
            1,
        );
        compile(&consumed).unwrap_or_else(|error| {
            panic!("consuming the {description} control should compile: {error:?}")
        });
    }
}

#[test]
fn copy_fields_and_shared_references_do_not_create_linear_obligations() {
    let source = "(#struct Resource (#linear) ((value #u64)))
        (#struct CopyView () ((number #u64) (view (#ref Resource))))
        (#fn main ((view (#ref Resource))) #u64
          (#let value CopyView (#struct-literal CopyView
            ((number 8u64) (view view))))
          (#let duplicate CopyView (#clone value))
          (#return (#get duplicate number)))";
    compile(source).unwrap_or_else(|error| {
        panic!("Copy fields and references to linear resources should remain Copy: {error:?}")
    });
}
