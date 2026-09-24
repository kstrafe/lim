use std::process::Command;

struct Case {
    name: &'static str,
    diagnostic_code: &'static str,
    offending_line: &'static str,
    line_number: usize,
}

#[test]
fn compilation_errors_render_the_offending_source_line() {
    let cases = [
        Case {
            name: "lex",
            diagnostic_code: "E1000",
            offending_line: "  (#return \"unterminated)",
            line_number: 2,
        },
        Case {
            name: "parse",
            diagnostic_code: "E2000",
            offending_line: "  (#return 0u64",
            line_number: 2,
        },
        Case {
            name: "import",
            diagnostic_code: "E4000",
            offending_line: "(#import \"missing-module.lim\")",
            line_number: 1,
        },
        Case {
            name: "imported",
            diagnostic_code: "E4000",
            offending_line: "(#import \"missing-dependency.lim\")",
            line_number: 1,
        },
        Case {
            name: "cycle-a",
            diagnostic_code: "E4000",
            offending_line: "(#import \"cycle-a.lim\")",
            line_number: 1,
        },
        Case {
            name: "cfg",
            diagnostic_code: "E4000",
            offending_line: "(#cfg-if (#cfg-is #platfrom linux) (#fn main () u64 (#return 0u64)))",
            line_number: 1,
        },
        Case {
            name: "type",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#u64.+.wrap value missing))",
            line_number: 3,
        },
        Case {
            name: "mismatched-let",
            diagnostic_code: "E4000",
            offending_line: "  (#let total u64 count)",
            line_number: 3,
        },
        Case {
            name: "nested-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#u64.+.wrap 1u64 false))",
            line_number: 2,
        },
        Case {
            name: "top-level-mismatch",
            diagnostic_code: "E4000",
            offending_line: "(#let TOTAL u64 true)",
            line_number: 1,
        },
        Case {
            name: "struct-literal",
            diagnostic_code: "E4000",
            offending_line: "  (#let point Point (#struct-literal Point ((y 1u64))))",
            line_number: 3,
        },
        Case {
            name: "struct-literal-duplicate-field",
            diagnostic_code: "E4000",
            offending_line: "  (#let point Point (#struct-literal Point ((x 1u64) (x 2u64))))",
            line_number: 3,
        },
        Case {
            name: "call-arguments",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#call take (#fn-args (other 42u64))))",
            line_number: 4,
        },
        Case {
            name: "call-missing-argument",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#call take (#fn-args )))",
            line_number: 4,
        },
        Case {
            name: "call-duplicate-argument",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#call take (#fn-args (value 1u64) (value 2u64))))",
            line_number: 4,
        },
        Case {
            name: "borrow",
            diagnostic_code: "E4100",
            offending_line: "  (#set value 2u64)",
            line_number: 4,
        },
        Case {
            name: "linear",
            diagnostic_code: "E4200",
            offending_line:
                "  (#let resource Resource (#struct-literal Resource ((value (#cell 1u64)))))",
            line_number: 3,
        },
        Case {
            name: "unsafe",
            diagnostic_code: "E4300",
            offending_line: "  (#return VALUE)",
            line_number: 3,
        },
        Case {
            name: "generator",
            diagnostic_code: "E3000",
            offending_line: "(@fail)",
            line_number: 2,
        },
        Case {
            name: "generator-imported",
            diagnostic_code: "E3000",
            offending_line: "(@fail)",
            line_number: 2,
        },
        Case {
            name: "generator-function-recursion",
            diagnostic_code: "E3000",
            offending_line: "(#gn-fn second (x) (#gn-call first x))",
            line_number: 2,
        },
        Case {
            name: "generator-capability",
            diagnostic_code: "E3000",
            offending_line: "(#capability order u64 ((missing (u64 u64) bool)))",
            line_number: 1,
        },
        Case {
            name: "generator-capability-signature",
            diagnostic_code: "E3000",
            offending_line: "(#capability order u64 ((compare (u64 u64) u64)))",
            line_number: 2,
        },
        Case {
            name: "generator-capability-duplicate-operation",
            diagnostic_code: "E3000",
            offending_line:
                "(#capability order u64 ((compare (u64 u64) bool) (compare (u64 u64) bool)))",
            line_number: 2,
        },
        Case {
            name: "generator-capability-duplicate-type",
            diagnostic_code: "E3000",
            offending_line: "(#capability order u64 ((compare (u64 u64) bool)))",
            line_number: 3,
        },
        Case {
            name: "duplicate-generator",
            diagnostic_code: "E3000",
            offending_line: "(#generator make () (#gn-list))",
            line_number: 2,
        },
        Case {
            name: "codegen",
            diagnostic_code: "E5000",
            offending_line: "(#const First u64 (#u64.+.wrap Second 1u64))",
            line_number: 1,
        },
        Case {
            name: "nonconstant-static",
            diagnostic_code: "E5000",
            offending_line: "(#static VALUE u64 (#call get-value (#fn-args)))",
            line_number: 2,
        },
        Case {
            name: "recursive-call",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#call worker (#fn-args)))",
            line_number: 2,
        },
        Case {
            name: "duplicate-type",
            diagnostic_code: "E4000",
            offending_line: "(#struct Token ())",
            line_number: 2,
        },
        Case {
            name: "duplicate-parameter",
            diagnostic_code: "E4000",
            offending_line: "(#fn main ((value u64) (value u64)) u64 (#return value))",
            line_number: 1,
        },
        Case {
            name: "duplicate-field",
            diagnostic_code: "E4000",
            offending_line: "(#struct Point ((x u64) (x u64)))",
            line_number: 1,
        },
        Case {
            name: "duplicate-variant",
            diagnostic_code: "E2000",
            offending_line: "(#enum State (Open Closed Open))",
            line_number: 1,
        },
        Case {
            name: "duplicate-variant-global",
            diagnostic_code: "E4000",
            offending_line: "(#enum Other (Open))",
            line_number: 2,
        },
        Case {
            name: "recursive-alias",
            diagnostic_code: "E4000",
            offending_line: "(#type First Second)",
            line_number: 1,
        },
        Case {
            name: "duplicate-global",
            diagnostic_code: "E4000",
            offending_line: "(#let COUNT u64 2u64)",
            line_number: 2,
        },
        Case {
            name: "duplicate-function",
            diagnostic_code: "E3000",
            offending_line: "(#fn main () u64 (#return 2u64))",
            line_number: 2,
        },
        Case {
            name: "repr-c-discriminant",
            diagnostic_code: "E4000",
            offending_line: "(#enum Code #repr-c ((TooLarge 2147483648)))",
            line_number: 1,
        },
        Case {
            name: "unsafe-impl",
            diagnostic_code: "E4000",
            offending_line: "(#unsafe-impl #send Missing)",
            line_number: 1,
        },
        Case {
            name: "thread-send",
            diagnostic_code: "E4000",
            offending_line: "(#fn worker ((pointer (#ptr u64))) u64 (#return 0u64))",
            line_number: 1,
        },
        Case {
            name: "thread-task-field",
            diagnostic_code: "E4000",
            offending_line: "(#struct Container ((task Task)))",
            line_number: 3,
        },
        Case {
            name: "thread-worker-unknown-type",
            diagnostic_code: "E4000",
            offending_line: "(#fn worker ((argument Missing)) u64 (#return 1u64))",
            line_number: 1,
        },
        Case {
            name: "unknown-local-type",
            diagnostic_code: "E4000",
            offending_line: "(#fn main () u64 (#let value Missing 1u64) (#return 0u64))",
            line_number: 1,
        },
        Case {
            name: "immutable-assignment",
            diagnostic_code: "E4000",
            offending_line: "  (#set value 2u64)",
            line_number: 3,
        },
        Case {
            name: "non-array-index",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#index value 0usize))",
            line_number: 3,
        },
        Case {
            name: "non-array-assignment",
            diagnostic_code: "E4000",
            offending_line: "  (#set-index value 0usize 2u64)",
            line_number: 3,
        },
        Case {
            name: "non-struct-assignment",
            diagnostic_code: "E4000",
            offending_line: "  (#set-field value field 2u64)",
            line_number: 3,
        },
        Case {
            name: "non-slice-len",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#slice-len value))",
            line_number: 3,
        },
        Case {
            name: "non-slice-idx",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#slice-idx value 0usize))",
            line_number: 3,
        },
        Case {
            name: "non-array-slice-of",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#slice-of value))",
            line_number: 3,
        },
        Case {
            name: "non-struct-get",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#get value field))",
            line_number: 3,
        },
        Case {
            name: "non-enum-payload",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#get-payload value Variant 0))",
            line_number: 3,
        },
        Case {
            name: "unknown-get-field",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#get point missing))",
            line_number: 4,
        },
        Case {
            name: "unknown-payload-variant",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#get-payload value MissingVariant 0))",
            line_number: 4,
        },
        Case {
            name: "unknown-match-variant",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value (Missing 0u64) (Ready 1u64)))",
            line_number: 4,
        },
        Case {
            name: "unknown-let-else-variant",
            diagnostic_code: "E4000",
            offending_line: "  (#let-else Missing State value (#return 1u64))",
            line_number: 4,
        },
        Case {
            name: "duplicate-enum-match-pattern",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value (Ready 0u64) (Ready 1u64)))",
            line_number: 4,
        },
        Case {
            name: "duplicate-wildcard-match-pattern",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match true (_ 0u64) (_ 1u64)))",
            line_number: 2,
        },
        Case {
            name: "out-of-range-match-integer",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value (300 0u64) (_ 1u64)))",
            line_number: 3,
        },
        Case {
            name: "duplicate-match-integer",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value (2 0u64) (2 1u64) (_ 0u64)))",
            line_number: 3,
        },
        Case {
            name: "duplicate-character-match-pattern",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match #\\a (#\\b 0u64) (#\\b 1u64)))",
            line_number: 2,
        },
        Case {
            name: "out-of-range-match-range",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value ((#range 2 300) 0u64) (_ 1u64)))",
            line_number: 3,
        },
        Case {
            name: "reversed-match-range",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value ((#range 10 2) 0u64) (_ 1u64)))",
            line_number: 3,
        },
        Case {
            name: "non-reference-deref-set",
            diagnostic_code: "E4000",
            offending_line: "  (#deref-set value 2u64)",
            line_number: 3,
        },
        Case {
            name: "thread-worker-missing",
            diagnostic_code: "E4000",
            offending_line: "(#thread-task Task missing-worker)",
            line_number: 1,
        },
        Case {
            name: "thread-worker-reference-result",
            diagnostic_code: "E4000",
            offending_line: "(#fn worker ((value (#ref u64))) (#ref u64) (#return value))",
            line_number: 1,
        },
        Case {
            name: "thread-task-function-signature",
            diagnostic_code: "E4000",
            offending_line: "(#fn bad ((task Task)) u64 (#return 0u64))",
            line_number: 3,
        },
        Case {
            name: "thread-task-type-alias",
            diagnostic_code: "E4000",
            offending_line: "(#type TaskAlias Task)",
            line_number: 3,
        },
    ];

    for case in cases {
        let source_path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/ui/");
        let input = format!("{source_path}{}.lim", case.name);
        let output = std::env::temp_dir().join(format!(
            "lim-ui-{}-{}-{}.s",
            std::process::id(),
            case.name,
            case.line_number
        ));
        let result = Command::new(env!("CARGO_BIN_EXE_lim"))
            .args(["--emit-asm", &input, output.to_str().unwrap()])
            .output()
            .unwrap_or_else(|error| panic!("failed to run Lim UI case {}: {error}", case.name));

        assert!(
            !result.status.success(),
            "UI case {} unexpectedly compiled",
            case.name
        );
        let stderr = String::from_utf8(result.stderr).expect("compiler stderr is UTF-8");
        assert!(
            stderr.contains(&format!("error[{}]", case.diagnostic_code)),
            "UI case {} had the wrong diagnostic category:\n{stderr}",
            case.name
        );
        let expected_source = match case.name {
            "imported" => format!("{source_path}imported/broken-module.lim"),
            "cycle-a" => format!("{source_path}cycle-b.lim"),
            "generator-imported" => {
                format!("{source_path}generator-imported/module.lim")
            }
            _ => input.clone(),
        };
        assert!(
            stderr.contains(&format!("--> {expected_source}:{}:", case.line_number)),
            "UI case {} did not point to line {}:\n{stderr}",
            case.name,
            case.line_number
        );
        assert!(
            stderr.contains(case.offending_line),
            "UI case {} did not show its offending source line:\n{stderr}",
            case.name
        );
        assert!(
            stderr.lines().any(|line| line.contains('^')),
            "UI case {} did not underline the source:\n{stderr}",
            case.name
        );
        if case.name == "mismatched-let" {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            assert_eq!(
                source_row.find("count"),
                underline_row.find('^'),
                "type mismatch underline is not aligned under the offending value:\n{stderr}"
            );
        }
        if case.name == "top-level-mismatch" {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            assert_eq!(
                source_row.find("true"),
                underline_row.find('^'),
                "top-level type mismatch underline is not aligned under the incompatible initializer:\n{stderr}"
            );
        }
        if case.name == "nested-mismatch" {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            assert_eq!(
                source_row.find("false"),
                underline_row.find('^'),
                "nested type mismatch underline is not aligned under its incompatible operand:\n{stderr}"
            );
        }
        if matches!(
            case.name,
            "thread-worker-unknown-type" | "unknown-local-type"
        ) {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            assert_eq!(
                source_row.find("Missing"),
                underline_row.find('^'),
                "unknown type diagnostic is not aligned under the unknown type name for {}:\n{stderr}",
                case.name
            );
        }
        if case.name == "call-duplicate-argument" {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            assert_eq!(
                source_row.rfind("value"),
                underline_row.find('^'),
                "duplicate argument underline does not select its second occurrence:\n{stderr}"
            );
        }
        if case.name == "struct-literal-duplicate-field" {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            assert_eq!(
                source_row.rfind("x"),
                underline_row.find('^'),
                "duplicate struct field underline does not select its second occurrence:\n{stderr}"
            );
        }
        let precise_fragment = match case.name {
            "recursive-alias" => Some("Second"),
            "repr-c-discriminant" => Some("2147483648"),
            "duplicate-type" => Some("Token"),
            "duplicate-field" => Some("x"),
            "duplicate-variant" | "duplicate-variant-global" => Some("Open"),
            "duplicate-parameter" => Some("value"),
            "duplicate-global" => Some("COUNT"),
            "unsafe-impl" => Some("Missing"),
            "unknown-local-type" => Some("Missing"),
            "immutable-assignment" => Some("value"),
            "non-array-index" => Some("value"),
            "non-array-assignment" => Some("value"),
            "non-struct-assignment" => Some("value"),
            "non-slice-len" => Some("value"),
            "non-slice-idx" => Some("value"),
            "non-array-slice-of" => Some("value"),
            "non-struct-get" => Some("value"),
            "non-enum-payload" => Some("value"),
            "unknown-get-field" => Some("missing"),
            "unknown-payload-variant" => Some("MissingVariant"),
            "unknown-match-variant" => Some("Missing"),
            "unknown-let-else-variant" => Some("Missing"),
            "duplicate-enum-match-pattern" => Some("Ready"),
            "duplicate-wildcard-match-pattern" => Some("_"),
            "out-of-range-match-integer" => Some("300"),
            "duplicate-match-integer" => Some("2"),
            "duplicate-character-match-pattern" => Some("#\\b"),
            "out-of-range-match-range" => Some("(#range 2 300)"),
            "reversed-match-range" => Some("2"),
            "non-reference-deref-set" => Some("value"),
            "thread-worker-missing" => Some("missing-worker"),
            "thread-worker-reference-result" => Some("(#ref u64)"),
            "thread-task-function-signature" => Some("Task"),
            "thread-task-type-alias" => Some("Task"),
            "thread-task-field" => Some("Task"),
            "duplicate-function" => Some("main"),
            "generator-capability" => Some("missing"),
            "generator-capability-signature" => Some("compare"),
            "generator-capability-duplicate-operation" => Some("compare"),
            "generator-capability-duplicate-type" => Some("u64"),
            "duplicate-generator" => Some("make"),
            "unsafe" => Some("VALUE"),
            "borrow" => Some("#set"),
            "linear" => Some("resource"),
            "nonconstant-static" => Some("(#call get-value (#fn-args))"),
            "call-arguments" => Some("other"),
            "call-missing-argument" => Some("#fn-args"),
            "struct-literal" => Some("((y 1u64))"),
            _ => None,
        };
        if let Some(fragment) = precise_fragment {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            let expected_column = if case.name == "duplicate-parameter" {
                source_row
                    .match_indices(fragment)
                    .nth(1)
                    .map(|(column, _)| column)
            } else if case.name == "generator-capability-duplicate-operation" {
                source_row
                    .match_indices(fragment)
                    .nth(1)
                    .map(|(column, _)| column)
            } else if matches!(
                case.name,
                "thread-worker-reference-result"
                    | "thread-task-type-alias"
                    | "duplicate-field"
                    | "duplicate-variant"
                    | "duplicate-function"
                    | "duplicate-enum-match-pattern"
                    | "duplicate-wildcard-match-pattern"
                    | "duplicate-match-integer"
                    | "duplicate-character-match-pattern"
            ) {
                source_row.rfind(fragment)
            } else {
                source_row.find(fragment)
            };
            assert_eq!(
                expected_column,
                underline_row.find('^'),
                "{} underline is not aligned under {fragment:?}:\n{stderr}",
                case.name
            );
        }
        if case.name == "codegen" {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            assert_eq!(
                source_row.find("Second"),
                underline_row.find('^'),
                "codegen underline is not aligned under the offending symbol:\n{stderr}"
            );
        }
        if case.name == "recursive-call" {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            assert_eq!(
                source_row.find("worker"),
                underline_row.find('^'),
                "recursive-call underline is not aligned under the recursive callee:\n{stderr}"
            );
        }
        if case.name == "generator-imported" {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            assert_eq!(
                source_row.find("(@fail)"),
                underline_row.find('^'),
                "imported generator underline is not aligned under its invocation:\n{stderr}"
            );
        }
        if case.name == "type" {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            assert_eq!(
                source_row.find("missing"),
                underline_row.find('^'),
                "nested type error is not aligned under its offending identifier:\n{stderr}"
            );
        }
        if case.name == "nonconstant-static" {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            assert_eq!(
                source_row.find("(#call"),
                underline_row.find('^'),
                "non-constant initializer underline is not aligned under its expression:\n{stderr}"
            );
        }
        if matches!(
            case.name,
            "duplicate-parameter"
                | "duplicate-field"
                | "duplicate-variant"
                | "duplicate-variant-global"
        ) {
            let source_row = stderr
                .lines()
                .find(|line| line.contains(case.offending_line))
                .unwrap();
            let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
            let duplicated_name = match case.name {
                "duplicate-parameter" => "value",
                "duplicate-field" => "x",
                _ => "Open",
            };
            let occurrence_index = usize::from(case.name != "duplicate-variant-global");
            let second_value = source_row
                .match_indices(duplicated_name)
                .nth(occurrence_index)
                .unwrap()
                .0;
            assert_eq!(
                Some(second_value),
                underline_row.find('^'),
                "duplicate declaration underline is not aligned under the second name:\n{stderr}"
            );
        }
        let _ = std::fs::remove_file(output);
    }
}
