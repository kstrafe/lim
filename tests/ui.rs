use std::process::Command;

#[test]
fn direct_file_dependency_cycles_reach_recursive_call_validation() {
    let entry = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/ui/cycle-a.lim");
    let source = std::fs::read_to_string(&entry).unwrap();
    let program = lim::parse_program_from_path(&source, &entry).unwrap();
    let error = lim::check_types(&program).unwrap_err();
    assert!(error.contains("recursive calls are not allowed"), "{error}");
    assert!(error.contains("cycle-b.lim::cycle"), "{error}");
}

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
            name: "kernel-opaque-value",
            diagnostic_code: "E4400",
            offending_line: "(#math-opaque invalid () #pt-nat (#pt-type 0))",
            line_number: 1,
        },
        Case {
            name: "kernel-nested-case-index",
            diagnostic_code: "E4400",
            offending_line: "(#math-definition tree-count",
            line_number: 4,
        },
        Case {
            name: "validation-wrong-object",
            diagnostic_code: "E4400",
            offending_line: "  (#proof-requires-validation main",
            line_number: 12,
        },
        Case {
            name: "proof-disproved",
            diagnostic_code: "E4400",
            offending_line: "  (#proof-eq 1u64 2u64))",
            line_number: 2,
        },
        Case {
            name: "call-graph-arity",
            diagnostic_code: "E4000",
            offending_line: "  (#let trace (#slice #char) (#call-graph 42u64))",
            line_number: 2,
        },
        Case {
            name: "call-graph-return-escape",
            diagnostic_code: "E4100",
            offending_line: "  (#return (#call-graph)))",
            line_number: 2,
        },
        Case {
            name: "enum-literal-unknown-variant",
            diagnostic_code: "E4000",
            offending_line: "  (#let value Outcome (#enum-literal missing 42u64))",
            line_number: 3,
        },
        Case {
            name: "enum-literal-payload-type",
            diagnostic_code: "E4000",
            offending_line: "  (#let value Outcome (#enum-literal Outcome.Success false))",
            line_number: 3,
        },
        Case {
            name: "enum-literal-extra-payload",
            diagnostic_code: "E4000",
            offending_line: "  (#let value Outcome (#enum-literal Outcome.Success 41u64 2u64))",
            line_number: 3,
        },
        Case {
            name: "let-else-fallthrough",
            diagnostic_code: "E4000",
            offending_line: "    (#else (#if true (#block (#return 0u64)) ())))",
            line_number: 4,
        },
        Case {
            name: "let-else-owner-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#let-else (Outcome.Success answer) 42u64",
            line_number: 3,
        },
        Case {
            name: "integer-match-coverage-gap",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value",
            line_number: 2,
        },
        Case {
            name: "guarded-boolean-match-not-exhaustive",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value",
            line_number: 2,
        },
        Case {
            name: "borrowed-case-requires-mut",
            diagnostic_code: "E4100",
            offending_line: "    (#case-ref-mut (Choice.Full value) (#deref value)))))",
            line_number: 4,
        },
        Case {
            name: "borrowed-case-mixed-modes",
            diagnostic_code: "E4000",
            offending_line: "    (#case-pin Choice.Empty 0u64))))",
            line_number: 5,
        },
        Case {
            name: "borrowed-case-owner-escape",
            diagnostic_code: "E4100",
            offending_line: "  (#return (#match (#borrow value)",
            line_number: 4,
        },
        Case {
            name: "pinned-case-requires-exclusive",
            diagnostic_code: "E4100",
            offending_line: "    (#case-pin-mut (Choice.Full value) (#deref value)))))",
            line_number: 4,
        },
        Case {
            name: "pinned-case-parent-reborrow",
            diagnostic_code: "E4100",
            offending_line: "        (#call touch (: input choice))",
            line_number: 9,
        },
        Case {
            name: "earlier-argument-write",
            diagnostic_code: "E4100",
            offending_line: "          (#deref-set (#get held value) 99u64)",
            line_number: 9,
        },
        Case {
            name: "reserved-generator-name",
            diagnostic_code: "E3000",
            offending_line: "(#gn #future-generator () ())",
            line_number: 1,
        },
        Case {
            name: "reserved-local-name",
            diagnostic_code: "E3000",
            offending_line: "  (#let #local #u64 1u64)",
            line_number: 2,
        },
        Case {
            name: "slice-borrow-bound-type",
            diagnostic_code: "E4000",
            offending_line: "  (#let view (#slice #u64) (#borrow-slice values 0u32 2usize))",
            line_number: 3,
        },
        Case {
            name: "slice-borrow-overlap",
            diagnostic_code: "E4100",
            offending_line: "  (#let right (#slice-mut #u64) (#borrow-slice-mut values 1usize 3usize))",
            line_number: 4,
        },
        Case {
            name: "slice-range-parent-use",
            diagnostic_code: "E4100",
            offending_line: "  (#let length #usize (#slice-mut-len parent))",
            line_number: 5,
        },
        Case {
            name: "println-missing-std",
            diagnostic_code: "E4000",
            offending_line: "  (#println 1u64)",
            line_number: 2,
        },
        Case {
            name: "println-arity",
            diagnostic_code: "E4000",
            offending_line: "  (#println)",
            line_number: 3,
        },
        Case {
            name: "println-type",
            diagnostic_code: "E4000",
            offending_line: "  (#println 1u64)",
            line_number: 3,
        },
        Case {
            name: "std-body",
            diagnostic_code: "E2000",
            offending_line: "  (#std)",
            line_number: 2,
        },
        Case {
            name: "string-borrow-mutation",
            diagnostic_code: "E4100",
            offending_line: "  (#call string-clear (: string (#borrow-mut text)))",
            line_number: 12,
        },
        Case {
            name: "call-builtin-name-type",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#call panic (: value false))))",
            line_number: 3,
        },
        Case {
            name: "gensym-reserved-source",
            diagnostic_code: "E2000",
            offending_line: "  (#let lim.gensym.fake #u64 42u64)",
            line_number: 2,
        },
        Case {
            name: "gensym-invalid-hint",
            diagnostic_code: "E3000",
            offending_line: "(#generate emit)",
            line_number: 2,
        },
        Case {
            name: "gensym-forged-symbol",
            diagnostic_code: "E3000",
            offending_line: "(#generate emit)",
            line_number: 2,
        },
        Case {
            name: "heap-pin-release",
            diagnostic_code: "E4100",
            offending_line: "  (#let pointer (#ptr-mut #u64) (#unsafe (#pin-release owner)))",
            line_number: 5,
        },
        Case {
            name: "stored-reference-projection-replacement",
            diagnostic_code: "E4100",
            offending_line: "  (#set values (#tuple (#tuple #u64 #u64) 99u64 100u64))",
            line_number: 9,
        },
        Case {
            name: "async-source-type-mismatch",
            diagnostic_code: "E4000",
            offending_line: "    (#let bad #u64 false)",
            line_number: 9,
        },
        Case {
            name: "async-unknown-loop-label",
            diagnostic_code: "E4000",
            offending_line: "      (#continue-to missing))",
            line_number: 9,
        },
        Case {
            name: "async-break-outside-loop",
            diagnostic_code: "E4000",
            offending_line: "    (#break)",
            line_number: 8,
        },
        Case {
            name: "fresh-aggregate-borrows",
            diagnostic_code: "E4100",
            offending_line: "  (#let pair Pair (#struct-literal Pair (: left (#borrow-mut owner) : right (#borrow-mut owner))))",
            line_number: 4,
        },
        Case {
            name: "pinned-copy-parent-release",
            diagnostic_code: "E4100",
            offending_line: "  (#drop parent)",
            line_number: 12,
        },
        Case {
            name: "call-returned-parent",
            diagnostic_code: "E4100",
            offending_line: "  (#call overwrite (: owner parent))",
            line_number: 10,
        },
        Case {
            name: "call-suspended-parent",
            diagnostic_code: "E4100",
            offending_line: "  (#let observed #u64 (#call observe (: target parent)))",
            line_number: 8,
        },
        Case {
            name: "exclusive-handle-duplicate",
            diagnostic_code: "E4200",
            offending_line: "  (#let output Pair (#struct-literal Pair (: right reference : left reference)))",
            line_number: 5,
        },
        Case {
            name: "callee-store-retained-borrow",
            diagnostic_code: "E4100",
            offending_line: "  (#set value 1u64)",
            line_number: 12,
        },
        Case {
            name: "callee-store-scope-escape",
            diagnostic_code: "E4100",
            offending_line: "    (#call replace (: target target : value (#borrow local)))",
            line_number: 11,
        },
        Case {
            name: "local-store-retained-borrow",
            diagnostic_code: "E4100",
            offending_line: "  (#set value 1u64)",
            line_number: 9,
        },
        Case {
            name: "external-store-local-reference",
            diagnostic_code: "E4100",
            offending_line: "  (#deref-set target temporary)",
            line_number: 5,
        },
        Case {
            name: "external-pin-store-local-reference",
            diagnostic_code: "E4100",
            offending_line: "  (#unsafe (#pin-write target temporary))",
            line_number: 5,
        },
        Case {
            name: "outer-storage-scope-escape",
            diagnostic_code: "E4100",
            offending_line: "    (#let temporary Holder (#struct-literal Holder (: view (#borrow local))))",
            line_number: 6,
        },
        Case {
            name: "local-pin-alias-read",
            diagnostic_code: "E4200",
            offending_line: "  (#let value #u64 (#get target number))",
            line_number: 8,
        },
        Case {
            name: "local-pin-read-twice",
            diagnostic_code: "E4200",
            offending_line: "  (#let second Resource (#unsafe (#pin-read target)))",
            line_number: 8,
        },
        Case {
            name: "local-pin-write-live",
            diagnostic_code: "E4200",
            offending_line: "  (#unsafe (#pin-write target (#struct-literal Resource (: number 2u64))))",
            line_number: 6,
        },
        Case {
            name: "pinned-loaded-reference-escape",
            diagnostic_code: "E4100",
            offending_line: "  (#return (#block",
            line_number: 3,
        },
        Case {
            name: "match-guard-consumes-preview",
            diagnostic_code: "E4200",
            offending_line: "      (#forget first)",
            line_number: 8,
        },
        Case {
            name: "anchor-only-linear-referent-consumption",
            diagnostic_code: "E4200",
            offending_line: "  (#forget (#deref target))",
            line_number: 7,
        },
        Case {
            name: "shared-linear-referent-consumption",
            diagnostic_code: "E4200",
            offending_line: "  (#forget (#deref reference))",
            line_number: 4,
        },
        Case {
            name: "pinned-linear-referent-move",
            diagnostic_code: "E4200",
            offending_line: "  (#let moved Resource (#deref reference))",
            line_number: 4,
        },
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
            offending_line: "(#alias missing = ./missing-module.lim::missing)",
            line_number: 1,
        },
        Case {
            name: "imported",
            diagnostic_code: "E4000",
            offending_line: "(#alias missing = ../missing-dependency.lim::missing)",
            line_number: 1,
        },
        Case {
            name: "cfg",
            diagnostic_code: "E4000",
            offending_line: "(#cfg-if (#cfg-is #platfrom linux) (#fn main () #u64 (#return 0u64)))",
            line_number: 1,
        },
        Case {
            name: "type",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#u64::add-wrap value missing))",
            line_number: 3,
        },
        Case {
            name: "mismatched-let",
            diagnostic_code: "E4000",
            offending_line: "  (#let total #u64 count)",
            line_number: 3,
        },
        Case {
            name: "return-type-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#return false)",
            line_number: 2,
        },
        Case {
            name: "tuple-element-type-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#tuple 1u64 2u64))",
            line_number: 2,
        },
        Case {
            name: "nested-tuple-element-type-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#tuple (#tuple 1u64) 2u64)))",
            line_number: 2,
        },
        Case {
            name: "array-element-type-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#array 1u64 false))",
            line_number: 2,
        },
        Case {
            name: "tuple-constructor-extra-element",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#tuple 1u64 true false))",
            line_number: 2,
        },
        Case {
            name: "array-constructor-missing-element",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#array 1u64))",
            line_number: 2,
        },
        Case {
            name: "nested-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#u64::add-wrap 1u64 false))",
            line_number: 2,
        },
        Case {
            name: "if-branch-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#if true 1u64 false))",
            line_number: 2,
        },
        Case {
            name: "match-branch-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match true (#case true 1u64) (#case false false)))",
            line_number: 2,
        },
        Case {
            name: "match-missing-case",
            diagnostic_code: "E2000",
            offending_line: "    (true 1u64)",
            line_number: 3,
        },
        Case {
            name: "operator-arity",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#u64::add-wrap 1u64))",
            line_number: 2,
        },
        Case {
            name: "nonboolean-if-condition",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#if 1u64 2u64 3u64))",
            line_number: 2,
        },
        Case {
            name: "noninteger-array-index",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#index values true))",
            line_number: 3,
        },
        Case {
            name: "out-of-range-shift-count",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#u8::shl 1u8 8))",
            line_number: 2,
        },
        Case {
            name: "unknown-function",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#call missing (:)))",
            line_number: 2,
        },
        Case {
            name: "top-level-mismatch",
            diagnostic_code: "E4000",
            offending_line: "(#let tOTAL #u64 true)",
            line_number: 1,
        },
        Case {
            name: "struct-literal",
            diagnostic_code: "E4000",
            offending_line: "  (#let point Point (#struct-literal Point ((y 1u64))))",
            line_number: 3,
        },
        Case {
            name: "struct-field-type-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#let pair Pair (#struct-literal Pair ((flag true) (count false))))",
            line_number: 3,
        },
        Case {
            name: "enum-payload-type-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#let value Payload (Payload.Pair (#tuple true false)))",
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
            offending_line: "  (#return (#call take (: other 42u64)))",
            line_number: 4,
        },
        Case {
            name: "call-argument-type-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#call consume (: first true : value false)))",
            line_number: 3,
        },
        Case {
            name: "call-missing-argument",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#call take (:)))",
            line_number: 4,
        },
        Case {
            name: "call-duplicate-argument",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#call take (: value 1u64 : value 2u64)))",
            line_number: 4,
        },
        Case {
            name: "type-as-constructor",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#get (Point 20u64 22u64) x)))",
            line_number: 3,
        },
        Case {
            name: "aggregate-layout-overflow",
            diagnostic_code: "E5000",
            offending_line:
                "(#fn main ((values (#array (#array #u64 18446744073709551615) 2))) () (#return ()))",
            line_number: 1,
        },
        Case {
            name: "array-repeat-linear",
            diagnostic_code: "E4200",
            offending_line: "  (#let values (#array Token 2) (#array-repeat (#struct-literal Token ((value 1u64)))))",
            line_number: 4,
        },
        Case {
            name: "atomic-invalid-load-order",
            diagnostic_code: "E4000",
            offending_line: "  (#atomic-load (#borrow counter) #memory-release)",
            line_number: 3,
        },
        Case {
            name: "local-name-type-error",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#call needs-value (: input flag)))",
            line_number: 4,
        },
        Case {
            name: "shadowing",
            diagnostic_code: "E4000",
            offending_line: "  (#let value #u64 2u64)",
            line_number: 3,
        },
        Case {
            name: "shadowing-destructure",
            diagnostic_code: "E4000",
            offending_line: "  (#let (#tuple value) (#tuple #u64) (#tuple 2u64))",
            line_number: 3,
        },
        Case {
            name: "shadowing-if-let",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#if-let (Maybe.Some value) maybe value value)))",
            line_number: 3,
        },
        Case {
            name: "shadowing-let-else",
            diagnostic_code: "E4000",
            offending_line: "  (#let-else (Maybe.Some value) Maybe maybe (#return 0u64))",
            line_number: 3,
        },
        Case {
            name: "pinned-reference-replacement",
            diagnostic_code: "E4000",
            offending_line: "  (#deref-set pinned 2u64)",
            line_number: 4,
        },
        Case {
            name: "pinned-reference-escape",
            diagnostic_code: "E4100",
            offending_line: "  (#return (#pin-borrow owner)))",
            line_number: 3,
        },
        Case {
            name: "pinned-self-reference-conflict",
            diagnostic_code: "E4100",
            offending_line: "  (#pin-set-field pinned view external)",
            line_number: 8,
        },
        Case {
            name: "call-self-loan-owner-mutation",
            diagnostic_code: "E4100",
            offending_line: "  (#let updated (#pin-ref-mut Link) (#call tick (: target running)))",
            line_number: 10,
        },
        Case {
            name: "call-self-loan-owner-borrow",
            diagnostic_code: "E4100",
            offending_line: "  (#let updated (#pin-ref-mut Link) (#call tick (: target running)))",
            line_number: 11,
        },
        Case {
            name: "reordered-named-argument-error",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#call combine (: right 1u64 : left 2u64)))",
            line_number: 3,
        },
        Case {
            name: "nested-case-pattern-error",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value (#case (Outer.Nested Inner.Ready) false) (#case Outer.Stop 0u64))))",
            line_number: 4,
        },
        Case {
            name: "positional-call",
            diagnostic_code: "E4000",
            offending_line: "  (#return (add 20u64 22u64)))",
            line_number: 4,
        },
        Case {
            name: "generic-function",
            diagnostic_code: "E2000",
            offending_line: "(#fn identity (T) ((value T)) T",
            line_number: 1,
        },
        Case {
            name: "generic-angle-call",
            diagnostic_code: "E4000",
            offending_line: "  (#return (identity<#u64> 42u64)))",
            line_number: 4,
        },
        Case {
            name: "borrow",
            diagnostic_code: "E4100",
            offending_line: "  (#set value 2u64)",
            line_number: 4,
        },
        Case {
            name: "overlapping-call-borrows",
            diagnostic_code: "E4100",
            offending_line: "  (#return (#call inspect (: left (#borrow-mut value) : right (#borrow value)))))",
            line_number: 5,
        },
        Case {
            name: "block-reference-escape",
            diagnostic_code: "E4100",
            offending_line: "  (#let escaped (#ref #u64) (#block (#let (#tuple local) (#tuple #u64) (#tuple 7u64)) (#borrow local)))",
            line_number: 2,
        },
        Case {
            name: "destructure-reference-escape",
            diagnostic_code: "E4100",
            offending_line: "  (#let (#tuple escaped) (#tuple (#ref #u64)) (#tuple (#block (#let (#tuple local) (#tuple #u64) (#tuple 7u64)) (#borrow local))))",
            line_number: 2,
        },
        Case {
            name: "call-reference-escape",
            diagnostic_code: "E4100",
            offending_line: "  (#call consume (: input (#block (#let local #u64 7u64) (#borrow local))))",
            line_number: 5,
        },
        Case {
            name: "match-reference-escape",
            diagnostic_code: "E4100",
            offending_line: "  (#return (#match holder (#case (Holder.Has view) view))))",
            line_number: 5,
        },
        Case {
            name: "borrow-conflict-field-name",
            diagnostic_code: "E4100",
            offending_line: "  (#return (#tuple (#get pair owner) owner)))",
            line_number: 6,
        },
        Case {
            name: "borrow-conflict-callee-name",
            diagnostic_code: "E4100",
            offending_line: "  (#return (#call owner (: arg owner)))",
            line_number: 5,
        },
        Case {
            name: "use-after-reference-release",
            diagnostic_code: "E4200",
            offending_line: "  (#return (#deref view)))",
            line_number: 5,
        },
        Case {
            name: "linear",
            diagnostic_code: "E4200",
            offending_line:
                "  (#let resource Resource (#struct-literal Resource ((value 1u64))))",
            line_number: 4,
        },
        Case {
            name: "linear-projection-replacement",
            diagnostic_code: "E4200",
            offending_line: "  (#set-field owner item (#struct-literal Resource ((number 2u64))))",
            line_number: 7,
        },
        Case {
            name: "linear-partial-parent",
            diagnostic_code: "E4200",
            offending_line: "  (#forget pair)",
            line_number: 8,
        },
        Case {
            name: "linear-copy-after-owner",
            diagnostic_code: "E4200",
            offending_line: "  (#return (#get pair other)))",
            line_number: 8,
        },
        Case {
            name: "opaque-token-constructor",
            diagnostic_code: "E4000",
            offending_line:
                "    (#struct-literal WakeToken4 ((slot 0usize) (generation 1u64))))",
            line_number: 4,
        },
        Case {
            name: "unsafe",
            diagnostic_code: "E4300",
            offending_line: "  (#return vALUE)",
            line_number: 3,
        },
        Case {
            name: "unsafe-external-call",
            diagnostic_code: "E4300",
            offending_line: "  (#let result #i32 (#unsafe-call external-value (: value 1i32)))",
            line_number: 3,
        },
        Case {
            name: "unsafe-external-reference-return",
            diagnostic_code: "E4300",
            offending_line: "  (#let reference (#ref-mut #u64) (#unsafe-call external-reference (:)))",
            line_number: 3,
        },
        Case {
            name: "unsafe-function-call",
            diagnostic_code: "E4300",
            offending_line: "  (#return (#unsafe-call answer (:))))",
            line_number: 3,
        },
        Case {
            name: "call-unsafe-function-spelling",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#unsafe (#call answer (:)))))",
            line_number: 3,
        },
        Case {
            name: "unsafe-call-safe-function-spelling",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#unsafe (#unsafe-call answer (:)))))",
            line_number: 3,
        },
        Case {
            name: "call-external-function-spelling",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#unsafe (#call external-value (:)))))",
            line_number: 3,
        },
        Case {
            name: "unsafe-pointer-op",
            diagnostic_code: "E4300",
            offending_line: "  (#return (#ptr-read pointer))",
            line_number: 2,
        },
        Case {
            name: "generator",
            diagnostic_code: "E3000",
            offending_line: "(#generate fail)",
            line_number: 2,
        },
        Case {
            name: "generator-imported",
            diagnostic_code: "E3000",
            offending_line: "(#generate fail)",
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
            offending_line: "(#capability order #u64 ((missing (#u64 #u64) #bool)))",
            line_number: 1,
        },
        Case {
            name: "generator-capability-signature",
            diagnostic_code: "E3000",
            offending_line: "(#capability order #u64 ((compare (#u64 #u64) #u64)))",
            line_number: 2,
        },
        Case {
            name: "generator-capability-duplicate-operation",
            diagnostic_code: "E3000",
            offending_line:
                "(#capability order #u64 ((compare (#u64 #u64) #bool) (compare (#u64 #u64) #bool)))",
            line_number: 2,
        },
        Case {
            name: "generator-capability-duplicate-type",
            diagnostic_code: "E3000",
            offending_line: "(#capability order #u64 ((compare (#u64 #u64) #bool)))",
            line_number: 3,
        },
        Case {
            name: "duplicate-generator",
            diagnostic_code: "E3000",
            offending_line: "(#gn make () (#gn-list))",
            line_number: 2,
        },
        Case {
            name: "duplicate-generator-parameter",
            diagnostic_code: "E3000",
            offending_line: "(#gn make (x x) (#gn-list))",
            line_number: 1,
        },
        Case {
            name: "codegen",
            diagnostic_code: "E5000",
            offending_line: "(#const first #u64 (#u64::add-wrap second 1u64))",
            line_number: 1,
        },
        Case {
            name: "nonconstant-static",
            diagnostic_code: "E5000",
            offending_line: "(#static vALUE #u64 (#call get-value (:)))",
            line_number: 2,
        },
        Case {
            name: "recursive-call",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#call worker (:)))",
            line_number: 2,
        },
        Case {
            name: "recursive-clone-hook",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#clone value)))",
            line_number: 3,
        },
        Case {
            name: "duplicate-type",
            diagnostic_code: "E4000",
            offending_line: "(#struct Token () ())",
            line_number: 2,
        },
        Case {
            name: "duplicate-parameter",
            diagnostic_code: "E4000",
            offending_line: "(#fn main ((value #u64) (value #u64)) #u64 (#return value))",
            line_number: 1,
        },
        Case {
            name: "duplicate-field",
            diagnostic_code: "E4000",
            offending_line: "(#struct Point () ((x #u64) (x #u64)))",
            line_number: 1,
        },
        Case {
            name: "duplicate-variant",
            diagnostic_code: "E2000",
            offending_line: "(#enum State () (State.Open State.Closed State.Open))",
            line_number: 1,
        },
        Case {
            name: "variant-wrong-owner",
            diagnostic_code: "E3000",
            offending_line: "(#enum State () (Other.Open State.Closed))",
            line_number: 1,
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
            offending_line: "(#let cOUNT #u64 2u64)",
            line_number: 2,
        },
        Case {
            name: "duplicate-function",
            diagnostic_code: "E3000",
            offending_line: "(#fn main () #u64 (#return 2u64))",
            line_number: 2,
        },
        Case {
            name: "repr-c-discriminant",
            diagnostic_code: "E4000",
            offending_line: "(#enum Code (#repr-c) ((Code.TooLarge 2147483648)))",
            line_number: 1,
        },
        Case {
            name: "unsafe-impl",
            diagnostic_code: "E4000",
            offending_line: "(#unsafe-impl #send missing)",
            line_number: 1,
        },
        Case {
            name: "thread-send",
            diagnostic_code: "E4000",
            offending_line: "(#fn worker ((pointer (#ptr #u64))) #u64 (#return 0u64))",
            line_number: 1,
        },
        Case {
            name: "thread-worker-ffi",
            diagnostic_code: "E5000",
            offending_line: "(#thread-task Work work)",
            line_number: 3,
        },
        Case {
            name: "thread-task-field",
            diagnostic_code: "E4000",
            offending_line: "(#struct Container () ((task Task)))",
            line_number: 3,
        },
        Case {
            name: "thread-worker-unknown-type",
            diagnostic_code: "E4000",
            offending_line: "(#fn worker ((argument missing)) #u64 (#return 1u64))",
            line_number: 4,
        },
        Case {
            name: "unknown-local-type",
            diagnostic_code: "E4000",
            offending_line: "(#fn main () #u64 (#let value missing 1u64) (#return 0u64))",
            line_number: 1,
        },
        Case {
            name: "destructure-type-mismatch",
            diagnostic_code: "E4000",
            offending_line: "  (#let (Point x) Point value)",
            line_number: 4,
        },
        Case {
            name: "immutable-assignment",
            diagnostic_code: "E4000",
            offending_line: "  (#set value 2u64)",
            line_number: 3,
        },
        Case {
            name: "immutable-mutable-borrow",
            diagnostic_code: "E4100",
            offending_line: "  (#let reference (#ref-mut #u64) (#borrow-mut value))",
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
            name: "variant-is-not-reference",
            diagnostic_code: "E4000",
            offending_line: "  (#variant-is value Choice.Ready)",
            line_number: 4,
        },
        Case {
            name: "variant-is-wrong-variant",
            diagnostic_code: "E4000",
            offending_line: "  (#variant-is (#borrow value) missing)",
            line_number: 4,
        },
        Case {
            name: "variant-is-borrowed-parent",
            diagnostic_code: "E4100",
            offending_line: "  (#variant-is parent Choice.Number)",
            line_number: 10,
        },
        Case {
            name: "unknown-match-variant",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value (#case missing 0u64) (#case State.Ready 1u64))))",
            line_number: 4,
        },
        Case {
            name: "non-exhaustive-match",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value (#case State.Ready 1u64))))",
            line_number: 4,
        },
        Case {
            name: "unknown-let-else-variant",
            diagnostic_code: "E4000",
            offending_line: "  (#let-else missing State value (#return 1u64))",
            line_number: 4,
        },
        Case {
            name: "async-let-else-await",
            diagnostic_code: "E4000",
            offending_line:
                "        (#await #u32 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 7u64)))))",
            line_number: 11,
        },
        Case {
            name: "duplicate-enum-match-pattern",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value (#case State.Ready 0u64) (#case State.Ready 1u64))))",
            line_number: 4,
        },
        Case {
            name: "enum-match-payload-arity",
            diagnostic_code: "E4000",
            offending_line:
                "  (#return (#match value (#case (Choice.One left right) 0u64) (#case Choice.Done 1u64))))",
            line_number: 4,
        },
        Case {
            name: "duplicate-wildcard-match-pattern",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match true (#case _ 0u64) (#case _ 1u64)))",
            line_number: 2,
        },
        Case {
            name: "out-of-range-match-integer",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value (#case 300 0u64) (#case _ 1u64)))",
            line_number: 3,
        },
        Case {
            name: "duplicate-match-integer",
            diagnostic_code: "E4000",
            offending_line:
                "  (#return (#match value (#case 2 0u64) (#case 2 1u64) (#case _ 0u64)))",
            line_number: 3,
        },
        Case {
            name: "duplicate-character-match-pattern",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match #\\a (#case #\\b 0u64) (#case #\\b 1u64)))",
            line_number: 2,
        },
        Case {
            name: "out-of-range-match-range",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value (#case (#range 2 300) 0u64) (#case _ 1u64)))",
            line_number: 3,
        },
        Case {
            name: "reversed-match-range",
            diagnostic_code: "E4000",
            offending_line: "  (#return (#match value (#case (#range 10 2) 0u64) (#case _ 1u64)))",
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
            offending_line: "(#fn worker ((value (#ref #u64))) (#ref #u64) (#return value))",
            line_number: 1,
        },
        Case {
            name: "thread-task-function-signature",
            diagnostic_code: "E4000",
            offending_line: "(#fn bad ((task Task)) #u64 (#return 0u64))",
            line_number: 3,
        },
        Case {
            name: "thread-task-type-alias",
            diagnostic_code: "E4000",
            offending_line: "(#type TaskAlias Task)",
            line_number: 3,
        },
    ];

    let mut failures = Vec::new();
    for case in cases {
        let result = std::panic::catch_unwind(|| {
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
                "generator-imported" => format!("{source_path}generator-imported/module.lim"),
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
            if case.name == "call-self-loan-owner-mutation" {
                assert!(
                    stderr.contains("cannot mutate or consume an owner while its stored internal reference is retained in 'tick'"),
                    "owner mutation did not report the retained internal reference:\n{stderr}"
                );
            }
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
            if case.name == "anchor-only-linear-referent-consumption" {
                assert!(stderr.contains("cannot prove storage identity"), "{stderr}");
                assert!(stderr.contains("lifetime-only anchor"), "{stderr}");
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
                source_row.find("missing"),
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
            "proof-disproved" => Some("(#proof-eq 1u64 2u64)"),
            "validation-wrong-object" => Some("(#proof-requires-validation main"),
            "reserved-generator-name" => Some("#future-generator"),
            "reserved-local-name" => Some("#local"),
            "println-missing-std" | "println-arity" => Some("#println"),
            "println-type" => Some("1u64"),
            "std-body" => Some("#std"),
            "heap-pin-release" => Some("(#pin-release owner)"),
            "async-source-type-mismatch" => Some("false"),
            "async-unknown-loop-label" => Some("missing"),
            "async-break-outside-loop" => Some("#break"),
            "fresh-aggregate-borrows" => Some("(#borrow-mut owner)"),
            "pinned-copy-parent-release" => Some("#drop"),
            "call-suspended-parent" => Some("parent"),
            "call-returned-parent" => Some("parent"),
            "exclusive-handle-duplicate" => Some("reference"),
            "callee-store-retained-borrow" => Some("#set"),
            "callee-store-scope-escape" => Some("(#borrow local)"),
            "local-store-retained-borrow" => Some("#set"),
            "external-store-local-reference" | "external-pin-store-local-reference" => Some("temporary"),
            "outer-storage-scope-escape" => Some("(#borrow local)"),
            "local-pin-alias-read" => Some("(#get target number)"),
            "local-pin-read-twice" => Some("(#pin-read target)"),
            "local-pin-write-live" => Some("(#pin-write target (#struct-literal Resource (: number 2u64)))"),
            "pinned-loaded-reference-escape" => Some("(#return (#block"),
            "lex" => Some("\"unterminated)"),
            "type" => Some("missing"),
            "return-type-mismatch" => Some("false"),
            "tuple-element-type-mismatch" => Some("2u64"),
            "nested-tuple-element-type-mismatch" => Some("2u64"),
            "array-element-type-mismatch" => Some("false"),
            "tuple-constructor-extra-element" => Some("false"),
            "array-constructor-missing-element" => Some("#array"),
            "import" => Some("./missing-module.lim::missing"),
            "imported" => Some("../missing-dependency.lim::missing"),
            "cfg" => Some("#platfrom"),
            "operator-arity" => Some("#u64::add-wrap"),
            "call-graph-arity" => Some("#call-graph"),
            "call-graph-return-escape" => Some("(#return (#call-graph))"),
            "unknown-function" => Some("missing"),
            "nonboolean-if-condition" => Some("(#if 1u64 2u64 3u64)"),
            "if-branch-mismatch" => Some("false"),
            "match-branch-mismatch" => Some("false"),
            "match-missing-case" => Some("(true 1u64)"),
            "noninteger-array-index" => Some("true"),
            "out-of-range-shift-count" => Some("8"),
            "recursive-alias" => Some("Second"),
            "repr-c-discriminant" => Some("2147483648"),
            "codegen" => Some("second"),
            "recursive-call" => Some("worker"),
            "recursive-clone-hook" => Some("#clone"),
            "duplicate-type" => Some("Token"),
            "duplicate-field" => Some("x"),
            "duplicate-variant" => Some("State.Open"),
            "variant-wrong-owner" => Some("Other.Open"),
            "duplicate-parameter" => Some("value"),
            "duplicate-global" => Some("cOUNT"),
            "unsafe-impl" => Some("missing"),
            "unknown-local-type" => Some("missing"),
            "destructure-type-mismatch" => Some("Point"),
            "immutable-assignment" => Some("value"),
            "immutable-mutable-borrow" => Some("value"),
            "non-array-index" => Some("value"),
            "non-array-assignment" => Some("value"),
            "non-struct-assignment" => Some("value"),
            "non-slice-len" => Some("value"),
            "non-slice-idx" => Some("value"),
            "non-array-slice-of" => Some("value"),
            "slice-borrow-bound-type" => Some("0u32"),
            "slice-borrow-overlap" => Some("#borrow-slice-mut"),
            "slice-range-parent-use" => Some("parent"),
            "non-struct-get" => Some("value"),
            "non-enum-payload" => Some("value"),
            "unknown-get-field" => Some("missing"),
            "unknown-payload-variant" => Some("MissingVariant"),
            "variant-is-not-reference" => Some("value"),
            "variant-is-wrong-variant" => Some("missing"),
            "variant-is-borrowed-parent" => Some("#variant-is"),
            "unknown-match-variant" => Some("missing"),
            "non-exhaustive-match" => Some("#match"),
            "integer-match-coverage-gap" | "guarded-boolean-match-not-exhaustive" => Some("#match"),
            "enum-literal-unknown-variant" => Some("missing"),
            "enum-literal-payload-type" => Some("false"),
            "enum-literal-extra-payload" => Some("2u64"),
            "let-else-fallthrough" => Some("#else"),
            "let-else-owner-mismatch" => Some("42u64"),
            "unknown-let-else-variant" => Some("missing"),
            "async-let-else-await" => Some("#u32"),
            "duplicate-enum-match-pattern" => Some("State.Ready"),
            "enum-match-payload-arity" => Some("Choice.One"),
            "duplicate-wildcard-match-pattern" => Some("_"),
            "out-of-range-match-integer" => Some("300"),
            "duplicate-match-integer" => Some("2"),
            "duplicate-character-match-pattern" => Some("#\\b"),
            "out-of-range-match-range" => Some("(#range 2 300)"),
            "reversed-match-range" => Some("2"),
            "non-reference-deref-set" => Some("value"),
            "anchor-only-linear-referent-consumption" => Some("(#forget (#deref target))"),
            "match-guard-consumes-preview" => Some("(#forget first)"),
            "shared-linear-referent-consumption" => Some("(#forget (#deref reference))"),
            "pinned-linear-referent-move" => Some("(#deref reference)"),
            "thread-worker-missing" => Some("missing-worker"),
            "thread-worker-ffi" => Some("(#thread-task Work work)"),
            "thread-send" => Some("(#ptr #u64)"),
            "thread-worker-reference-result" => Some("(#ref #u64)"),
            "thread-task-function-signature" => Some("Task"),
            "thread-task-type-alias" => Some("Task"),
            "thread-task-field" => Some("Task"),
            "duplicate-function" => Some("main"),
            "generator-capability" => Some("missing"),
            "generator-function-recursion" => Some("first"),
            "generator-capability-signature" => Some("compare"),
            "generator-capability-duplicate-operation" => Some("compare"),
            "generator-capability-duplicate-type" => {
                Some("(#capability order #u64 ((compare (#u64 #u64) #bool)))")
            }
            "duplicate-generator" => Some("make"),
            "duplicate-generator-parameter" => Some("x"),
            "unsafe" => Some("vALUE"),
            "unsafe-external-call" => Some("external-value"),
            "unsafe-external-reference-return" => Some("external-reference"),
            "unsafe-function-call" => Some("answer"),
            "call-unsafe-function-spelling" | "unsafe-call-safe-function-spelling" => Some("answer"),
            "call-external-function-spelling" => Some("external-value"),
            "unsafe-pointer-op" => Some("#ptr-read"),
            "borrow" => Some("#set"),
            "earlier-argument-write" => Some("(#deref-set (#get held value) 99u64)"),
            "string-borrow-mutation" => Some("#borrow-mut"),
            "stored-reference-projection-replacement" => Some("#set"),
            "overlapping-call-borrows" => Some("(#borrow value)"),
            "block-reference-escape" => Some("(#block (#let (#tuple local) (#tuple #u64) (#tuple 7u64)) (#borrow local))"),
            "destructure-reference-escape" => Some("(#tuple (#block (#let (#tuple local) (#tuple #u64) (#tuple 7u64)) (#borrow local)))"),
            "call-reference-escape" => Some("(#block (#let local #u64 7u64) (#borrow local))"),
            "match-reference-escape" => Some("(#return (#match holder (#case (Holder.Has view) view)))"),
            "borrow-conflict-field-name" => Some("owner"),
            "borrow-conflict-callee-name" => Some("owner"),
            "use-after-reference-release" => Some("view"),
            "linear" => Some("resource"),
            "linear-projection-replacement" => Some("(#set-field owner item (#struct-literal Resource ((number 2u64))))"),
            "linear-partial-parent" => Some("pair"),
            "linear-copy-after-owner" => Some("(#get pair other)"),
            "opaque-token-constructor" => Some("WakeToken4"),
            "generator" | "generator-imported" => Some("(#generate fail)"),
            "gensym-reserved-source" => Some("lim.gensym.fake"),
            "gensym-invalid-hint" | "gensym-forged-symbol" => Some("(#generate emit)"),
            "nonconstant-static" => Some("(#call get-value (:))"),
            "call-arguments" => Some("other"),
            "call-argument-type-mismatch" => Some("false"),
            "call-builtin-name-type" => Some("false"),
            "call-missing-argument" => Some("#call"),
            "type-as-constructor" => Some("Point"),
            "aggregate-layout-overflow" => Some("(#fn main ((values (#array (#array #u64 18446744073709551615) 2))) () (#return ()))"),
            "array-repeat-linear" => Some("(#array-repeat (#struct-literal Token ((value 1u64))))"),
            "atomic-invalid-load-order" => Some("(#atomic-load (#borrow counter) #memory-release)"),
            "local-name-type-error" => Some("flag"),
            "kernel-opaque-value" => Some(case.offending_line),
            "kernel-nested-case-index" => Some(&include_str!("ui/kernel-nested-case-index.lim").lines().nth(3).unwrap()[..80]),
            "shadowing" => Some("value"),
            "shadowing-destructure" => Some("value"),
            "shadowing-if-let" => Some("value"),
            "shadowing-let-else" => Some("value"),
            "pinned-reference-replacement" => Some("pinned"),
            "pinned-reference-escape" => Some("(#return (#pin-borrow owner))"),
            "pinned-self-reference-conflict" => Some("#pin-set-field"),
            "pinned-case-requires-exclusive" => Some("Choice.Full"),
            "borrowed-case-requires-mut" => Some("Choice.Full"),
            "borrowed-case-mixed-modes" => Some("Choice.Empty"),
            "borrowed-case-owner-escape" => Some("(#return (#match (#borrow value)"),
            "pinned-case-parent-reborrow" => Some("choice"),
            "call-self-loan-owner-mutation" => Some("running"),
            "call-self-loan-owner-borrow" => Some("running"),
            "reordered-named-argument-error" => Some("1u64"),
            "nested-case-pattern-error" => {
                Some("(#match value (#case (Outer.Nested Inner.Ready) false) (#case Outer.Stop 0u64))")
            }
            "positional-call" => Some("add"),
            "generic-function" => Some("(#fn"),
            "generic-angle-call" => Some("(identity<#u64> 42u64)"),
            "struct-literal" => Some("((y 1u64))"),
            "struct-field-type-mismatch" => Some("false"),
            "enum-payload-type-mismatch" => Some("false"),
            _ => None,
        };
            let has_custom_alignment = matches!(
                case.name,
                "parse"
                    | "mismatched-let"
                    | "nested-mismatch"
                    | "top-level-mismatch"
                    | "struct-literal-duplicate-field"
                    | "call-duplicate-argument"
                    | "thread-worker-unknown-type"
            );
            assert!(
                precise_fragment.is_some() || has_custom_alignment,
                "UI case {} must assert an exact source fragment or custom alignment",
                case.name
            );
            if let Some(fragment) = precise_fragment {
                let source_row = stderr
                    .lines()
                    .find(|line| line.contains(case.offending_line))
                    .unwrap();
                let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
                let expected_column = if case.name == "parse" {
                    Some(source_row.len())
                } else if case.name == "duplicate-parameter" {
                    source_row
                        .match_indices(fragment)
                        .nth(1)
                        .map(|(column, _)| column)
                } else if matches!(
                    case.name,
                    "generator-capability-duplicate-operation" | "duplicate-generator-parameter"
                ) {
                    source_row
                        .match_indices(fragment)
                        .nth(1)
                        .map(|(column, _)| column)
                } else if matches!(
                    case.name,
                    "destructure-type-mismatch"
                        | "out-of-range-shift-count"
                        | "match-branch-mismatch"
                        | "borrow-conflict-field-name"
                        | "borrow-conflict-callee-name"
                        | "fresh-aggregate-borrows"
                        | "local-name-type-error"
                ) {
                    source_row.rfind(fragment)
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
                let caret_width = underline_row
                    .chars()
                    .skip_while(|character| *character != '^')
                    .take_while(|character| *character == '^')
                    .count();
                let expected_width = if matches!(
                    case.name,
                    "aggregate-layout-overflow" | "destructure-reference-escape"
                ) {
                    fragment.chars().count().min(80)
                } else {
                    fragment.chars().count()
                };
                assert_eq!(
                caret_width,
                expected_width,
                "{} underline width does not match the declared source fragment {fragment:?}:\n{stderr}",
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
                    source_row.find("second"),
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
                    source_row.find("(#generate fail)"),
                    underline_row.find('^'),
                    "file dependency generator underline is not aligned under its invocation:\n{stderr}"
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
                "duplicate-parameter" | "duplicate-field" | "duplicate-variant"
            ) {
                let source_row = stderr
                    .lines()
                    .find(|line| line.contains(case.offending_line))
                    .unwrap();
                let underline_row = stderr.lines().find(|line| line.contains('^')).unwrap();
                let duplicated_name = match case.name {
                    "duplicate-parameter" => "value",
                    "duplicate-field" => "x",
                    _ => "State.Open",
                };
                let occurrence_index = 1;
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
        });
        if result.is_err() {
            failures.push(case.name);
        }
    }
    assert!(failures.is_empty(), "failed UI cases: {failures:?}");
}

#[test]
fn cached_generator_semantic_errors_show_generated_code_and_invocation() {
    let directory =
        std::env::temp_dir().join(format!("lim-ui-generated-span-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).unwrap();
    let source = include_str!("ui/generator-semantic-error.lim");
    let input = directory.join("input.lim");
    let output = directory.join("output.s");
    std::fs::write(&input, source).unwrap();
    for _ in 0..2 {
        let result = Command::new(env!("CARGO_BIN_EXE_lim"))
            .args([
                "--emit-asm",
                input.to_str().unwrap(),
                output.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert!(!result.status.success());
        let stderr = String::from_utf8(result.stderr).unwrap();
        assert!(stderr.contains("error[E4000]"), "{stderr}");
        assert!(stderr.contains("input.lim:2:"), "{stderr}");
        assert!(
            stderr.contains("(#fn generated () #u64 (#return false))"),
            "{stderr}"
        );
        assert!(
            stderr.contains("generated from this invocation"),
            "{stderr}"
        );
        assert!(stderr.contains("(#generate bad generated)"), "{stderr}");
        let generated_row = stderr
            .lines()
            .find(|line| line.contains("#fn generated"))
            .unwrap();
        let generated_underline = stderr
            .lines()
            .find(|line| line.contains("^^^^^ here"))
            .unwrap();
        assert_eq!(
            generated_row.split_once("| ").unwrap().1.find("false"),
            generated_underline
                .split_once("| ")
                .unwrap()
                .1
                .find("^^^^^")
        );
        let invocation_row = stderr
            .lines()
            .find(|line| line.contains("(#generate bad generated)"))
            .unwrap();
        let invocation_underline = stderr
            .lines()
            .find(|line| line.contains("generated from this invocation"))
            .unwrap();
        assert_eq!(
            invocation_row
                .split_once("| ")
                .unwrap()
                .1
                .find("(#generate bad generated)"),
            invocation_underline
                .split_once("| ")
                .unwrap()
                .1
                .find("^^^^^^^^^^^^^^^^")
        );
        assert!(!output.exists());
    }
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn builtin_generator_errors_show_generated_declaration_and_invocation() {
    let directory = std::env::temp_dir().join(format!(
        "lim-ui-builtin-generated-span-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).unwrap();
    let input = directory.join("input.lim");
    let output = directory.join("output.s");
    let source =
        "(#generate #optional (: type #u64 : name Maybe?))\n(#generate #optional (: type #u32 : name Maybe?))\n";
    std::fs::write(&input, source).unwrap();
    for _ in 0..2 {
        let result = Command::new(env!("CARGO_BIN_EXE_lim"))
            .args([
                "--emit-asm",
                input.to_str().unwrap(),
                output.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert!(!result.status.success());
        let stderr = String::from_utf8(result.stderr).unwrap();
        assert!(stderr.contains("duplicate type name 'Maybe?'"), "{stderr}");
        assert!(stderr.contains("#enum Maybe?"), "{stderr}");
        assert!(
            stderr.contains("generated from this invocation"),
            "{stderr}"
        );
        let invocation_row = stderr
            .lines()
            .find(|line| line.contains("(#generate #optional (: type #u32 : name Maybe?))"))
            .unwrap();
        let invocation_underline = stderr
            .lines()
            .find(|line| line.contains("generated from this invocation"))
            .unwrap();
        assert_eq!(
            invocation_row
                .split_once("| ")
                .unwrap()
                .1
                .find("(#generate #optional (: type #u32 : name Maybe?))"),
            invocation_underline
                .split_once("| ")
                .unwrap()
                .1
                .find("^^^^^^^^^^^^^^^^^^^^^^")
        );
        assert!(!output.exists());
    }
    std::fs::remove_dir_all(directory).unwrap();
}
