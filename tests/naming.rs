mod support;
use lim::{check_types, generate_assembly, parse_program};

fn check(source: &str) -> Result<(), String> {
    check_types(&parse_program(source)?)
}

#[test]
fn names_identify_types_functions_and_variants() {
    let source = "#enum Work::Poll () ((Work::Poll.Ready #u64) Work::Poll.Pending)
#fn Work::poll {
  #params = ((value #u64));
  #returns = Work::Poll;
  #body = (
          (#return (#enum-literal Work::Poll.Ready (#u64::add-wrap value 2u64)))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#return (#match (#call Work::poll ((value 40u64)))
            (#case (Work::Poll.Ready result) result)
            (#case Work::Poll.Pending 0u64)))\n  );\n}\n";
    let program = parse_program(source).unwrap();
    check_types(&program).unwrap();
    generate_assembly(&program).unwrap();
}

#[test]
fn invalid_declaration_spellings_are_rejected() {
    for source in [
        "#struct thing () ()\n", "#type thing #u64\n",
        "#enum thing () (thing.Ready)\n", "#distributed-enum thing ()\n",
        "#struct Work::frame () ()\n", "#struct Work.Frame () ()\n",
        "#generate #optional ((type #u64) (name thing))\n",
        "#fn Main {\n  #params = ();\n  #returns = ();\n  #body = ( (#return ())\n  );\n}\n", "#fn work::poll {\n  #params = ();\n  #returns = ();\n  #body = ( (#return ())\n  );\n}\n",
        "#fn main {\n  #params = ((Value #u64));\n  #returns = #u64;\n  #body = ( (#return Value)\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let Value #u64 42u64) (#return Value)\n  );\n}\n",
        "#struct Thing () ((Field #u64))\n",
        "#enum State () (Ready)\n", "#enum State () (State.ready)\n",
        "#enum State () (Other.Ready)\n", "#enum State () (State::Ready)\n",
        "#enum State () ((State.Ready #u64))
#fn main {
  #params = ((state State));
  #returns = #u64;
  #body = ( (#return (#match state (#case (State.Ready Value) Value)))\n  );\n}\n",
    ] {
        let error = parse_program(source).unwrap_err();
        assert!(error.contains("identifier '"), "{source}: {error}");
    }
}

#[test]
fn numeric_words_preserve_all_operation_families() {
    for scalar in [
        "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
    ] {
        for operation in [
            "add-wrap",
            "add-saturate",
            "sub-wrap",
            "sub-saturate",
            "mul-wrap",
            "mul-saturate",
            "div-wrap",
            "div-saturate",
            "rem-wrap",
            "rem-saturate",
            "bit-and",
            "bit-or",
            "bit-xor",
            "shl",
            "shr",
        ] {
            check(&format!(
                "#fn main {{\n  #params = ();\n  #returns = #{scalar};\n  #body = ( (#return (#{scalar}::{operation} 6{scalar} 2{scalar}))\n  );\n}}\n"
            ))
            .unwrap();
        }
        for operation in ["eq", "ne", "lt", "le", "gt", "ge"] {
            check(&format!(
                "#fn main {{\n  #params = ();\n  #returns = #bool;\n  #body = ( (#return (#{scalar}::{operation} 6{scalar} 2{scalar}))\n  );\n}}\n"
            ))
            .unwrap();
        }
    }
    check("#fn main {\n  #params = ();\n  #returns = #bool;\n  #body = ( (#return (#bool::and (#bool::not false) (#bool::or false true)))\n  );\n}\n")
        .unwrap();
    check("#fn main {\n  #params = ();\n  #returns = #f64;\n  #body = ( (#return (#f64::add 40.0f64 2.0f64))\n  );\n}\n").unwrap();
}

#[test]
fn old_operator_spellings_and_implicit_overflow_are_rejected() {
    for operation in [
        "#u64.+.wrap",
        "#u64::+::wrap",
        "#u64::add",
        "#u64::add-trap",
    ] {
        assert!(
            check(&format!(
                "#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return ({operation} 40u64 2u64))\n  );\n}}\n"
            ))
            .is_err(),
            "{operation}"
        );
    }
}

#[test]
fn generators_construct_variants_without_overloading_symbol_append() {
    check(
        "#gn make (name)
        `((#enum ,name () ((,(#gn-variant name \"Ready\") #u64)))
          (#fn ,(#gn-symbol-append name \"create\") ((value #u64)) ,name
            (#return (#enum-literal ,(#gn-variant name \"Ready\") value))))
#generate make State
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return (#match (#call State::create ((value 42u64)))
          (#case (State.Ready value) value)))\n  );\n}\n",
    )
    .unwrap();
    assert!(parse_program("#gn bad () `((#struct lowercase () ()))\n#generate bad\n").is_err());
}

#[test]
fn compiler_issued_private_type_symbols_remain_hygienic() {
    check(
        "#gn-fn private-type (name) `((#struct ,name () ((value #u64))))
#gn make () (#gn-call private-type (#gn-gensym \"Private\"))
#generate make
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return 42u64)\n  );\n}\n",
    )
    .unwrap();
}

#[test]
fn naming_diagnostics_underline_the_identifier() {
    let scratch = support::Scratch::new("naming-diagnostics");
    for (source, offending) in [
        ("#struct wrong () ()\n", "wrong"),
        ("#enum State () (Other.Ready)\n", "Other.Ready"),
        ("#fn main {\n  #params = ((Wrong #u64));\n  #returns = #u64;\n  #body = ( (#return Wrong)\n  );\n}\n", "Wrong"),
        (
            "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#u64.+.wrap 1u64 2u64))\n  );\n}\n",
            "#u64.+.wrap",
        ),
    ] {
        let error = lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        let span = error.span.expect("naming errors have a source span");
        assert_eq!(&source[span.start..span.end], offending, "{error:?}");
    }
}
