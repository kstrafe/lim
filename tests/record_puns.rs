#[test]
fn bare_identifier_entries_expand_to_ordinary_named_pairs() {
    let punned = lim::parse("print { value; }").unwrap();
    let explicit = lim::parse("print { value = value; }").unwrap();
    assert_eq!(punned[0].expr, explicit[0].expr);

    let mixed = lim::parse("{ first; second = value; third; }").unwrap();
    let explicit = lim::parse("{ first = first; second = value; third = third; }").unwrap();
    assert_eq!(mixed[0].expr, explicit[0].expr);

    assert_eq!(
        lim::parse("{ value::; }").unwrap()[0].expr,
        lim::parse("{ value:: = value::; }").unwrap()[0].expr
    );
}

#[test]
fn pun_label_and_value_share_the_identifier_source_span() {
    let source = "{ value; }";
    let record = lim::parse(source).unwrap().remove(0);
    let pair = &record.children[0];
    let label = &pair.children[0];
    let value = &pair.children[1];

    assert_eq!(label.expr, value.expr);
    assert_eq!(label.span, value.span);
    assert_eq!(&source[label.span.start..label.span.end], "value");
    assert_eq!(&source[pair.span.start..pair.span.end], "value;");
}

#[test]
fn malformed_and_missing_terminator_entries_remain_errors() {
    for source in [
        "{ value }",
        "{ value =; }",
        "{ = value; }",
        "{ value:; }",
        "{ value other; }",
    ] {
        assert!(lim::parse(source).is_err(), "accepted {source}");
    }
}

#[test]
fn pun_calls_typecheck_and_duplicate_arguments_still_fail() {
    let valid = r#"
#fn identity {
  #params = ((input #u64));
  #returns = #u64;
  #body = (#return input;);
}
#fn main {
  #params = ((input #u64));
  #returns = #u64;
  #body = (#return identity { input; };);
}
"#;
    lim::check_types(&lim::parse_program(valid).unwrap()).unwrap();

    let duplicate = r#"
#fn take {
  #params = ((value #u64));
  #returns = #u64;
  #body = (#return value;);
}
#fn main {
  #params = ((value #u64));
  #returns = #u64;
  #body = (#return take { value; value = 1u64; };);
}
"#;
    let error = lim::parse_program(duplicate)
        .and_then(|program| lim::check_types(&program))
        .unwrap_err();
    assert!(
        error.contains("provides parameter 'value' more than once"),
        "{error}"
    );
}

#[test]
fn pun_values_do_not_implicitly_borrow() {
    let source = r#"
#fn take {
  #params = ((value (#ref #u64)));
  #returns = ();
  #body = (#return (););
}
#fn main {
  #params = ((value #u64));
  #returns = ();
  #body = (take { value; }; #return (););
}
"#;
    assert!(
        lim::parse_program(source)
            .and_then(|program| lim::check_types(&program))
            .is_err()
    );
    let explicit = source.replace("take { value; }", "take { value = (#borrow value); }");
    lim::check_types(&lim::parse_program(&explicit).unwrap()).unwrap();
}

#[test]
fn formatting_keeps_the_pun_spelling_and_reader_tree() {
    let source = "print { value; flags = 0u32; }";
    let formatted = lim::format_syntax(source).unwrap();
    assert!(formatted.contains("value;"), "{formatted}");
    assert_eq!(
        lim::parse(source).unwrap()[0].expr,
        lim::parse(&formatted).unwrap()[0].expr
    );
    assert_eq!(lim::format_syntax(&formatted).unwrap(), formatted);
}
