use lim::{Expr, SpannedExpr};

#[test]
fn deep_parsed_lists_keep_expr_and_spanned_children_in_step() {
    let source = "(root (branch (leaf 7)))";
    let forms = lim::parse(source).unwrap();
    let root = &forms[0];
    let branch = &root.children[1];
    let inner = &branch.children[1];

    assert_eq!(
        root.expr,
        Expr::List(
            root.children
                .iter()
                .map(|child| child.expr.clone())
                .collect()
        )
    );
    assert_eq!(
        branch.expr,
        Expr::List(
            branch
                .children
                .iter()
                .map(|child| child.expr.clone())
                .collect()
        )
    );
    assert_eq!(
        inner.expr,
        Expr::List(
            inner
                .children
                .iter()
                .map(|child| child.expr.clone())
                .collect()
        )
    );
    assert_eq!(inner.children[1].expr, Expr::Integer(7));
}

#[test]
fn mutation_detaches_cloned_trees_and_preserves_raw_parent_expr() {
    let source = "(outer (inner value))";
    let parsed = lim::parse(source).unwrap();
    let original = parsed[0].clone();
    let mut clone = original.clone();
    let detached = original.clone();
    let old_nested_span = original.children[1].children[1].span;

    clone.children[1].children[1].span.source_id = 17;
    clone.children[1].children[1].expr = Expr::Symbol("changed".into());
    assert_eq!(clone.children[1].children[1].span.source_id, 17);
    assert_eq!(original.children[1].children[1].span, old_nested_span);
    assert_eq!(detached.children[1].children[1].span, old_nested_span);
    assert_eq!(
        original.children[1].children[1].expr,
        Expr::Symbol("value".into())
    );
    assert_eq!(
        detached.children[1].children[1].expr,
        Expr::Symbol("value".into())
    );

    // Expr remains the raw parsed value: changing source children does not rewrite it.
    assert_eq!(clone.expr, original.expr);
    assert_ne!(clone.children[1].expr, clone.children[1].children[1].expr);
    assert_eq!(parsed[0], original);

    let consumed = Vec::from(clone.children.clone());
    let rebuilt = SpannedExpr {
        expr: clone.expr.clone(),
        span: clone.span,
        children: consumed.into_iter().collect(),
    };
    assert_eq!(rebuilt.children, clone.children);
}

#[test]
fn reader_and_group_children_keep_exact_source_spans() {
    let source = "'alpha `beta ,gamma ,@delta (: first x : second ($ name)) ($ shorthand)";
    let forms = lim::parse(source).unwrap();
    let check = |node: &SpannedExpr, expected: &str| {
        assert_eq!(&source[node.span.start..node.span.end], expected);
        assert_eq!(node.span.source_id, 0);
    };

    for (node, text, expected) in [
        (
            &forms[0],
            "'alpha",
            Expr::Quote(Box::new(Expr::Symbol("alpha".into()))),
        ),
        (
            &forms[1],
            "`beta",
            Expr::QuasiQuote(Box::new(Expr::Symbol("beta".into()))),
        ),
        (
            &forms[2],
            ",gamma",
            Expr::Unquote(Box::new(Expr::Symbol("gamma".into()))),
        ),
        (
            &forms[3],
            ",@delta",
            Expr::UnquoteSplicing(Box::new(Expr::Symbol("delta".into()))),
        ),
    ] {
        check(node, text);
        let child_text = if text.starts_with(",@") {
            &text[2..]
        } else {
            &text[1..]
        };
        check(&node.children[0], child_text);
        assert_eq!(node.expr, expected);
    }

    let grouped = &forms[4];
    check(grouped, "(: first x : second ($ name))");
    for child in &grouped.children {
        assert_eq!(child.span.source_id, 0);
        check(child, &source[child.span.start..child.span.end]);
    }
    let shorthand = &forms[5];
    check(shorthand, "($ shorthand)");
    assert_eq!(shorthand.children.len(), 2);
    for child in &shorthand.children {
        check(child, "shorthand");
    }
}

#[test]
fn public_type_mismatch_span_and_rendering_point_at_rhs() {
    let source = "(#fn main () #bool (#return 23u64))";
    let path = std::env::temp_dir().join(format!("lim-source-children-{}.lim", std::process::id()));
    let compile = || {
        lim::compile_source_to_assembly(
            source,
            &path,
            &lim::CompileConfig::default(),
            &std::env::temp_dir().join("lim-source-children-cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
    };
    let error = compile().unwrap_err();
    assert!(
        error.message.contains("has type U64, expected Bool"),
        "{}",
        error.message
    );
    let span = error.span.expect("type mismatch carries source span");
    assert_eq!(&source[span.start..span.end], "23u64");
    assert_eq!(span.source_id, 0);
    let rendered = lim::render_diagnostic(&error, source, "input.lim");
    let source_line = rendered
        .lines()
        .find(|line| line.contains("#return 23u64"))
        .unwrap();
    let underline = rendered.lines().find(|line| line.contains('^')).unwrap();
    assert_eq!(source_line.find("23u64"), underline.find('^'), "{rendered}");

    let parsed = lim::parse(source).unwrap();
    let mut parsed_clone = parsed[0].clone();
    parsed_clone.children[4].children[1].expr = Expr::Symbol("mutated".into());
    let after = compile().unwrap_err();
    assert_eq!(after.message, error.message);
    assert_eq!(after.span, error.span);
    assert_eq!(
        parsed[0].children[4].children[1].expr,
        Expr::List(vec![
            Expr::Symbol("#literal".into()),
            Expr::Symbol("#u64".into()),
            Expr::Integer(23),
        ])
    );
}
