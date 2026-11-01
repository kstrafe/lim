use std::{fs, path::Path};

mod support;

fn write(base: &Path, path: &str, source: &str) {
    let path = base.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
}

#[test]
fn imported_mutual_members_and_absolute_family_names_resolve() {
    let scratch = support::Scratch::new("kernel-mutual-resolution");
    write(
        scratch.path(),
        "families.lim",
        r#"
          (#math-inductive tree () () (#mutual @tree @forest) (#pt-type 0)
            ((leaf ()) (node ((children (#pt-recur @forest ()))))))
          (#math-inductive forest () () (#mutual @tree @forest) (#pt-type 0)
            ((empty ()) (cons ((first (#pt-recur @tree ()))
                               (rest (#pt-recur @forest ()))))))
        "#,
    );
    let source = r#"
      (#alias tree-alias = ./families.lim::tree)
      (#alias forest-alias = ./families.lim::forest)
      (#theorem imported_member
        (#universes)
        (#parameters (#parameter value (#pt-use @tree-alias ())))
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
      (#theorem imported_sibling
        (#universes)
        (#parameters (#parameter value (#pt-use @forest-alias ())))
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#;
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim"))
        .expect("imported mutual aliases and @ references resolve");
    let resolved = format!("{:#?}", program.items);
    assert!(resolved.contains("families.lim::tree"), "{resolved}");
    assert!(resolved.contains("families.lim::forest"), "{resolved}");
    lim::check_types(&program).unwrap_or_else(|error| panic!("{error}\n{source}"));
}
