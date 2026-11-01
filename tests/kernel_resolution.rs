use std::{fs, path::Path};

mod support;

fn write(base: &Path, path: &str, source: &str) {
    let path = base.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
}

#[test]
fn proof_names_resolve_inside_constructor_and_induction_data_lists() {
    let scratch = support::Scratch::new("kernel-resolution-lists");
    write(
        scratch.path(),
        "math.lim",
        "(#math-definition natural () (#pt-type 0) #pt-nat)\n\
         (#math-inductive box () () (#pt-type 0) ((pack ())))",
    );

    let source = r#"
      (#alias natural-alias = ./math.lim::natural)
      (#alias box-alias = ./math.lim::box)
      (#math-definition claim () (#pt-type 0)
        (#pt-app
          (#pt-construct box-alias () ((#pt-use natural-alias ())) pack ((#pt-use natural-alias ())))
          (#pt-induct box-alias () ((#pt-use natural-alias ()))
            (#pt-use natural-alias ()) ((#pt-use natural-alias ()) (#pt-use natural-alias ())) (#pt-use natural-alias ()))))
    "#;
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    let (proof_name, proof) = program
        .items
        .iter()
        .find_map(|item| match item {
            lim::Item::Proof { name, proposition } if name.ends_with("::claim") => {
                Some((name, proposition))
            }
            _ => None,
        })
        .expect("top-level math declaration keeps its qualified source identity");
    assert!(proof_name.contains("main.lim::"), "{proof_name}");
    let resolved = format!("{proof:?}");
    assert_eq!(
        resolved.matches("math.lim::natural").count(),
        7,
        "{resolved}"
    );
    assert_eq!(resolved.matches("math.lim::box").count(), 2, "{resolved}");
}

#[test]
fn pt_let_file_resolution_preserves_type_value_body_scopes() {
    let scratch = support::Scratch::new("kernel-let-resolution-scope");
    write(
        scratch.path(),
        "math.lim",
        "(#math-definition global-x () (#pt-type 0) #pt-nat)",
    );
    let source = r#"
      (#alias x = ./math.lim::global-x)
      (#math-definition scoped () (#pt-use x ())
        (#pt-let (#parameter x (#pt-use x ()))
          (#pt-app (#pt-lambda ((temporary (#pt-use x ()))) temporary) #pt-zero)
          x))
    "#;
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    let resolved = format!("{:#?}", program.items);
    assert_eq!(
        resolved.matches("math.lim::global-x").count(),
        4,
        "{resolved}"
    );
    assert_eq!(resolved.matches("\"x\"").count(), 2, "{resolved}");
    lim::check_types(&program).unwrap();
}

#[test]
fn absolute_names_in_universe_positions_cannot_capture_a_local_universe() {
    let scratch = support::Scratch::new("kernel-universe-qualification");
    for level in ["@u", "(#pt-level-imax v @u)", "(#pt-level-max @u v)"] {
        let source = format!(
            r#"
          (#math-definition u () (#pt-sort 1) #pt-nat)
          (#math-definition editing (u v)
            (#pt-sort (#pt-level-succ (#pt-level-imax v u)))
            (#pt-sort {level}))
        "#
        );
        let program =
            lim::parse_program_from_path(&source, &scratch.path().join("main.lim")).unwrap();
        let error =
            lim::check_types(&program).expect_err("an absolute name became a local universe");
        assert!(error.contains("universe"), "{error}");
    }
}

#[test]
fn global_proof_references_still_accept_explicit_absolute_names() {
    let scratch = support::Scratch::new("kernel-global-qualification");
    let source = "(#math-definition natural () (#pt-sort 1) #pt-nat)\n\
      (#math-definition alias () (#pt-sort 1) (#pt-use @natural ()))";
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    lim::check_types(&program).unwrap();
}

#[test]
fn mathematical_looking_generator_inputs_still_check_private_absolute_names() {
    let scratch = support::Scratch::new("kernel-input-qualification");
    write(
        scratch.path(),
        "library/lib.lim",
        r#"
      (#export make)
      (#gn make (input) '())
      (#fn secret () #u64 (#return 0u64))
    "#,
    );
    let source = r#"
      (#alias make = ./library/lib.lim::make)
      (#generate make (#pt-sort @./library/lib.lim::secret))
      (#fn main () #u64 (#return 42u64))
    "#;
    let error = lim::parse_program_from_path(source, &scratch.path().join("main.lim"))
        .expect_err("mathematical-looking input hid a private generator argument");
    assert!(error.contains("private"), "{error}");
}
