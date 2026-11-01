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
