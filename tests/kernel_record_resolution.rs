use std::{fs, path::Path};

mod support;

fn write(base: &Path, path: &str, source: &str) {
    let path = base.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
}

fn check_from_path(source: &str, path: &Path) {
    let program = lim::parse_program_from_path(source, path)
        .unwrap_or_else(|error| panic!("record resolution fixture must parse: {error}\n{source}"));
    lim::check_types(&program).unwrap_or_else(|error| {
        panic!("record resolution fixture must typecheck: {error}\n{source}")
    });
}

const IMPORTED_RECORD: &str = r#"
  (#math-inductive record-one-nat () () (#pt-type 0)
    ((pack ((value #pt-nat)))))
"#;

const ZERO_PROJECTION_THEOREMS: &str = r#"
  (#theorem projected-zero (#universes) (#parameters)
    (#statement (#pt-eq #pt-nat
      (#pt-project FAMILY 0
        (#pt-construct FAMILY () () pack (#pt-zero)))
      #pt-zero))
    (#proof (#pt-refl #pt-nat #pt-zero)))
"#;

#[test]
fn projection_family_resolves_import_alias_and_direct_file_path() {
    let scratch = support::Scratch::new("kernel-record-family-resolution");
    write(scratch.path(), "records.lim", IMPORTED_RECORD);
    let source = format!(
        "(#alias record_alias = ./records.lim::record-one-nat)\n{}\n{}",
        ZERO_PROJECTION_THEOREMS.replace("FAMILY", "record_alias"),
        ZERO_PROJECTION_THEOREMS
            .replace("projected-zero", "projected-zero-direct")
            .replace("FAMILY", "./records.lim::record-one-nat")
    );
    check_from_path(&source, &scratch.path().join("main.lim"));
}

#[test]
fn absolute_family_name_does_not_capture_same_named_local_subject() {
    let scratch = support::Scratch::new("kernel-record-family-absolute");
    let source = r#"
      (#math-inductive record-one-nat () () (#pt-type 0)
        ((pack ((value #pt-nat)))))
      (#theorem absolute-family-local-subject
        (#universes) (#parameters
          (#parameter record-one-nat (#pt-use @record-one-nat ())))
        (#statement (#pt-eq #pt-nat
          (#pt-project @record-one-nat 0 record-one-nat)
          (#pt-project @record-one-nat 0 record-one-nat)))
        (#proof (#pt-refl #pt-nat
          (#pt-project @record-one-nat 0 record-one-nat))))
    "#;
    check_from_path(source, &scratch.path().join("main.lim"));
}

#[test]
fn generated_record_projection_typechecks_on_cold_and_warm_parse() {
    let scratch = support::Scratch::new("kernel-record-generator-resolution");
    let path = scratch.path().join("main.lim");
    let source = r#"
      (#gn emit-record () `((#math-inductive generated-record () () (#pt-type 0)
        ((pack ((value #pt-nat)))))))
      (#generate emit-record)
      (#theorem generated-projected-zero (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-project generated-record 0
            (#pt-construct generated-record () () pack (#pt-zero)))
          #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#;
    check_from_path(source, &path);
    check_from_path(source, &path);
}
