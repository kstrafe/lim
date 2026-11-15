use std::{fs, path::Path};

#[test]
fn all_examples_format_idempotently_without_changing_syntax() {
    fn visit(directory: &Path) {
        for entry in fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                if !path.file_name().unwrap().to_string_lossy().starts_with('.') {
                    visit(&path);
                }
            } else if path.extension().is_some_and(|extension| extension == "lim") {
                let source = fs::read_to_string(&path).unwrap();
                let formatted = lim::format_source(&source)
                    .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
                assert_eq!(
                    lim::format_source(&formatted).unwrap(),
                    formatted,
                    "non-idempotent formatting: {}",
                    path.display()
                );
                let expressions = |text: &str| {
                    lim::parse_source_unit(text)
                        .unwrap()
                        .into_iter()
                        .map(|expression| expression.expr)
                        .collect::<Vec<_>>()
                };
                assert_eq!(
                    expressions(&source),
                    expressions(&formatted),
                    "formatting changed syntax: {}",
                    path.display()
                );
            }
        }
    }
    visit(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .as_path(),
    );
}
