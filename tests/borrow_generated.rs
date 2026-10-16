mod support;

use lim::{CompileConfig, DiagnosticCode, TargetDescription};

fn compile(source: &str, name: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new(name);
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("case.lim"),
        &CompileConfig::default(),
        &scratch.path().join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
}

fn expect_accept(name: &str, source: &str) {
    compile(source, name)
        .unwrap_or_else(|error| panic!("{name}: unexpected {:?}: {}", error.code, error.message));
}

fn expect_borrow(name: &str, source: &str) {
    let error = match compile(source, name) {
        Err(error) => error,
        Ok(_) => panic!("{name}: violating program compiled"),
    };
    assert_eq!(
        error.code,
        DiagnosticCode::Borrow,
        "{name}: {}",
        error.message
    );
}

// Construct a chain of nested wrappers around a two-field leaf. `depth` is
// finite and explicit so every generated case is stable and reproducible.
fn nested_prefix(depth: usize) -> (String, String, String, String) {
    let mut declarations = String::from("(#struct Leaf () (: left #u64 : right #u64))\n");
    let mut ty = "Leaf".to_owned();
    let mut path = "owner".to_owned();
    let mut literal = "(#struct-literal Leaf (: left 1u64 : right 2u64))".to_owned();
    for level in 0..depth {
        let next = format!("Nest{level}");
        declarations.push_str(&format!(
            "(#struct {next} () (: child {ty} : spare #u64))\n"
        ));
        path = format!("(#get {path} child)");
        literal = format!("(#struct-literal {next} (: child {literal} : spare 3u64))");
        ty = next;
    }
    (declarations, ty, path, literal)
}

#[test]
fn generated_nested_field_projection_matrix() {
    for depth in 0..=3 {
        let (decls, ty, leaf, literal) = nested_prefix(depth);
        let left = format!("(#get {leaf} left)");
        let right = format!("(#get {leaf} right)");
        let base = format!("{decls}(#fn main () #u64\n  (#let-mut owner {ty} {literal})\n");
        let disjoint = format!(
            "{base}  (#let a (#ref-mut #u64) (#borrow-mut {left}))\n  (#let b (#ref-mut #u64) (#borrow-mut {right}))\n  (#deref-set a 4u64) (#deref-set b 5u64)\n  (#drop a) (#drop b) (#return 0u64))"
        );
        let overlap = format!(
            "{base}  (#let a (#ref-mut #u64) (#borrow-mut {left}))\n  (#let b (#ref-mut #u64) (#borrow-mut {left}))\n  (#deref-set a 4u64) (#deref-set b 5u64)\n  (#drop a) (#drop b) (#return 0u64))"
        );
        expect_accept(&format!("nested-{depth}-disjoint"), &disjoint);
        expect_borrow(&format!("nested-{depth}-overlap"), &overlap);

        let shared_controls = format!(
            "{decls}(#fn main () #u64\n  (#let owner {ty} {literal})\n  (#let a (#ref #u64) (#borrow {left}))\n  (#let b (#ref #u64) (#borrow {left}))\n  (#let result #u64 (#u64.+.wrap (#deref a) (#deref b)))\n  (#drop a) (#drop b) (#return result))"
        );
        let shared_conflict = format!(
            "{decls}(#fn main () #u64\n  (#let-mut owner {ty} {literal})\n  (#let a (#ref #u64) (#borrow {left}))\n  (#let b (#ref-mut #u64) (#borrow-mut {left}))\n  (#drop a) (#drop b) (#return 0u64))"
        );
        expect_accept(&format!("nested-{depth}-shared-shared"), &shared_controls);
        expect_borrow(&format!("nested-{depth}-shared-write"), &shared_conflict);
    }
}

#[test]
fn generated_helper_returned_reference_matrix() {
    for field in ["left", "right"] {
        let other = if field == "left" { "right" } else { "left" };
        for depth in 0..=2 {
            let (decls, ty, leaf, literal) = nested_prefix(depth);
            let selected = format!("(#get {leaf} {field})");
            let sibling = format!("(#get {leaf} {other})");
            let helper_selected = selected.replace("owner", "target");
            let helper = format!(
                "{decls}(#fn pick (: target (#ref-mut {ty})) (#ref-mut #u64)\n  (#return (#borrow-mut {helper_selected})))\n"
            );
            let common = format!(
                "{helper}(#fn main () #u64\n  (#let-mut owner {ty} {literal})\n  (#let view (#ref-mut #u64) (#call pick (: target (#borrow-mut owner))))\n"
            );
            let accepted = format!(
                "{common}  (#let sibling (#ref-mut #u64) (#borrow-mut {sibling}))\n  (#deref-set sibling 7u64) (#deref-set view 8u64)\n  (#drop sibling) (#drop view) (#return 0u64))"
            );
            let rejected = format!(
                "{common}  (#let sibling (#ref-mut #u64) (#borrow-mut {selected}))\n  (#deref-set sibling 7u64) (#deref-set view 8u64)\n  (#drop sibling) (#drop view) (#return 0u64))"
            );
            expect_accept(&format!("helper-{field}-depth-{depth}-sibling"), &accepted);
            expect_borrow(&format!("helper-{field}-depth-{depth}-selected"), &rejected);
        }
    }
}

#[test]
fn generated_branch_selected_origin_matrix() {
    for (ordering, first, second) in [("forward", "a", "b"), ("reverse", "b", "a")] {
        let source = format!(
            "(#fn select (: choose #bool : a (#ref #u64) : b (#ref #u64)) (#ref #u64)\n  (#return (#if choose {first} {second})))\n\
             (#fn main () #u64\n  (#let-mut a #u64 1u64) (#let-mut b #u64 2u64)\n\
             (#let view (#ref #u64) (#call select (: choose true : a (#borrow a) : b (#borrow b))))\n\
             (#set {first} 7u64)\n  (#drop view) (#return 0u64))"
        );
        expect_borrow(&format!("branch-{ordering}-selected-origin"), &source);

        let control = format!(
            "(#fn select (: choose #bool : a (#ref #u64) : b (#ref #u64)) (#ref #u64)\n  (#return (#if choose {first} {second})))\n\
             (#fn main () #u64\n  (#let-mut a #u64 1u64) (#let-mut b #u64 2u64)\n\
             (#let view (#ref #u64) (#call select (: choose true : a (#borrow a) : b (#borrow b))))\n\
             (#let answer #u64 (#deref view))\n  (#drop view) (#return answer))"
        );
        expect_accept(&format!("branch-{ordering}-other-origin-control"), &control);
    }
}
