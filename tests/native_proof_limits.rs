use lim::{LeanExportLimits, LeanFoundationPolicy, NativeProofLimits, ProofBudget};
use std::io::{self, BufRead, Read, Write};

const IDENTITY: &str = include_str!("fixtures/lean_export/identity.ndjson");
const TARGET: &str = "Audit.identity.theorem";

struct PanicReader;
impl Read for PanicReader {
    fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
        panic!("reader must not be touched")
    }
}
impl BufRead for PanicReader {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        panic!("reader must not be touched")
    }
    fn consume(&mut self, _: usize) {}
}

fn selected_raw() -> LeanExportLimits {
    LeanExportLimits {
        max_bytes: 1 << 30,
        max_names: 10_000,
        max_name_bytes: 32 << 20,
        max_levels: 100,
        max_expressions: 100,
        max_declarations: 10_000,
        max_dependencies: 10_000,
        max_dependency_bytes: 32 << 20,
        max_payload_bytes: 32 << 20,
        max_scratch_bytes: 128 * 1024 * 1024,
    }
}

fn native() -> NativeProofLimits {
    NativeProofLimits::default()
}

#[test]
fn invalid_native_profile_fails_before_input_is_read() {
    let invalid = NativeProofLimits {
        max_bytes: 0,
        ..native()
    };
    assert!(invalid.validate().is_err());
    let error = lim::translate_lean_export_with_profiles(
        PanicReader,
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        LeanExportLimits::default(),
        invalid,
    )
    .unwrap_err();
    assert!(!error.message.is_empty());
}

#[test]
fn native_limits_validate_and_each_limit_is_enforced() {
    assert_eq!(native().validate().unwrap(), native());
    let boundaries = [
        (
            NativeProofLimits {
                max_bytes: 1,
                ..native()
            },
            "byte",
        ),
        (
            NativeProofLimits {
                max_declarations: 1,
                ..native()
            },
            "declaration",
        ),
        (
            NativeProofLimits {
                max_directory_bytes: 1,
                ..native()
            },
            "directory",
        ),
        (
            NativeProofLimits {
                max_render_nodes: 1,
                ..native()
            },
            "node",
        ),
        (
            NativeProofLimits {
                max_correspondence_nodes: 1,
                ..native()
            },
            "correspondence",
        ),
        (
            NativeProofLimits {
                max_correspondence_bytes: 1,
                ..native()
            },
            "correspondence",
        ),
    ];
    for (limits, _hint) in boundaries {
        assert!(lim::translate_lean_export_with_profiles(
            IDENTITY.as_bytes(),
            TARGET,
            LeanFoundationPolicy::Constructive,
            ProofBudget::default(),
            LeanExportLimits::default(),
            limits,
        )
        .is_err());
    }
}

fn many_aliases(count: usize, long_names: bool) -> String {
    let mut rows: Vec<String> = IDENTITY.lines().map(str::to_owned).collect();
    let theorem = rows.pop().unwrap();
    for i in 0..count {
        let id = i + 5;
        let name = if long_names {
            format!("alias{i}_{}", "x".repeat(1_800))
        } else {
            format!("alias{i}")
        };
        rows.push(format!(
            "{{\"str\":{{\"pre\":0,\"str\":\"{name}\"}},\"in\":{id}}}"
        ));
    }
    let mut input = rows.join("\n");
    input.push('\n');
    for i in 0..count {
        let id = i + 5;
        input.push_str(&format!("{{\"thm\":{{\"name\":{id},\"levelParams\":[],\"type\":12,\"value\":19,\"all\":[{id}]}}}}\n"));
    }
    input.push_str(&theorem);
    input.push('\n');
    input
}

#[test]
fn raised_native_and_raw_profiles_kernel_check_large_proof_and_file_artifact() {
    let input = many_aliases(5_000, true);
    let raw = selected_raw();
    let native_limits = NativeProofLimits {
        max_bytes: 64 << 20,
        max_declarations: 6_000,
        max_directory_bytes: 32 << 20,
        max_render_nodes: 1_000_000,
        max_correspondence_nodes: 1_000_000,
        max_correspondence_bytes: 64 << 20,
        max_scratch_bytes: 128 * 1024 * 1024,
    };
    let budget = ProofBudget::new(100_000_000, 1 << 30, 1 << 30).unwrap();
    let default_error = lim::translate_lean_export_with_profiles(
        input.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget,
        raw,
        NativeProofLimits::default(),
    )
    .unwrap_err();
    assert!(
        default_error.message.to_lowercase().contains("declaration"),
        "{default_error}"
    );

    let receipt = lim::translate_lean_export_receipt_with_profiles(
        input.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget,
        raw,
        native_limits,
    )
    .unwrap();
    assert_eq!(receipt.receipt.native_limits(), Some(native_limits));
    let mut receipt_json = Vec::new();
    receipt.receipt.write_json(&mut receipt_json).unwrap();
    assert!(String::from_utf8_lossy(&receipt_json).contains("native_proof_limits"));
    let materialized = lim::translate_lean_export_with_profiles(
        input.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget,
        raw,
        native_limits,
    )
    .unwrap();
    assert!(
        receipt.source.len() == materialized.source.len()
            && receipt.source.as_bytes() == materialized.source.as_bytes()
    );
    let scratch =
        std::env::temp_dir().join(format!("lim-native-proof-limits-{}", std::process::id()));
    std::fs::create_dir_all(&scratch).unwrap();
    let artifact = scratch.join("identity.lim");
    let staged = lim::translate_lean_export_artifact_with_profiles(
        input.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget,
        raw,
        native_limits,
    )
    .unwrap();
    assert!(staged.source_len() > 8 * 1024 * 1024);
    assert_eq!(staged.receipt.declaration_count(), 5_002);
    {
        let mut file = std::fs::File::create(&artifact).unwrap();
        staged.write_source(&mut file).unwrap();
    }
    let checked =
        lim::check_proof_artifact_from_path(&artifact, budget, native_limits, &staged.target)
            .unwrap();
    assert_eq!(staged.target, materialized.target);
    assert_eq!(checked.name, staged.target);

    let late_start = staged.source_len();
    let mut file = std::fs::OpenOptions::new()
        .append(true)
        .open(&artifact)
        .unwrap();
    file.write_all(
        b"\n(#theorem late-bad (#universes) (#parameters)\n\
          (#statement (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero)))\n\
          (#proof (#pt-refl #pt-nat #pt-zero)))\n",
    )
    .unwrap();
    drop(file);
    let error =
        lim::check_proof_artifact_from_path(&artifact, budget, native_limits, &staged.target)
            .unwrap_err();
    let diagnostic = error
        .diagnostic()
        .expect("late proof failure has a diagnostic");
    assert!(
        diagnostic.message.contains("type mismatch"),
        "{diagnostic:?}"
    );
    assert!(!diagnostic.message.contains("resource"), "{diagnostic:?}");
    assert!(
        diagnostic.span.unwrap().start >= late_start,
        "{diagnostic:?}"
    );
    assert!(
        diagnostic.source_text.is_none(),
        "full proof source was retained"
    );
    std::fs::remove_dir_all(scratch).unwrap();
}

#[test]
fn proof_type_mismatch_and_non_closed_sources_are_rejected() {
    let translated = lim::translate_lean_export_with_profiles(
        IDENTITY.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        LeanExportLimits::default(),
        native(),
    )
    .unwrap();
    let nodes = lim::parse(&translated.source).unwrap();
    let target = nodes.iter().find(|node| matches!(&node.expr,
        lim::Expr::List(parts) if matches!(parts.get(1), Some(lim::Expr::Symbol(name)) if name == &translated.target)
    )).unwrap();
    let span = target.children.last().unwrap().children[1].span;
    let altered = format!(
        "{}#pt-zero{}",
        &translated.source[..span.start],
        &translated.source[span.end..]
    );
    assert!(lim::check_types(&lim::parse_program(&altered).unwrap())
        .unwrap_err()
        .contains("type mismatch"));

    let scratch = std::env::temp_dir().join(format!("lim-native-altered-{}", std::process::id()));
    std::fs::create_dir_all(&scratch).unwrap();
    let altered_path = scratch.join("altered.lim");
    std::fs::write(&altered_path, &altered).unwrap();
    let error = lim::check_proof_artifact_from_path(
        &altered_path,
        ProofBudget::default(),
        native(),
        &translated.target,
    )
    .unwrap_err();
    assert!(error.to_string().contains("type mismatch"), "{error}");
    std::fs::remove_dir_all(&scratch).unwrap();

    for source in [
        format!(
            "{}\n(#fn forged () #u64 (#return 0u64))\n",
            translated.source
        ),
        format!(
            "{}\n(#theorem late-bad (#universes) (#parameters)\n\
             (#statement (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero)))\n\
             (#proof (#pt-refl #pt-nat #pt-zero)))\n",
            translated.source
        ),
        format!("{}\n#import \"missing.lim\"\n", translated.source),
    ] {
        let scratch =
            std::env::temp_dir().join(format!("lim-native-strict-{}", std::process::id()));
        std::fs::create_dir_all(&scratch).unwrap();
        let path = scratch.join("altered.lim");
        std::fs::write(&path, source).unwrap();
        assert!(lim::check_proof_artifact_from_path(
            &path,
            ProofBudget::default(),
            native(),
            &translated.target
        )
        .is_err());
        std::fs::remove_dir_all(scratch).unwrap();
    }
}
