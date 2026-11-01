mod support;

use lim::lsp::{
    self,
    json::{self, Json},
};
use std::{collections::HashMap, io::Cursor};

fn quoted(s: &str) -> String {
    Json::String(s.into()).render()
}

#[test]
fn logical_foundation_references_have_no_user_definition_target() {
    run(
        r#"
      (#math-definition pt-foundation-propext () #pt-nat #pt-zero)
      (#math-definition pt-foundation-choice () #pt-nat #pt-zero)
      (#math-definition pt-foundation-quot-sound () #pt-nat #pt-zero)
      (#math-definition use-foundations () #pt-nat
        (#pt-app (#pt-use [[propext|#pt-foundation-propext]] ())
          (#pt-app (#pt-use [[choice|#pt-foundation-choice]] (u))
            (#pt-use [[quot-sound|#pt-foundation-quot-sound]] (u)))))
    "#,
        &[("propext", &[]), ("choice", &[]), ("quot-sound", &[])],
    );
}

#[test]
fn mutual_headers_recursive_targets_and_constructor_offsets_have_explicit_roles() {
    run(
        r#"
      (#math-inductive [[left|left]] (u) ((A (#pt-type u)))
        (#mutual [[header-left|left]] [[header-right|right]])
        (#indices (#parameter generic-index #pt-nat)) (#pt-type u)
        ((wrap (([[field|k]] #pt-nat)
                 (child (#pt-recur [[target|right]] ([[child-index|k]]))))
          ([[result-index|k]]))))
      (#math-inductive [[right|right]] (u) ((A (#pt-type u)))
        (#mutual left right) (#indices (#parameter generic-index #pt-nat)) (#pt-type u)
        (([[label|leaf]] () (#pt-zero))))
      (#math-definition use (u) (#pt-type u)
        (#pt-construct right (u) (#pt-nat) [[label-use|leaf]] ()))
      (#math-definition outside () #pt-nat (#pt-recur right ([[outside|k]])))
    "#,
        &[
            ("header-left", &["left"]),
            ("header-right", &["right"]),
            ("target", &["right"]),
            ("child-index", &["field"]),
            ("result-index", &["field"]),
            ("label-use", &["label"]),
            ("outside", &[]),
        ],
    );
}

#[test]
fn mutual_eliminator_uses_global_case_keys_and_lexical_term_scopes() {
    run(
        r#"
      (#math-inductive [[left|left]] () () (#mutual left right) (#pt-type 0) ((make ())))
      (#math-inductive [[right|right]] () () (#mutual left right) (#pt-type 0) ((end ())))
      (#math-definition fold () (#pt-pi ((value (#pt-use left ()))) #pt-nat)
        (#pt-lambda (([[outer|value]] (#pt-use left ())))
          (#pt-mutual-induct [[selected|left]] () () (#indices)
            (([[case-left|left]] (#pt-lambda (([[binder|right]] (#pt-use left ())))
                (#pt-pi ((unused (#pt-eq (#pt-use left ()) [[body|right]] right))) #pt-nat))
               ((#pt-lambda ((proof (#pt-eq (#pt-use left ()) (#pt-construct left () () make ()) (#pt-construct left () () make ())))) #pt-zero)))
             ([[case-right|right]] (#pt-lambda ((subject (#pt-use right ()))) #pt-nat) (#pt-zero)))
            [[subject|value]])))
      (#math-definition after () #pt-nat (#pt-recur right ([[leak|value]])))
    "#,
        &[
            ("selected", &["left"]),
            ("case-left", &["left"]),
            ("case-right", &["right"]),
            ("body", &["binder"]),
            ("subject", &["outer"]),
            ("leak", &[]),
        ],
    );
}

#[test]
fn generated_mutual_members_resolve_through_checked_expansion() {
    run(
        r#"
      (#gn emit () `(
        (#math-inductive first () () (#mutual first second) (#pt-type 0) ((make ())))
        (#math-inductive second () () (#mutual first second) (#pt-type 0) ((end ())))))
      (#generate emit)
      (#math-definition use () #pt-nat
        (#pt-mutual-induct [[selected|first]] () () (#indices)
          (([[case|first]] (#pt-lambda ((x (#pt-use first ()))) #pt-nat) (#pt-zero))
           (second (#pt-lambda ((x (#pt-use second ()))) #pt-nat) (#pt-zero)))
          (#pt-construct first () () make ())))
    "#,
        &[
            ("selected", &["generated:first"]),
            ("case", &["generated:first"]),
        ],
    );
}

#[test]
fn malformed_mutual_roles_have_no_global_spelling_fallback() {
    for value in [
        "(#pt-recur [[query|left]] #pt-zero)",
        "(#pt-recur [[query|left]] () extra)",
        "(#pt-mutual-induct [[query|left]] () () (#indices) ((left #pt-zero ())) #pt-zero)",
        "(#pt-mutual-induct left () () (#indices) (([[query|left]] #pt-zero #pt-zero) (right #pt-zero ())) #pt-zero)",
    ] {
        let source=format!(r#"
          (#math-inductive left () () (#mutual left right) (#pt-type 0) ((make ())))
          (#math-inductive right () () (#mutual left right) (#pt-type 0) ((end ())))
          (#math-definition bad () #pt-nat {value})"#);
        run(&source,&[("query",&[])]);
    }
    run(
        r#"
      (#math-inductive left () () (#mutual left [[query|left]]) (#pt-type 0) ((make ())))
    "#,
        &[("query", &[])],
    );
}

#[test]
fn sort_and_imax_operands_navigate_only_their_universe_binders() {
    run(
        r#"
      (#math-definition u () #pt-nat #pt-zero)
      (#math-definition missing () #pt-nat #pt-zero)
      (#math-definition levels ([[universe|u]] [[other|v]])
        (#[[sort-keyword|pt-sort]]
          (#[[imax-keyword|pt-level-imax]] [[left|u]] (#pt-level-succ [[right|v]])))
        (#pt-lambda (([[term|u]] #pt-nat))
          (#pt-pair (#pt-sort (#pt-level-imax [[level-under-term|u]] [[zero|0]]))
            [[term-use|u]] (#pt-sort (#pt-level-max v (#pt-level-imax [[nested-left|u]] [[nested-right|v]]))))))
      (#math-definition unknown () (#pt-sort (#pt-level-imax [[unknown|missing]] 0)) #pt-zero)
    "#,
        &[
            ("sort-keyword", &[]),
            ("imax-keyword", &[]),
            ("left", &["universe"]),
            ("right", &["other"]),
            ("level-under-term", &["universe"]),
            ("zero", &[]),
            ("term-use", &["term"]),
            ("nested-left", &["universe"]),
            ("nested-right", &["other"]),
            ("unknown", &[]),
        ],
    );
}

#[test]
fn quotient_terms_separate_universe_roles_and_resolve_every_term_operand() {
    run(
        r#"
      (#math-definition [[definition|quotient-use]] ([[universe|u]] [[target-universe|v]])
        (#pt-type 0)
        (#pt-lambda (([[type|alpha]] #pt-nat) ([[relation|rel]] #pt-nat)
                     ([[target-type|beta]] #pt-nat) ([[function|f]] #pt-nat)
                     ([[respect|respects]] #pt-nat) ([[value|value]] #pt-nat)
                     ([[subject|subject]] #pt-nat) ([[motive|motive]] #pt-nat)
                     ([[constructor-proof|constructor]] #pt-nat))
          (#pt-pair #pt-nat
            (#pt-quot [[quot-level|u]] [[quot-type|alpha]] [[quot-relation|rel]])
            (#pt-pair #pt-nat
              (#pt-quot-make [[make-level|u]] [[make-type|alpha]] [[make-relation|rel]] [[make-value|value]])
              (#pt-pair #pt-nat
                (#pt-quot-lift ([[source-level|u]] [[lift-target-level|v]]) [[lift-type|alpha]] [[lift-relation|rel]] [[lift-target-type|beta]] [[lift-function|f]] [[lift-respect|respects]] [[lift-subject|subject]])
                (#pt-quot-induct [[induct-level|u]] [[induct-type|alpha]] [[induct-relation|rel]] [[induct-motive|motive]] [[induct-constructor|constructor]] [[induct-subject|subject]]))))))
      (#math-definition namesake () #pt-nat #pt-zero)
    "#,
        &[
            ("definition", &["definition"]),
            ("universe", &["universe"]),
            ("target-universe", &["target-universe"]),
            ("quot-level", &["universe"]),
            ("make-level", &["universe"]),
            ("source-level", &["universe"]),
            ("lift-target-level", &["target-universe"]),
            ("induct-level", &["universe"]),
            ("quot-type", &["type"]),
            ("quot-relation", &["relation"]),
            ("make-type", &["type"]),
            ("make-relation", &["relation"]),
            ("make-value", &["value"]),
            ("lift-type", &["type"]),
            ("lift-relation", &["relation"]),
            ("lift-target-type", &["target-type"]),
            ("lift-function", &["function"]),
            ("lift-respect", &["respect"]),
            ("lift-subject", &["subject"]),
            ("induct-type", &["type"]),
            ("induct-relation", &["relation"]),
            ("induct-motive", &["motive"]),
            ("induct-constructor", &["constructor-proof"]),
            ("induct-subject", &["subject"]),
        ],
    );
}

#[test]
fn malformed_quotient_arities_pair_layouts_and_keyword_clicks_have_no_fallback() {
    for expression in [
        "(#[[query|pt-quot]] 0)",
        "(#pt-quot [[query|u]] alpha)",
        "(#pt-quot-make 0 alpha [[query|relation]])",
        "(#pt-quot-make 0 alpha relation value [[query|extra]])",
        "(#pt-quot-lift ([[query|u]]) alpha relation beta f respects subject)",
        "(#pt-quot-lift ([[query|u]] v extra) alpha relation beta f respects subject)",
        "(#pt-quot-lift (u [[query|v]]) alpha relation beta f respects subject extra)",
        "(#pt-quot-induct 0 alpha relation motive [[query|proof]])",
        "(#pt-quot-induct 0 alpha relation motive proof [[query|subject]] extra)",
        "(#pt-quot-induct [[query|@u]] alpha relation motive proof subject)",
    ] {
        run(
            &format!("(#math-definition u () #pt-nat #pt-zero) (#math-definition v () #pt-nat #pt-zero) (#math-definition alpha () #pt-nat #pt-zero) (#math-definition editing (u v) (#pt-type 0) (#pt-lambda ((relation #pt-nat) (beta #pt-nat) (f #pt-nat) (respects #pt-nat) (subject #pt-nat) (motive #pt-nat) (proof #pt-nat) (value #pt-nat)) {expression}))"),
            &[("query", &[])],
        );
    }
}

#[test]
fn pt_let_has_scoped_binder_and_outer_type_value_roles() {
    run(
        r#"
      (#math-definition global () (#pt-type 0) #pt-nat)
      (#math-definition scoped () (#pt-pi ((A (#pt-type 0)) (y A)) A)
        (#pt-lambda (([[outer-type|A]] (#pt-type 0)) ([[outer|y]] A))
          (#pt-let (#[[binder-keyword|parameter]] [[binder|x]] [[type-use|A]])
            [[value-use|y]]
            (#pt-app (#pt-lambda ((temporary A)) [[body-use|x]]) [[nested|x]]))))
      (#math-definition after () (#pt-type 0) [[after-let|x]])
    "#,
        &[
            ("binder-keyword", &[]),
            ("binder", &["binder"]),
            ("type-use", &["outer-type"]),
            ("value-use", &["outer"]),
            ("body-use", &["binder"]),
            ("nested", &["binder"]),
            ("after-let", &[]),
        ],
    );
}

#[test]
fn malformed_pt_let_and_explicit_pt_use_fail_closed() {
    for term in [
        "(#pt-let (#parameter [[query|name]] #pt-nat) #pt-zero)",
        "(#pt-let (#parameter name #pt-nat) [[query|name]] #pt-zero #pt-zero extra)",
        "(#pt-let (#other [[query|name]] #pt-nat) #pt-zero #pt-zero)",
    ] {
        let source = format!(
            "(#math-definition name () (#pt-type 0) #pt-nat) (#math-definition check () (#pt-type 0) {term})"
        );
        lim::parse(&source).expect("malformed kernel form must still have balanced S-expressions");
        run(&source, &[("query", &[])]);
    }
    run(
        "(#math-definition [[x|x]] () (#pt-type 0) #pt-nat) (#math-definition check () (#pt-type 0) (#pt-let (#parameter [[binder|x]] #pt-nat) #pt-zero (#pt-use [[explicit|x]] ())))",
        &[("binder", &["binder"]), ("explicit", &["x"])],
    );
}

#[test]
fn pt_let_accepts_underscore_and_rejects_invalid_or_shadowing_binders() {
    run(
        "(#math-definition underscore () (#pt-type 0) (#pt-let (#parameter [[binder|_]] #pt-nat) #pt-zero [[use|_]]))",
        &[("binder", &["binder"]), ("use", &["binder"])],
    );

    for expression in [
        "(#pt-let (#parameter [[query|a/b]] #pt-nat) #pt-zero #pt-zero)",
        "(#pt-let (#parameter [[query|a::b]] #pt-nat) #pt-zero #pt-zero)",
        "(#pt-let (#parameter [[query|7name]] #pt-nat) #pt-zero #pt-zero)",
        "(#pt-lambda ((x #pt-nat)) (#pt-let (#parameter [[query|x]] #pt-nat) #pt-zero x))",
        "(#pt-let (#parameter [[query|u]] #pt-nat) #pt-zero #pt-zero)",
    ] {
        let source = format!(
            "(#math-definition u () (#pt-type 0) #pt-nat) (#math-definition check (u) (#pt-type 0) {expression})"
        );
        lim::parse(&source).expect("invalid binder fixture must have balanced S-expressions");
        run(&source, &[("query", &[])]);
    }
}

#[test]
fn theorem_sort_parameters_use_the_shared_universe_scope() {
    run(
        r#"
      (#theorem reflexive (#universes [[universe|u]] [[other|v]])
        (#parameters
          (#parameter [[type-parameter|A]]
            (#[[sort-keyword|pt-sort]] (#[[imax-keyword|pt-level-imax]] [[left|u]] [[right|v]])))
          (#parameter [[value-parameter|x]] [[parameter-type|A]]))
        (#statement (#pt-eq [[statement-type|A]] [[statement-value|x]] x))
        (#proof (#pt-refl [[evidence-type|A]] [[evidence-value|x]])))
    "#,
        &[
            ("sort-keyword", &[]),
            ("imax-keyword", &[]),
            ("left", &["universe"]),
            ("right", &["other"]),
            ("parameter-type", &["type-parameter"]),
            ("statement-type", &["type-parameter"]),
            ("statement-value", &["value-parameter"]),
            ("evidence-type", &["type-parameter"]),
            ("evidence-value", &["value-parameter"]),
        ],
    );
}

#[test]
fn sort_and_imax_malformed_operands_and_keyword_clicks_have_no_fallback() {
    for expression in [
        "(#[[query|pt-sort]] 0)",
        "(#pt-sort (#[[query|pt-level-imax]] u v))",
        "(#pt-sort (#pt-level-imax [[query|u]]))",
        "(#pt-sort (#pt-level-imax [[query|u]] v 0))",
        "(#pt-sort [[query|u]] v)",
        "(#pt-sort [[query|@u]])",
        "(#pt-sort (#pt-level-imax v [[query|@u]]))",
        "(#pt-type (#pt-level-imax v [[query|@u]]))",
        "(#pt-use u ([[query|@u]]))",
        "(#pt-level-imax [[query|u]] v)",
    ] {
        run(
            &format!("(#math-definition u () #pt-nat #pt-zero) (#math-definition editing (u v) (#pt-sort 1) {expression})"),
            &[("query", &[])],
        );
    }
}

#[test]
fn imported_sort_definitions_keep_colliding_level_aliases_out_of_universe_metadata() {
    run_files(
        r#"
      (#alias u = ./levels.lim::global-u)
      (#alias v = ./levels.lim::global-v)
      (#alias sort-value = ./levels.lim::sort-value)
      (#math-definition instantiate ([[universe|u]] [[other|v]])
        (#pt-sort (#pt-level-succ (#pt-level-imax [[left|u]] [[right|v]])))
        (#pt-use [[reference|sort-value]] ([[argument-left|u]] [[argument-right|v]])))
      (#math-definition nested ([[nested-u|u]] [[nested-v|v]])
        (#pt-sort (#pt-level-succ (#pt-level-imax (#pt-level-imax u v) v)))
        (#pt-use sort-value ((#pt-level-imax [[nested-argument-left|u]] [[nested-argument-right|v]]) v)))
    "#,
        &[(
            "levels.lim",
            r#"
          (#math-definition global-u () #pt-nat #pt-zero)
          (#math-definition global-v () #pt-nat #pt-zero)
          (#math-definition [[original|sort-value]] (a b)
            (#pt-sort (#pt-level-succ (#pt-level-imax a b)))
            (#pt-sort (#pt-level-imax a b)))
        "#,
        )],
        &[
            ("left", &["universe"]),
            ("right", &["other"]),
            ("reference", &["original"]),
            ("argument-left", &["universe"]),
            ("argument-right", &["other"]),
            ("nested-argument-left", &["nested-u"]),
            ("nested-argument-right", &["nested-v"]),
        ],
    );
}

#[test]
fn generated_sort_definitions_keep_universes_distinct_from_definition_context_names() {
    run_files(
        r#"
      (#alias emit = ./generator.lim::emit)
      (#generate emit)
      (#math-definition instantiate ([[universe|u]] [[other|v]])
        (#pt-sort (#pt-level-succ (#pt-level-imax [[left|u]] [[right|v]])))
        (#pt-use [[reference|sort-value]] ([[argument-left|u]] [[argument-right|v]])))
    "#,
        &[(
            "generator.lim",
            r#"
          (#math-definition u () #pt-nat #pt-zero)
          (#gn emit () `((#math-definition sort-value (u v)
            (#pt-sort (#pt-level-succ (#pt-level-imax u v)))
            (#pt-sort (#pt-level-imax u v)))))
        "#,
        )],
        &[
            ("left", &["universe"]),
            ("right", &["other"]),
            ("reference", &["generated:sort-value"]),
            ("argument-left", &["universe"]),
            ("argument-right", &["other"]),
        ],
    );
}

#[test]
fn theorem_parameters_share_their_source_binders_across_statement_and_evidence() {
    run(
        r#"
      (#[[declaration|theorem]] [[name|reflexive]]
        (#[[universes-keyword|universes]] [[universe|u]])
        (#[[parameters-keyword|parameters]]
          (#[[parameter-keyword|parameter]] [[type-parameter|A]] (#pt-type [[parameter-level|u]]))
          (#parameter [[value-parameter|x]] [[parameter-type|A]]))
        (#[[statement-keyword|statement]]
          (#pt-eq [[statement-type|A]] [[statement-left|x]] [[statement-right|x]]))
        (#[[proof-keyword|proof]] (#pt-refl [[evidence-type|A]] [[evidence-value|x]])))
      (#math-definition outside () #pt-nat [[leak|x]])
    "#,
        &[
            ("declaration", &[]),
            ("name", &["name"]),
            ("universes-keyword", &[]),
            ("parameters-keyword", &[]),
            ("parameter-keyword", &[]),
            ("statement-keyword", &[]),
            ("proof-keyword", &[]),
            ("universe", &["universe"]),
            ("parameter-level", &["universe"]),
            ("type-parameter", &["type-parameter"]),
            ("value-parameter", &["value-parameter"]),
            ("parameter-type", &["type-parameter"]),
            ("statement-type", &["type-parameter"]),
            ("statement-left", &["value-parameter"]),
            ("statement-right", &["value-parameter"]),
            ("evidence-type", &["type-parameter"]),
            ("evidence-value", &["value-parameter"]),
            ("leak", &[]),
        ],
    );
}

#[test]
fn theorem_parameter_types_are_sequential_and_use_the_kernel_namespaces() {
    run(
        r#"
      (#type Runtime #u64)
      (#theorem editing
        (#universes [[universe|u]])
        (#parameters
          (#parameter [[type-parameter|A]] (#pt-type [[level|u]]))
          (#parameter [[value-parameter|x]] [[value-type|A]])
          (#parameter [[path-parameter|p]] (#pt-eq [[path-type|A]] [[path-left|x]] x))
          (#parameter future [[future-type|later]])
          (#parameter later [[runtime-type|Runtime]]))
        (#statement (#pt-eq A [[statement|x]] x))
        (#proof (#pt-lambda (([[inner|x]] [[inner-type|A]])) [[inner-use|x]])))
    "#,
        &[
            ("level", &["universe"]),
            ("value-type", &["type-parameter"]),
            ("path-type", &["type-parameter"]),
            ("path-left", &["value-parameter"]),
            ("future-type", &[]),
            ("runtime-type", &[]),
            ("statement", &["value-parameter"]),
            ("inner-type", &["type-parameter"]),
            ("inner-use", &["inner"]),
        ],
    );
}

#[test]
fn math_theorems_and_direct_definitions_have_global_proof_reference_roles() {
    run_files(
        r#"
      (#alias imported = ./library.lim::reflexive)
      (#theorem [[procedural|procedural]] (#proof-eq 0u64 0u64))
      (#math-definition refs () #pt-nat
        (#pt-app (#pt-use [[theorem-use|imported]] ())
          (#pt-program [[procedural-use|procedural]])
          (#pt-certificate [[wrong-certificate|imported]])))
    "#,
        &[(
            "library.lim",
            r#"
          (#theorem [[original|reflexive]]
            (#universes) (#parameters (#parameter A (#pt-type 0)) (#parameter x A))
            (#statement (#pt-eq A x x)) (#proof (#pt-refl A x)))
        "#,
        )],
        &[
            ("theorem-use", &["original"]),
            ("procedural-use", &["procedural"]),
            ("wrong-certificate", &[]),
        ],
    );
}

#[test]
fn generated_shared_parameter_theorems_keep_the_authored_declaration_target() {
    run(
        r#"
      (#gn emit () `((#theorem reflexive
        (#universes) (#parameters (#parameter n #pt-nat))
        (#statement (#pt-eq #pt-nat n n)) (#proof (#pt-refl #pt-nat n)))))
      (#generate emit)
      (#theorem instance (#universes) (#parameters (#parameter m #pt-nat))
        (#statement (#pt-eq #pt-nat m m))
        (#proof (#pt-app (#pt-use [[reference|reflexive]] ()) m)))
    "#,
        &[("reference", &["generated:reflexive"])],
    );
}

#[test]
fn kernel_universes_and_dependent_binders_have_sequential_lexical_scopes() {
    run(
        r#"
      (#[[declaration|math-definition]] [[name|identity]] ([[universe|u]]) (#[[pi|pt-pi]] (([[type-binder|A]] (#pt-type [[signature-level|u]]))
                      ([[argument|x]] [[argument-type|A]])) [[codomain|A]]) (#[[lambda|pt-lambda]] (([[value-type|A]] (#pt-type [[value-level|u]]))
                              ([[value-binder|x]] [[value-argument-type|A]])) [[body|x]]))
      (#math-definition separate () #pt-nat [[no-leak|x]])
    "#,
        &[
            ("name", &["name"]),
            ("declaration", &[]),
            ("pi", &[]),
            ("lambda", &[]),
            ("universe", &["universe"]),
            ("signature-level", &["universe"]),
            ("value-level", &["universe"]),
            ("type-binder", &["type-binder"]),
            ("argument", &["argument"]),
            ("argument-type", &["type-binder"]),
            ("codomain", &["type-binder"]),
            ("value-argument-type", &["value-type"]),
            ("body", &["value-binder"]),
            ("no-leak", &[]),
        ],
    );
}

#[test]
fn kernel_binder_types_precede_their_binding_and_nested_binders_shadow() {
    run(
        r#"
      (#math-definition scopes () #pt-nat (#pt-lambda (([[outer|x]] #pt-nat))
          (#pt-app (#pt-lambda (([[inner|x]] [[own-type|x]])) [[inner-use|x]]) [[outer-use|x]])))
      (#math-definition bad-scope () #pt-nat (#pt-pi ((first [[later-type|later]]) (later #pt-nat)) [[first-use|first]]))
    "#,
        &[
            ("own-type", &["outer"]),
            ("inner-use", &["inner"]),
            ("outer-use", &["outer"]),
            ("later-type", &[]),
        ],
    );
}

#[test]
fn universe_levels_have_a_separate_namespace_and_never_resolve_globals() {
    run(
        r#"
      (#fn missing () #u64 (#return 0u64))
      (#math-definition levels ([[universe|u]] [[other|v]]) (#pt-type (#[[max|pt-level-max]] [[level|u]] (#[[succ|pt-level-succ]] [[successor|v]]) [[number|0]])) (#pt-lambda (([[local|u]] #pt-nat))
          (#pt-pair (#pt-type [[level-under-local|u]]) [[local-use|u]] [[universe-as-term|v]])))
      (#math-definition missing-level () (#pt-type [[unknown|missing]]) #pt-zero)
    "#,
        &[
            ("level", &["universe"]),
            ("successor", &["other"]),
            ("max", &[]),
            ("succ", &[]),
            ("number", &[]),
            ("level-under-local", &["universe"]),
            ("local-use", &["local"]),
            ("universe-as-term", &[]),
            ("unknown", &[]),
        ],
    );
}

#[test]
fn explicit_kernel_references_use_proof_declarations_instead_of_local_values() {
    run(
        r#"
      (#math-definition [[target|NatAlias]] ([[target-level|u]]) (#pt-type 0) #pt-nat)
      (#theorem [[procedural|runtime-proof]] (#proof-eq 0u64 0u64))
      (#fn function () #u64 (#return 0u64))
      (#math-definition refs ([[universe|v]]) #pt-nat (#pt-lambda ((NatAlias #pt-nat) (runtime-proof #pt-nat))
          (#pt-app (#[[use-keyword|pt-use]] [[reference|NatAlias]] ([[explicit-level|v]]))
            (#[[program-keyword|pt-program]] [[program|runtime-proof]])
            (#[[certificate-keyword|pt-certificate]] [[certificate|runtime-proof]])
            (#pt-use [[wrong-kind|function]] ())
            (#pt-program [[wrong-program|NatAlias]])
            (#pt-use [[wrong-use|runtime-proof]] ()))))
    "#,
        &[
            ("reference", &["target"]),
            ("explicit-level", &["universe"]),
            ("program", &["procedural"]),
            ("certificate", &["procedural"]),
            ("use-keyword", &[]),
            ("program-keyword", &[]),
            ("certificate-keyword", &[]),
            ("wrong-kind", &[]),
            ("wrong-program", &[]),
            ("wrong-use", &[]),
        ],
    );
}

#[test]
fn sigma_and_term_operands_reuse_kernel_scopes_without_runtime_lookup() {
    for expression in [
        "(#pt-app vALUE vALUE vALUE)",
        "(#pt-eq vALUE vALUE vALUE)",
        "(#pt-refl vALUE vALUE)",
        "(#pt-eq-elim vALUE vALUE vALUE vALUE vALUE vALUE)",
        "(#pt-pair vALUE vALUE vALUE)",
        "(#pt-first vALUE)",
        "(#pt-second vALUE)",
        "(#pt-succ vALUE)",
        "(#pt-nat-induct vALUE vALUE vALUE vALUE)",
    ] {
        let mut counter = 0;
        let mut expression = expression.to_owned();
        while let Some(start) = expression.find("vALUE") {
            expression.replace_range(start..start + 5, &format!("[[use-{counter}|value]]"));
            counter += 1;
        }
        let source = format!("(#math-definition operands () #pt-nat (#pt-lambda (([[binder|value]] #pt-nat)) {expression}))");
        let queries = (0..counter)
            .map(|index| format!("use-{index}"))
            .collect::<Vec<_>>();
        let expected = queries
            .iter()
            .map(|name| (name.as_str(), &["binder"][..]))
            .collect::<Vec<_>>();
        run(&source, &expected);
    }
    run(
        r#"
      (#math-definition dependent-pair () (#[[sigma-keyword|pt-sigma]] (([[binder|first]] #pt-nat)) (#pt-eq #pt-nat [[left|first]] [[right|first]])) [[outside|first]])
    "#,
        &[
            ("sigma-keyword", &[]),
            ("left", &["binder"]),
            ("right", &["binder"]),
            ("outside", &[]),
        ],
    );
}

#[test]
fn inductive_constructor_labels_and_dependent_fields_are_scoped_to_the_datatype() {
    run(
        r#"
      (#math-inductive [[datatype|Box]] ([[level|u]]) (([[parameter|A]] (#pt-type [[parameter-level|u]]))) (#pt-type [[sort-level|u]]) (([[constructor|pack]] (([[field|value]] [[field-type|A]])
                               ([[evidence|same]] (#pt-eq [[equality-type|A]] [[field-left|value]] [[field-right|value]]))))
         (other (([[isolated|value]] [[other-type|A]]) (leak [[field-leak|same]])))))
      (#math-inductive Another () () (#pt-type 0) ((pack ())))
      (#math-definition make ([[use-level|v]]) #pt-nat (#pt-lambda (([[element|T]] (#pt-type v)) ([[argument|x]] T))
          (#pt-construct [[datatype-use|Box]] ([[level-use|v]]) ([[parameter-use|T]]) [[constructor-use|pack]] ([[field-use|x]] x))))
      (#math-definition eliminate () #pt-nat (#pt-lambda (([[term|x]] #pt-nat))
          (#pt-induct [[induct-type|Box]] (0) ([[induct-param|x]]) [[motive|x]] ([[branch-one|x]] [[branch-two|x]]) [[subject|x]])))
    "#,
        &[
            ("datatype", &["datatype"]),
            ("parameter-level", &["level"]),
            ("sort-level", &["level"]),
            ("field-type", &["parameter"]),
            ("equality-type", &["parameter"]),
            ("field-left", &["field"]),
            ("field-right", &["field"]),
            ("other-type", &["parameter"]),
            ("field-leak", &[]),
            ("constructor", &["constructor"]),
            ("datatype-use", &["datatype"]),
            ("level-use", &["use-level"]),
            ("parameter-use", &["element"]),
            ("constructor-use", &["constructor"]),
            ("field-use", &["argument"]),
            ("induct-type", &["datatype"]),
            ("induct-param", &["term"]),
            ("motive", &["term"]),
            ("branch-one", &["term"]),
            ("branch-two", &["term"]),
            ("subject", &["term"]),
        ],
    );
}

#[test]
fn indexed_inductive_roles_respect_index_and_constructor_visibility() {
    run(
        r#"
      (#math-inductive [[datatype|vector]] () (([[parameter|A]] #pt-type 0) ([[parameter-value|a]] A))
        (#[[indices-keyword|indices]]
          (#parameter [[index|n]] (#pt-eq A a a))
          (#parameter [[second-index|m]] (#pt-eq (#pt-eq A a a) [[prior-index|n]] [[prior-index-right|n]])))
        (#pt-type 0)
        (([[cons|cons]] (([[head|x]] (#pt-eq A a a))
                         ([[tail|xs]] (#pt-eq (#pt-eq A a a) [[prior-field|x]] [[prior-field-right|x]])))
          ([[first-field-output|x]] [[field-output|xs]]))))
      (#math-definition eliminate () #pt-nat
        (#pt-lambda (([[induct-param-binding|A]] #pt-type 0) ([[induct-value-binding|a]] A)
                     ([[induct-index-binding|i]] (#pt-eq A a a))
                     ([[induct-second-index-binding|j]] (#pt-eq (#pt-eq A a a) i i))
                     ([[motive-binding|M]] #pt-nat) ([[branch-binding|B]] #pt-nat) ([[subject-binding|S]] #pt-nat))
          (#pt-induct [[datatype-use|vector]] () ([[param-use|A]] a)
            (#[[rec-indices-keyword|indices]] [[index-use|i]] [[second-index-use|j]])
            [[motive|M]] ([[branch|B]]) [[subject|S]])))
      (#math-definition self-index () #pt-nat (#pt-lambda (([[self-binding|i]] #pt-nat))
        (#pt-self-at ([[self-index|i]]))))
    "#,
        &[
            ("datatype", &["datatype"]),
            ("index", &["index"]),
            ("parameter-value", &["parameter-value"]),
            ("second-index", &["second-index"]),
            ("prior-index", &["index"]),
            ("prior-index-right", &["index"]),
            ("indices-keyword", &[]),
            ("parameter", &["parameter"]),
            ("head", &["head"]),
            ("tail", &["tail"]),
            ("prior-field", &["head"]),
            ("prior-field-right", &["head"]),
            ("field-output", &["tail"]),
            ("first-field-output", &["head"]),
            ("cons", &["cons"]),
            ("datatype-use", &["datatype"]),
            ("param-use", &["induct-param-binding"]),
            ("rec-indices-keyword", &[]),
            ("index-use", &["induct-index-binding"]),
            ("second-index-use", &["induct-second-index-binding"]),
            ("motive", &["motive-binding"]),
            ("branch", &["branch-binding"]),
            ("subject", &["subject-binding"]),
            ("self-index", &["self-binding"]),
        ],
    );
}

#[test]
fn recursive_function_fields_keep_nested_pi_and_self_index_scopes_local() {
    run(
        r#"
      (#math-inductive [[datatype|tree]] ()
        (([[parameter|a]] (#pt-type 0)))
        (#[[indices-keyword|indices]]
          (#parameter [[index|n]] #pt-nat)
          (#parameter [[dependent-index|w]] (#pt-eq #pt-nat [[prior-index-left|n]] [[prior-index-right|n]])))
        (#pt-type 0)
        (([[constructor|node]]
          (
            ([[seed-field|seed]] #pt-nat)
            ([[label-field|children]]
              (#pt-pi (([[outer-arg|x]] #pt-nat))
                (#pt-pi (([[dependent-arg|y]] (#pt-eq #pt-nat [[outer-use|x]] [[outer-use-right|x]]))
                         ([[seed-dependent|z]] (#pt-eq #pt-nat [[seed-use|seed]] [[seed-use-right|seed]]))
                         ([[element-field|element]] [[family-param-use|a]]))
                  (#pt-self-at ([[outer-index-use|x]] [[field-index-use|seed]] [[inner-index-use|y]])))))
          )
          (
            [[result-seed-use|seed]]
            (#pt-refl #pt-nat [[result-seed-refl-use|seed]])
          )
        )))
      (#math-definition build () #pt-nat
        (#pt-lambda (([[build-a|a]] (#pt-type 0)))
          (#pt-construct [[datatype-use|tree]] () ([[type-argument|a]]) [[constructor-use|node]]
            (#pt-zero
             (#pt-lambda ((x #pt-nat)
                          (y (#pt-eq #pt-nat x x))
                          (z (#pt-eq #pt-nat #pt-zero #pt-zero))
                          (element a))
               (#pt-self-at (x #pt-zero y)))))))
      (#math-definition build-external () #pt-nat
        (#pt-construct tree () ([[external-family-param|a]]) node (#pt-zero #pt-zero)))
      (#math-definition outside-index () #pt-nat [[leaked-generic-index|n]])
      (#math-definition outside () #pt-nat [[outside-y|y]])
    "#,
        &[
            ("datatype", &["datatype"]),
            ("parameter", &["parameter"]),
            ("index", &["index"]),
            ("dependent-index", &["dependent-index"]),
            ("prior-index-left", &["index"]),
            ("prior-index-right", &["index"]),
            ("indices-keyword", &[]),
            ("constructor", &["constructor"]),
            ("seed-field", &["seed-field"]),
            ("label-field", &["label-field"]),
            ("outer-arg", &["outer-arg"]),
            ("dependent-arg", &["dependent-arg"]),
            ("outer-use", &["outer-arg"]),
            ("outer-use-right", &["outer-arg"]),
            ("seed-dependent", &["seed-dependent"]),
            ("seed-use", &["seed-field"]),
            ("seed-use-right", &["seed-field"]),
            ("element-field", &["element-field"]),
            ("family-param-use", &["parameter"]),
            ("outer-index-use", &["outer-arg"]),
            ("field-index-use", &["seed-field"]),
            ("inner-index-use", &["dependent-arg"]),
            ("leaked-generic-index", &[]),
            ("result-seed-use", &["seed-field"]),
            ("result-seed-refl-use", &["seed-field"]),
            ("datatype-use", &["datatype"]),
            ("type-argument", &["build-a"]),
            ("constructor-use", &["constructor"]),
            ("build-a", &["build-a"]),
            ("external-family-param", &[]),
            ("outside-y", &[]),
        ],
    );

    for source in [
        r#"(#math-inductive tree () ((a (#pt-type 0)))
             (#indices (#parameter n #pt-nat)) (#pt-type 0)
             ((node ((child (#pt-pi ((arg #pt-nat)) (#pt-self-at ([[query|n]])))))
               (#pt-zero))))"#,
        r#"(#math-inductive tree () ((a (#pt-type 0)))
             (#indices (#parameter n #pt-nat)) (#pt-type 0)
             ((node ((child (#pt-pi ((arg #pt-nat)) #pt-self))
                     (later [[query|arg]])) (#pt-zero))))"#,
    ] {
        lim::parse(source).expect("scope-negative fixture must have balanced S-expressions");
        run(source, &[("query", &[])]);
    }
}

#[test]
fn nested_induction_resolves_terms_and_rejects_malformed_cases() {
    run(
        r#"
      (#math-inductive [[family|tree]] ([[family-level|u]]) ((A (#pt-type u))) (#pt-type u) ((leaf ())))
      (#math-definition [[selector|tree-view]] () (#pt-type 0) #pt-nat)
      (#math-definition [[apply-selector|apply-selector]] () (#pt-pi ((f #pt-nat)) #pt-nat) (#pt-lambda ((f #pt-nat)) f))
      (#math-definition proof ([[level|v]]) #pt-nat
        (#pt-lambda (([[binding|x]] (#pt-type v)) ([[selector-binding|view]] #pt-nat))
          (#pt-nested-induct [[family-use|tree]] ([[level-use|v]]) ([[parameter-use|x]]) 0 (#indices [[index-use|x]])
            ((#pt-case [[local-selector|view]]
               (#pt-lambda (([[motive-binding|m]] #pt-nat)) [[motive-use|m]])
               ((#pt-lambda (([[branch-binding|b]] #pt-nat)) [[branch-use|b]])))
             (#pt-case (#pt-app (#pt-use [[app-head|apply-selector]] ()) (#pt-use [[app-argument|tree-view]] ()))
               #pt-nat ([[sibling-use|x]]))) [[subject|x]])))
      (#math-definition bad-case () #pt-nat (#pt-nested-induct [[malformed-family|tree]] () () 0 (#indices)
        ((#pt-case (#pt-use tree ()) #pt-nat (#pt-zero)) (#pt-case #pt-nat #pt-nat #pt-zero)) #pt-zero))
    "#,
        &[
            ("family", &["family"]),
            ("family-level", &["family-level"]),
            ("selector", &["selector"]),
            ("apply-selector", &["apply-selector"]),
            ("family-use", &["family"]),
            ("level-use", &["level"]),
            ("parameter-use", &["binding"]),
            ("index-use", &["binding"]),
            ("selector-binding", &["selector-binding"]),
            ("local-selector", &["selector-binding"]),
            ("motive-binding", &["motive-binding"]),
            ("motive-use", &["motive-binding"]),
            ("branch-binding", &["branch-binding"]),
            ("branch-use", &["branch-binding"]),
            ("app-head", &["apply-selector"]),
            ("app-argument", &["selector"]),
            ("sibling-use", &["binding"]),
            ("subject", &["binding"]),
            ("malformed-family", &[]),
        ],
    );
    run(
        r#"(#math-inductive tree () () (#pt-type 0) ((leaf ())))
           (#math-definition bad () #pt-nat
             (#pt-nested-induct [[query|tree]] () () 0 (#indices)
               ((#wrong-case (#pt-use tree ()) #pt-nat (#pt-zero))
                (#pt-case (#pt-use tree ()) #pt-nat #pt-zero)) #pt-zero))"#,
        &[("query", &[])],
    );
    run(
        r#"(#math-inductive tree () () (#pt-type 0) ((leaf ())))
           (#math-definition case-index () #pt-nat #pt-zero)
           (#math-definition bad-index () #pt-nat
             (#pt-nested-induct tree () () [[query|case-index]] (#indices)
               ((#pt-case #pt-nat #pt-nat (#pt-zero))
                (#pt-case #pt-nat #pt-nat (#pt-zero))) #pt-zero))"#,
        &[("query", &[])],
    );
}

#[test]
fn generated_nested_example_family_resolves_to_emitted_declaration() {
    let example = include_str!("../examples/proof_nested.lim");
    let (declarations, rest) = example
        .split_once("(#math-definition add")
        .expect("nested example has declarations before add");
    let rest = rest.replacen(
        "(#pt-nested-induct tree",
        "(#pt-nested-induct [[family-use|tree]]",
        1,
    );
    let source =
        format!("(#gn emit () `({declarations}))\n(#generate emit)\n(#math-definition add{rest}");
    run(&source, &[("family-use", &["generated:tree"])]);
}

#[test]
fn indexed_forms_reject_malformed_clauses_arities_and_binders() {
    run(
        r#"
      (#math-inductive BadClause () () (#indices (#parameter i #pt-nat) extra) (#pt-type 0) ((ctor () ())))
      (#math-inductive BadBinder () () (#indices (#parameter [[bad-binder|bad.name]] #pt-nat)) (#pt-type 0) ((ctor () ())))
      (#math-inductive Shadow () ((A #pt-nat)) (#indices (#parameter [[shadow|A]] #pt-nat)) (#pt-type 0) ((ctor () ())))
      (#math-inductive Duplicate () () (#indices (#parameter [[duplicate-one|i]] #pt-nat) (#parameter [[duplicate-two|i]] #pt-nat)) (#pt-type 0) ((ctor () ())))
      (#math-inductive EmptyIndices () () (#[[empty-indices|indices]]) (#pt-type 0) ((ctor () ())))
      (#math-inductive OutputMismatch () () (#indices (#parameter i #pt-nat)) (#pt-type 0) (([[bad-output-ctor|ctor]] () ())))
      (#math-inductive UniverseShadow (u) () (#indices (#parameter i #pt-nat)) (#pt-type 0) ((ctor (([[universe-shadow|u]] #pt-nat)) (#pt-zero))))
      (#math-inductive good () () (#indices (#parameter i #pt-nat)) (#pt-type 0) ((ctor () ())))
      (#math-definition bad-use () #pt-nat (#pt-induct good () () (#wrong-clause i) #pt-zero () #pt-zero))
      (#math-definition short-use () #pt-nat (#pt-induct good () () (#indices i)))
      (#math-definition wrong-head () #pt-nat (#pt-induct good () () (i) #pt-zero () #pt-zero))
      (#math-definition metadata () #pt-nat (#[[indices-keyword|indices]]))
      (#math-definition parameter-metadata () #pt-nat (#[[parameter-keyword|parameter]]))
      (#math-definition malformed-self () #pt-nat (#pt-self-at i extra))
    "#,
        &[
            ("bad-binder", &[]),
            ("empty-indices", &[]),
            ("bad-output-ctor", &[]),
            ("universe-shadow", &[]),
            ("shadow", &[]),
            ("duplicate-one", &[]),
            ("duplicate-two", &[]),
            ("indices-keyword", &[]),
            ("parameter-keyword", &[]),
        ],
    );
    for term in [
        "(#pt-induct good () () (#wrong-clause [[query|value]]) #pt-zero () #pt-zero)",
        "(#pt-induct good () () ([[query|value]]) #pt-zero () #pt-zero)",
        "(#pt-induct good () () (#indices [[query|value]]) #pt-zero)",
        "(#pt-self-at [[query|value]] extra)",
    ] {
        let src = format!("(#math-inductive good () () (#indices (#parameter i #pt-nat)) (#pt-type 0) ((ctor () ()))) (#math-definition use () #pt-nat {term})");
        run(&src, &[("query", &[])]);
    }

    let many_binders = (0..65)
        .map(|i| {
            if i == 32 {
                "(#parameter [[over-index|i32]] #pt-nat)".to_owned()
            } else {
                format!("(#parameter i{i} #pt-nat)")
            }
        })
        .collect::<Vec<_>>()
        .join(" ");
    let many_outputs = std::iter::repeat("#pt-zero")
        .take(65)
        .collect::<Vec<_>>()
        .join(" ");
    run(
        &format!("(#math-inductive many () () (#indices {many_binders}) (#pt-type 0) ((ctor () ({many_outputs}))))"),
        &[("over-index", &[])],
    );

    let many_rec_indices = (0..65)
        .map(|i| {
            if i == 0 {
                "[[over-rec-index|x]]".to_owned()
            } else {
                "x".to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join(" ");
    let source = format!("(#math-inductive one () () (#indices (#parameter n #pt-nat)) (#pt-type 0) ((ctor () (#pt-zero)))) (#math-definition recursor () #pt-nat (#pt-lambda ((x #pt-nat)) (#pt-induct one () () (#indices {many_rec_indices}) #pt-zero () x)))");
    run(&source, &[("over-rec-index", &[])]);
}
#[test]
fn kernel_keywords_are_metadata_including_theorem_declarations() {
    for keyword in [
        "pt-type",
        "pt-sort",
        "pt-pi",
        "pt-lambda",
        "pt-sigma",
        "pt-use",
        "pt-app",
        "pt-level-succ",
        "pt-level-max",
        "pt-level-imax",
        "pt-eq",
        "pt-refl",
        "pt-eq-elim",
        "pt-pair",
        "pt-first",
        "pt-second",
        "pt-succ",
        "pt-numeral",
        "pt-nat-induct",
        "pt-construct",
        "pt-induct",
        "pt-self-at",
        "pt-program",
        "pt-certificate",
    ] {
        run(
            &format!("(#fn {keyword} () #u64 (#return 0u64)) (#math-definition test () #pt-nat (#[[keyword|{keyword}]]))"),
            &[("keyword", &[])],
        );
    }
    run(
        r#"
      (#[[keyword|theorem]] [[theorem|reflexive]] (#universes) (#parameters) (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
        &[("theorem", &["theorem"]), ("keyword", &[])],
    );
}

#[test]
fn kernel_metadata_and_bare_names_never_fall_back_to_global_spellings() {
    for expression in [
        "#[[query|pt-prop]]",
        "#[[query|pt-nat]]",
        "#[[query|pt-zero]]",
        "#[[query|pt-false]]",
        "#[[query|pt-self]]",
        "(#pt-numeral [[query|3]])",
        "(#pt-type [[query|value]])",
        "[[query|value]]",
        "[[query|@value]]",
        "(#pt-custom [[query|value]])",
        "(#get value [[query|value]])",
    ] {
        let source = format!("(#math-definition value () #pt-nat #pt-zero) (#math-definition test () #pt-nat {expression})");
        run(&source, &[("query", &[])]);
    }
}

#[test]
fn nat_literal_navigates_only_to_its_explicit_family_reference() {
    run(
        r#"
      (#math-inductive [[family|natural]] () () (#pt-type 0)
        (([[zero|zero]] ()) ([[successor|successor]] ((predecessor #pt-self)))))
      (#math-definition literal () (#pt-use [[result-type|natural]] ())
        (#pt-nat-literal [[family-use|natural]] "[[decimal|184467440737095516160]]"))
      (#math-definition malformed () #pt-nat
        (#pt-nat-literal [[malformed-family|natural]] "2" extra))
      (#math-definition not-string () #pt-nat
        (#pt-nat-literal [[non-string-family|natural]] natural))
    "#,
        &[
            ("result-type", &["family"]),
            ("family-use", &["family"]),
            ("decimal", &[]),
            ("malformed-family", &[]),
            ("non-string-family", &[]),
        ],
    );
}

#[test]
fn constructor_lookup_fails_closed_for_missing_ambiguous_or_noninductive_targets() {
    run(
        r#"
      (#fn label () #u64 (#return 0u64))
      (#math-inductive Duplicate () () (#pt-type 0) ((same ()) (same ())))
      (#math-definition Ordinary () (#pt-type 0) #pt-nat)
      (#math-inductive Empty () () (#pt-type 0) ())
      (#math-definition duplicate-use () #pt-nat (#pt-construct Duplicate () () [[ambiguous|same]] ()))
      (#math-definition missing-use () #pt-nat (#pt-construct Empty () () [[missing|label]] ()))
      (#math-definition wrong-use () #pt-nat (#pt-construct [[noninductive|Ordinary]] () () [[wrong-label|label]] ()))
    "#,
        &[
            ("ambiguous", &[]),
            ("missing", &[]),
            ("noninductive", &[]),
            ("wrong-label", &[]),
        ],
    );
}

#[test]
fn imported_proofs_aliases_levels_and_constructor_labels_keep_source_identity() {
    run_files(
        r#"
      (#alias Imported = ./facade.lim::Forward)
      (#alias imported-box = ./library.lim::box)
      (#math-definition NatAlias () (#pt-type 0) #pt-nat)
      (#math-definition refs ([[level|v]]) (#pt-type 0) (#pt-app (#pt-use [[alias|Imported]] ([[level-use|v]]))
                 (#pt-use [[path|./library.lim::NatAlias]] ())))
      (#math-definition constructed () #pt-nat (#pt-construct [[datatype|imported-box]] () () [[constructor|pack]] ()))
      (#alias certificate = ./library.lim::checked)
      (#theorem bridge (#universes) (#parameters) (#statement #pt-prop) (#proof (#pt-certificate [[procedural|certificate]])))
    "#,
        &[
            (
                "library.lim",
                r#"
              (#math-definition [[original|NatAlias]] (u) (#pt-type 0) #pt-nat)
              (#math-inductive [[box|box]] () () (#indices (#parameter n #pt-nat)) (#pt-type 0) (([[pack|pack]] () (#pt-zero))))
              (#theorem [[checked|checked]] (#proof-eq 0u64 0u64))
            "#,
            ),
            ("facade.lim", "(#alias Forward = ./library.lim::NatAlias)"),
        ],
        &[
            ("alias", &["original"]),
            ("path", &["original"]),
            ("level-use", &["level"]),
            ("datatype", &["box"]),
            ("constructor", &["pack"]),
            ("procedural", &["checked"]),
        ],
    );
}

#[test]
fn generated_kernel_proofs_resolve_to_their_emitted_declarations() {
    run(
        r#"
      (#gn emit () `((#math-definition nat-alias () (#pt-type 0) #pt-nat)
                    (#math-inductive vector () () (#indices (#parameter n #pt-nat)) (#pt-type 0) ((cons () (#pt-zero))))
                    (#math-definition zero () (#pt-use nat-alias ()) #pt-zero)))
      (#generate emit)
      (#math-definition use-generated () (#pt-type 0) (#pt-use [[use|nat-alias]] ()))
      (#math-definition construct-generated () (#pt-app (#pt-use vector ()) #pt-zero) (#pt-construct vector () () [[generated-label|cons]] ()))
    "#,
        &[
            ("use", &["generated:nat-alias"]),
            ("generated-label", &["generated:cons"]),
        ],
    );
}

#[test]
fn imported_generators_expose_kernel_names_through_the_final_file_scope() {
    run_files(
        r#"
      (#alias emit = ./generator.lim::emit)
      (#generate emit)
      (#math-definition use-generated () (#pt-type 0) (#pt-use [[use|generated-nat]] ()))
    "#,
        &[(
            "generator.lim",
            "(#gn emit () `((#math-definition generated-nat () (#pt-type 0) #pt-nat)))",
        )],
        &[("use", &["generated:generated-nat"])],
    );
}

#[test]
fn opaque_kernel_names_universes_and_body_binders_navigate() {
    run(
        r#"
      (#math-opaque [[opaque-name|opaque-value]] (u) #pt-nat #pt-zero)
      (#math-opaque [[function-declaration|opaque-function]] ([[function-universe|w]])
        (#pt-pi ((A (#pt-type [[signature-level|w]]))) (#pt-type w))
        (#pt-lambda (([[binder|A]] (#pt-type w))) [[body-use|A]]))
      (#math-definition use ([[use-level|v]]) #pt-nat
        (#pt-use [[explicit-use|opaque-value]] ([[level-argument|v]])))
    "#,
        &[
            ("explicit-use", &["opaque-name"]),
            ("signature-level", &["function-universe"]),
            ("body-use", &["binder"]),
            ("function-declaration", &["function-declaration"]),
            ("level-argument", &["use-level"]),
        ],
    );
}

#[test]
fn imported_and_generated_opaque_names_navigate_to_their_declarations() {
    run_files(
        r#"
      (#alias selected = ./lib.lim::imported-opaque)
      (#math-definition imported-use () #pt-nat
        (#pt-use [[imported-reference|selected]] ()))
      (#alias emit = ./generator.lim::emit)
      (#generate emit)
      (#math-definition generated-use () (#pt-type 0)
        (#pt-use [[generated-reference|generated-opaque]] ()))
    "#,
        &[
            ("lib.lim", "(#export imported-opaque) (#math-opaque [[imported-name|imported-opaque]] () #pt-nat #pt-zero)"),
            ("generator.lim", "(#gn emit () `((#math-opaque generated-opaque () (#pt-type 0) #pt-nat)))"),
        ],
        &[
            ("imported-reference", &["imported-name"]),
            ("generated-reference", &["generated:generated-opaque"]),
        ],
    );
}

fn annotated(input: &str) -> (String, HashMap<String, (usize, usize)>) {
    let mut source = String::new();
    let mut marks = HashMap::new();
    let mut rest = input;
    while let Some(start) = rest.find("[[") {
        source.push_str(&rest[..start]);
        rest = &rest[start + 2..];
        let end = rest.find("]]").unwrap();
        let (label, token) = rest[..end].split_once('|').unwrap();
        let start = source.len();
        source.push_str(token);
        assert!(marks
            .insert(label.to_owned(), (start, source.len()))
            .is_none());
        rest = &rest[end + 2..];
    }
    source.push_str(rest);
    (source, marks)
}
fn run(input: &str, expected: &[(&str, &[&str])]) {
    run_files(input, &[], expected);
}
fn run_files(input: &str, files: &[(&str, &str)], expected: &[(&str, &[&str])]) {
    let scratch = support::Scratch::new("kernel-navigation");
    let uri = lsp::path_to_uri(&scratch.path().join("main.lim")).unwrap();
    let (source, marks) = annotated(input);
    lim::parse(&source).unwrap();
    let mut locations = HashMap::new();
    for (name, &(start, end)) in &marks {
        locations.insert(name.clone(), (uri.clone(), source.clone(), start, end));
    }
    for (path, input) in files {
        let (text, marks) = annotated(input);
        let path = scratch.path().join(path);
        std::fs::write(&path, &text).unwrap();
        let uri = lsp::path_to_uri(&path).unwrap();
        for (name, (start, end)) in marks {
            assert!(locations
                .insert(name, (uri.clone(), text.clone(), start, end))
                .is_none());
        }
    }
    let mut input = Vec::new();
    for body in [
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#.to_owned(),
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.to_owned(),
        format!("{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":1,\"languageId\":\"lim\",\"text\":{}}}}}}}", quoted(&uri), quoted(&source)),
    ] { json::write_frame(&mut input, &body).unwrap(); }
    for (index, (query, _)) in expected.iter().enumerate() {
        let (line, character) = lsp::byte_position(&source, marks[*query].0);
        json::write_frame(&mut input, &format!("{{\"jsonrpc\":\"2.0\",\"id\":{},\"method\":\"textDocument/definition\",\"params\":{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":{line},\"character\":{character}}}}}}}", index + 2, quoted(&uri))).unwrap();
    }
    json::write_frame(
        &mut input,
        r#"{"jsonrpc":"2.0","id":999,"method":"shutdown","params":null}"#,
    )
    .unwrap();
    json::write_frame(
        &mut input,
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
    )
    .unwrap();
    let mut output = Vec::new();
    assert_eq!(
        lsp::serve(
            Cursor::new(input),
            &mut output,
            &lim::CompileConfig::default()
        )
        .unwrap(),
        0
    );
    let mut output = Cursor::new(output);
    let mut responses = HashMap::new();
    let mut diagnostics = Vec::new();
    while let Some(frame) = json::read_frame(&mut output).unwrap() {
        let value = json::parse(&frame).unwrap();
        if let Some(id) = value.get("id").and_then(Json::integer) {
            responses.insert(id, value);
        } else if value.get("method").and_then(Json::string)
            == Some("textDocument/publishDiagnostics")
        {
            diagnostics.push(value);
        }
    }
    for (index, (query, targets)) in expected.iter().enumerate() {
        let reply = &responses[&(index as i64 + 2)];
        let result = reply
            .get("result")
            .unwrap_or_else(|| panic!("{query}: {reply:?}"));
        let actual = match result {
            Json::Null => vec![],
            Json::Array(items) => items.iter().collect(),
            item => vec![item],
        };
        assert_eq!(
            actual.len(),
            targets.len(),
            "{query}: {result:?}\n{source}\nDiagnostics: {diagnostics:?}"
        );
        for target in *targets {
            let generated;
            let (target_uri, text, start, end) =
                if let Some(token) = target.strip_prefix("generated:") {
                    let item = actual[0];
                    let uri = item.get("uri").and_then(Json::string).unwrap().to_owned();
                    let path = lsp::uri_to_path(&uri).unwrap();
                    assert!(path
                        .file_name()
                        .unwrap()
                        .to_str()
                        .unwrap()
                        .starts_with("editor-"));
                    let text = std::fs::read_to_string(path).unwrap();
                    let start = [
                        "math-definition",
                        "math-opaque",
                        "math-inductive",
                        "theorem",
                    ]
                    .iter()
                    .find_map(|head| {
                        let prefix = format!("(#{head} ");
                        text.find(&format!("{prefix}{token} "))
                            .map(|start| start + prefix.len())
                    })
                    .or_else(|| text.find(&format!("({token} ")).map(|start| start + 1))
                    .unwrap();
                    generated = (uri, text, start, start + token.len());
                    &generated
                } else {
                    &locations[*target]
                };
            let (line, character) = lsp::byte_position(text, *start);
            let (end_line, end_character) = lsp::byte_position(text, *end);
            assert!(
                actual.iter().any(|item| {
                    let range = item.get("range").unwrap();
                    item.get("uri").and_then(Json::string) == Some(target_uri.as_str())
                        && range
                            .get("start")
                            .unwrap()
                            .get("line")
                            .and_then(Json::integer)
                            == Some(line as i64)
                        && range
                            .get("start")
                            .unwrap()
                            .get("character")
                            .and_then(Json::integer)
                            == Some(character as i64)
                        && range
                            .get("end")
                            .unwrap()
                            .get("line")
                            .and_then(Json::integer)
                            == Some(end_line as i64)
                        && range
                            .get("end")
                            .unwrap()
                            .get("character")
                            .and_then(Json::integer)
                            == Some(end_character as i64)
                }),
                "{query} must resolve to {target}: {result:?}"
            );
        }
    }
}
