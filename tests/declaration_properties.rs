#[test]
fn properties_are_part_of_the_declaring_type() {
    let program = lim::parse_program(
        "(#struct Handle (#linear #repr-c) (: value #u64))
      (#enum Error (#repr-c #linear) (Failed))
      (#struct Plain () (: value #u64))
      (#enum Flag () (On Off))",
    )
    .unwrap();
    for item in &program.items {
        let (name, linear, representation) = match item {
            lim::Item::Struct {
                name,
                linear,
                representation,
                ..
            }
            | lim::Item::Enum {
                name,
                linear,
                representation,
                ..
            } => (name, *linear, *representation),
            _ => panic!("property lists must not synthesize disconnected annotations"),
        };
        let marked = matches!(name.as_str(), "Handle" | "Error");
        assert_eq!(linear, marked);
        assert_eq!(
            representation,
            if marked {
                lim::Representation::C
            } else {
                lim::Representation::Lim
            }
        );
    }
}

#[test]
fn old_forms_and_invalid_properties_are_rejected() {
    for source in [
        "(#struct Token () ()) (#linear Token)",
        "(#enum State () (Empty)) (#linear State)",
        "(#struct Old (: field #u64))",
        "(#enum Old (Empty))",
        "(#struct Old #repr-c (: field #u64))",
        "(#struct Duplicate (#linear #linear) ())",
        "(#enum Duplicate (#repr-c #repr-c) (Empty))",
        "(#struct Unknown (#copy) ())",
        "(#struct Nested ((#linear)) ())",
        "(#enum Unprefixed (linear) (Empty))",
        "(#enum Unprefixed (#linear repr-c) (Empty))",
    ] {
        assert!(lim::parse_program(source).is_err(), "accepted {source}");
    }
}

#[test]
fn generators_emit_complete_property_bearing_declarations() {
    let program = lim::parse_program(
        "(#gn make-resource (name)
      `((#struct ,name (#linear) (: value #u64))))
      (@make-resource Resource)
      (#fn main () ()
        (#let resource Resource (#struct-literal Resource (: value 1u64)))
        (#forget resource) (#return ()))",
    )
    .unwrap();
    assert!(program.items.iter().any(|item| matches!(item,
        lim::Item::Struct { name, linear: true, .. } if name == "Resource")));
    lim::check_types(&program).unwrap();
}
