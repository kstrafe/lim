#[test]
fn properties_are_part_of_the_declaring_type() {
    let program = lim::parse_program(
        "#struct Handle (#linear #repr-c) ((value #u64))
#enum Error (#repr-c #linear) (Error.Failed)
#struct Plain () ((value #u64))
#enum Flag () (Flag.On Flag.Off)\n",
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
        "#struct Token () ()\n (#linear Token)",
        "#enum State () (State.Empty)\n (#linear State)",
        "#struct Old ((field #u64))\n",
        "#enum Old (Unprefixed.Empty)\n",
        "#struct Old #repr-c ((field #u64))\n",
        "#struct Duplicate (#linear #linear) ()\n",
        "#enum Duplicate (#repr-c #repr-c) (Duplicate.Empty)\n",
        "#struct Unknown (#copy) ()\n",
        "#struct Nested ((#linear)) ()\n",
        "#enum Unprefixed (linear) (Unprefixed.Empty)\n",
        "#enum Unprefixed (#linear repr-c) (Unprefixed.Empty)\n",
    ] {
        assert!(lim::parse_program(source).is_err(), "accepted {source}");
    }
}

#[test]
fn generators_emit_complete_property_bearing_declarations() {
    let program = lim::parse_program(
        "#gn make-resource { name; }
        `((#struct ,name (#linear) ((value #u64))))
#generate make-resource { name = Resource; }
#fn main {
  #params = ();
  #returns = ();
  #body = (
          (#let resource Resource (#struct-literal Resource ((value 1u64))))
          (#forget resource) (#return ())\n  );\n}\n",
    )
    .unwrap();
    assert!(program.items.iter().any(|item| matches!(item,
        lim::Item::Struct { name, linear: true, .. } if name == "Resource")));
    lim::check_types(&program).unwrap();
}
