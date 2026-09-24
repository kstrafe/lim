#[test]
fn array_of_constructs_values_without_changing_array_types() {
    let program = lim::parse_program(
        "(#fn main () u64 (#let values (#array u64 2) (#array-of (#array u64 2) 17u64 25u64)) (#return (#index values 1usize)))",
    )
    .unwrap();
    lim::check_types(&program).unwrap();
    lim::generate_assembly(&program).unwrap();
}
