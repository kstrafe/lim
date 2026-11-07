//! Constant proof obligations cross-check symbolic integers against Rust's
//! fixed-width wrapping and saturating operations at representative boundaries.
//! These are concrete cases, not universal claims over each integer domain.

fn check(source: &str) -> Result<(), String> {
    let program = lim::parse_program(source)?;
    lim::check_types(&program)
}

fn prove(claims: &[String]) {
    let source = format!(
        "(#theorem integer-semantics (#proof-and {}))",
        claims.join(" ")
    );
    check(&source).unwrap_or_else(|error| panic!("{error}\n{source}"));
}

fn disprove(claim: &str) {
    let source = format!("(#theorem false-integer-claim {claim})");
    let error = check(&source).expect_err("incorrect integer claim must be rejected");
    assert!(error.contains("disproved"), "{error}");
}

#[test]
fn every_width_matches_rust_wrap_and_saturate_boundaries() {
    let mut claims = Vec::new();
    macro_rules! unsigned_cases {
        ($ty:ty, $name:literal) => {{
            let name = $name;
            let max = <$ty>::MAX;
            let one: $ty = 1;
            let twice = max.wrapping_mul(2);
            let mask: $ty = 0b1010_1100;
            let bits: $ty = 0b0110_1010;
            let lit = |value: $ty| format!("{value}{}", $name);
            claims.push(format!(
                "(#proof-eq (#{name}::add-wrap {} {}) {})",
                lit(max),
                lit(one),
                lit(max.wrapping_add(one))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::add-saturate {} {}) {})",
                lit(max),
                lit(one),
                lit(max.saturating_add(one))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::sub-wrap 0{} {}) {})",
                $name,
                lit(one),
                lit((0 as $ty).wrapping_sub(one))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::sub-saturate 0{} {}) {})",
                $name,
                lit(one),
                lit((0 as $ty).saturating_sub(one))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::mul-wrap {} 2{}) {})",
                lit(max),
                $name,
                lit(twice)
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::mul-saturate {} 2{}) {})",
                lit(max),
                $name,
                lit(max.saturating_mul(2))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::bit-and {} {}) {})",
                lit(mask),
                lit(bits),
                lit(mask & bits)
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::bit-or {} {}) {})",
                lit(mask),
                lit(bits),
                lit(mask | bits)
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::bit-xor {} {}) {})",
                lit(mask),
                lit(bits),
                lit(mask ^ bits)
            ));
        }};
    }
    macro_rules! signed_cases {
        ($ty:ty, $name:literal) => {{
            let name = $name;
            let min = <$ty>::MIN;
            let max = <$ty>::MAX;
            let one: $ty = 1;
            let mask = 0b1010_1100u16 as $ty;
            let bits = 0b0110_1010u16 as $ty;
            let lit = |value: $ty| format!("{value}{}", $name);
            claims.push(format!(
                "(#proof-eq (#{name}::add-wrap {} {}) {})",
                lit(max),
                lit(one),
                lit(max.wrapping_add(one))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::add-saturate {} {}) {})",
                lit(max),
                lit(one),
                lit(max.saturating_add(one))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::sub-wrap {} {}) {})",
                lit(min),
                lit(one),
                lit(min.wrapping_sub(one))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::sub-saturate {} {}) {})",
                lit(min),
                lit(one),
                lit(min.saturating_sub(one))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::mul-wrap {} 2{}) {})",
                lit(min),
                $name,
                lit(min.wrapping_mul(2))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::mul-saturate {} 2{}) {})",
                lit(min),
                $name,
                lit(min.saturating_mul(2))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::div-wrap {} -1{}) {})",
                lit(min),
                $name,
                lit(min.wrapping_div(-1))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::div-saturate {} -1{}) {})",
                lit(min),
                $name,
                lit(min.saturating_div(-1))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::rem-wrap {} -1{}) {})",
                lit(min),
                $name,
                lit(min.wrapping_rem(-1))
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::bit-and {} {}) {})",
                lit(mask),
                lit(bits),
                lit(mask & bits)
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::bit-or {} {}) {})",
                lit(mask),
                lit(bits),
                lit(mask | bits)
            ));
            claims.push(format!(
                "(#proof-eq (#{name}::bit-xor {} {}) {})",
                lit(mask),
                lit(bits),
                lit(mask ^ bits)
            ));
        }};
    }
    unsigned_cases!(u8, "u8");
    unsigned_cases!(u16, "u16");
    unsigned_cases!(u32, "u32");
    unsigned_cases!(u64, "u64");
    unsigned_cases!(u128, "u128");
    unsigned_cases!(usize, "usize");
    signed_cases!(i8, "i8");
    signed_cases!(i16, "i16");
    signed_cases!(i32, "i32");
    signed_cases!(i64, "i64");
    signed_cases!(i128, "i128");
    signed_cases!(isize, "isize");
    prove(&claims);
}

#[test]
fn signed_division_remainder_shifts_and_casts_match_rust_cases() {
    prove(&[
        "(#proof-eq (#i8::div-wrap -7i8 3i8) -2i8)".into(),
        "(#proof-eq (#i8::rem-wrap -7i8 3i8) -1i8)".into(),
        "(#proof-eq (#i8::div-wrap -128i8 -1i8) -128i8)".into(),
        "(#proof-eq (#i8::div-saturate -128i8 -1i8) 127i8)".into(),
        "(#proof-eq (#i8::rem-wrap -128i8 -1i8) 0i8)".into(),
        "(#proof-eq (#u8::shl 3u8 2u8) 12u8)".into(),
        "(#proof-eq (#i8::shr -8i8 2i8) -2i8)".into(),
        "(#proof-eq (#as 255u8 #u16) 255u16)".into(),
        "(#proof-eq (#as 255u16 #u8) 255u8)".into(),
        "(#proof-eq (#as -1i16 #i8) -1i8)".into(),
    ]);
    for claim in [
        "(#proof-eq (#u8::add-wrap 255u8 1u8) 1u8)",
        "(#proof-eq (#i8::div-saturate -128i8 -1i8) -128i8)",
        "(#proof-eq (#i8::rem-wrap -7i8 3i8) 1i8)",
    ] {
        disprove(claim);
    }
}
