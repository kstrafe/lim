mod support;
use std::os::unix::process::ExitStatusExt;
use std::{fs, process::Command, time::Duration};

const SEED: u64 = 0x51ed_2026;

fn execute(source: &str, expected_signal: Option<i32>) {
    let scratch = support::Scratch::new("numeric");
    let root = scratch.path();
    fs::write(root.join("main.lim"), source).unwrap();
    let (status, _, error) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(root.join("main.lim"))
            .arg("-o")
            .arg(root.join("program")),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(
        status.success(),
        "seed={SEED:x}\n{source}\n{}",
        String::from_utf8_lossy(&error)
    );
    let (status, _, error) = support::run(
        &mut Command::new(root.join("program")),
        // The differential corpus launches many tiny binaries. Allow slower
        // CI/loaded-host scheduling while retaining a finite hang timeout.
        Duration::from_secs(10),
        1024,
    )
    .unwrap();
    assert_eq!(
        status.signal(),
        expected_signal,
        "seed={SEED:x}\n{source}\n{}",
        String::from_utf8_lossy(&error)
    );
    if expected_signal.is_none() {
        assert_eq!(status.code(), Some(42), "seed={SEED:x}\n{source}");
    }
}

#[test]
fn seeded_integer_oracle_checks_constants_and_native_operations() {
    macro_rules! check {
        ($ty:ty) => {{
            let name = stringify!($ty);
            let mut state = SEED;
            let mut cases = Vec::new();
            let mut values = vec![<$ty>::MIN, <$ty>::MAX, 0, 1, 2];
            for _ in 0..5 {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
                values.push(((state as u128) << 64 | state as u128) as $ty);
            }
            for (index, &a) in values.iter().enumerate() {
                for (operator, expected) in [
                    ("sub-wrap", a.wrapping_neg()),
                    ("sub-saturate", (0 as $ty).saturating_sub(a)),
                    ("not", !a),
                ] { cases.push((format!("(#{name}::{operator} {a}{name})"), expected)); }
                let b = values[(index + 1) % values.len()];
                for (op, expected) in [
                    ("add-wrap", a.wrapping_add(b)), ("sub-wrap", a.wrapping_sub(b)),
                    ("mul-wrap", a.wrapping_mul(b)), ("bit-and", a & b), ("bit-or", a | b), ("bit-xor", a ^ b),
                ] { cases.push((format!("(#{name}::{op} {a}{name} {b}{name})"), expected)); }
                {
                    for (op, expected) in [("add-saturate", a.saturating_add(b)), ("sub-saturate", a.saturating_sub(b)), ("mul-saturate", a.saturating_mul(b))] {
                        cases.push((format!("(#{name}::{op} {a}{name} {b}{name})"), expected));
                    }
                }
                if b != 0 {
                    cases.push((format!("(#{name}::div-wrap {a}{name} {b}{name})"), a.wrapping_div(b)));
                    cases.push((format!("(#{name}::rem-wrap {a}{name} {b}{name})"), a.wrapping_rem(b)));
                }
                for shift in [0, <$ty>::BITS - 1] {
                    cases.push((format!("(#{name}::shl {a}{name} {shift}{name})"), a.wrapping_shl(shift)));
                    cases.push((format!("(#{name}::shr {a}{name} {shift}{name})"), a.wrapping_shr(shift)));
                }
            }
            let (a, b) = (<$ty>::MIN, !0 as $ty);
            cases.push((format!("(#{name}::div-wrap (#{name}::sub-wrap {a}{name}) 2{name})"), a.wrapping_neg().wrapping_div(2)));
            cases.push((format!("(#{name}::div-wrap (#{name}::not 0{name}) 2{name})"), (!0 as $ty).wrapping_div(2)));
            cases.push((format!("(#{name}::div-wrap (#{name}::add-wrap {}{name} 1{name}) 2{name})", <$ty>::MAX), <$ty>::MAX.wrapping_add(1).wrapping_div(2)));
            cases.push((format!("(#{name}::div-wrap {a}{name} {b}{name})"), a.wrapping_div(b)));
            cases.push((format!("(#{name}::div-saturate {a}{name} {b}{name})"), a.saturating_div(b)));
            cases.push((format!("(#{name}::rem-wrap {a}{name} {b}{name})"), a.wrapping_rem(b)));
            for batch in cases.chunks(32) {
                let mut source = String::new();
                let mut checks = String::new();
                for (index, (expression, expected)) in batch.iter().enumerate() {
                    source.push_str(&format!("(#const c{index} #{name} {expression})\n"));
                    checks.push_str(&format!("(#assert (#{name}::eq c{index} {expected}{name}))\n(#assert (#{name}::eq {expression} {expected}{name}))\n"));
                }
                source.push_str(&format!("(#fn main () #u64 {checks} (#return 42u64))"));
                execute(&source, None);
            }
        }};
    }
    check!(u8);
    check!(u16);
    check!(u32);
    check!(u64);
    check!(u128);
    check!(usize);
    check!(i8);
    check!(i16);
    check!(i32);
    check!(i64);
    check!(i128);
    check!(isize);
}

#[test]
fn exceptional_values_casts_and_shift_failures_match_the_contract() {
    for ty in ["u128", "i128"] {
        execute(&format!("(#fn shift ((count #{ty})) #{ty} (#return (#{ty}::shl 1{ty} count))) (#fn main () #u64 (#let value #{ty} (#call shift ((count 18446744073709551616{ty})))) (#return 42u64))"), Some(4));
    }
    for ty in ["f32", "f64"] {
        execute(
            &format!(
                "(#fn main () #u64
          (#let nan #{ty} (#{ty}::div 0.0{ty} 0.0{ty}))
          (#let infinity #{ty} (#{ty}::div 1.0{ty} 0.0{ty}))
          (#assert (#{ty}::ne nan nan))
          (#assert (#bool::eq (#{ty}::lt nan infinity) false))
          (#assert (#bool::eq (#{ty}::ge nan infinity) false))
          (#assert (#{ty}::eq -0.0{ty} 0.0{ty}))
          (#assert (#{ty}::gt infinity 1.0{ty})) (#return 42u64))"
            ),
            None,
        );
    }
    execute("(#fn main () #u64 (#assert (#u8::eq (#as 511u64 #u8) 255u8)) (#assert (#i64::eq (#as -128i8 #i64) -128i64)) (#assert (#u128::eq (#as 18446744073709551615u64 #u128) 18446744073709551615u128)) (#return 42u64))", None);
    for ty in [
        "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
    ] {
        execute(&format!("(#fn div ((zero #{ty})) #{ty} (#return (#{ty}::div-wrap 1{ty} zero))) (#fn main () #u64 (#let value #{ty} (#call div ((zero 0{ty})))) (#return 42u64))"), Some(4));
        let width = if ty.ends_with("size") {
            64
        } else {
            ty[1..].parse::<u32>().unwrap()
        };
        // i8 cannot represent 128, but every type can represent its own width.
        execute(&format!("(#fn shift ((count #{ty})) #{ty} (#return (#{ty}::shl 1{ty} count))) (#fn main () #u64 (#let value #{ty} (#call shift ((count {width}{ty})))) (#return 42u64))"), Some(4));
    }
}
