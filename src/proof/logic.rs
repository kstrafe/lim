//! Finite, little-endian bitvectors and a bounded, fail-closed SAT solver.
//! Bits are `2 * node_id + negation`; node zero is the constant false.
use std::collections::HashMap;

pub(crate) type Bit = u32;
pub(crate) const FALSE: Bit = 0;
pub(crate) const TRUE: Bit = 1;
const NODE_LIMIT: usize = 100_000;
const WORK_LIMIT: usize = 2_000_000;
const MAX_WIDTH: usize = 128;

#[derive(Clone, Debug)]
pub(crate) struct Word {
    pub bits: Vec<Bit>,
    pub signed: bool,
}
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum Gate {
    Input,
    And(Bit, Bit),
    Xor(Bit, Bit),
}
#[derive(Clone)]
pub(crate) struct Circuit {
    nodes: Vec<Gate>,
    table: HashMap<Gate, Bit>,
    // Shape errors and either resource limit poison every subsequent SAT query.
    exhausted: bool,
}
impl Circuit {
    pub(crate) fn new() -> Self {
        Self {
            nodes: Vec::new(),
            table: HashMap::new(),
            exhausted: false,
        }
    }
    pub(crate) fn fresh(&mut self) -> Bit {
        if self.exhausted || self.nodes.len() >= NODE_LIMIT {
            self.exhausted = true;
            return FALSE;
        }
        self.nodes.push(Gate::Input);
        (self.nodes.len() as Bit) << 1
    }
    fn valid_bits(&mut self, bits: &[Bit]) -> bool {
        let ok = bits.iter().all(|&b| (b >> 1) as usize <= self.nodes.len());
        self.exhausted |= !ok;
        ok
    }
    fn gate(&mut self, g: Gate) -> Bit {
        if self.exhausted {
            return FALSE;
        }
        if let Some(&b) = self.table.get(&g) {
            return b;
        }
        if self.nodes.len() >= NODE_LIMIT {
            self.exhausted = true;
            return FALSE;
        }
        self.nodes.push(g);
        let b = (self.nodes.len() as Bit) << 1;
        self.table.insert(g, b);
        b
    }
    pub(crate) fn not(&self, b: Bit) -> Bit {
        b ^ 1
    }
    pub(crate) fn and(&mut self, a: Bit, b: Bit) -> Bit {
        if !self.valid_bits(&[a, b]) || self.exhausted {
            return FALSE;
        }
        if a == FALSE || b == FALSE || a == (b ^ 1) {
            return FALSE;
        }
        if a == TRUE {
            return b;
        }
        if b == TRUE || a == b {
            return a;
        }
        self.gate(Gate::And(a.min(b), a.max(b)))
    }
    pub(crate) fn or(&mut self, a: Bit, b: Bit) -> Bit {
        let neither = self.and(a ^ 1, b ^ 1);
        neither ^ 1
    }
    pub(crate) fn xor(&mut self, a: Bit, b: Bit) -> Bit {
        if !self.valid_bits(&[a, b]) || self.exhausted {
            return FALSE;
        }
        if a == FALSE {
            return b;
        }
        if b == FALSE {
            return a;
        }
        if a == TRUE {
            return b ^ 1;
        }
        if b == TRUE {
            return a ^ 1;
        }
        if a == b {
            return FALSE;
        }
        if a == (b ^ 1) {
            return TRUE;
        }
        self.gate(Gate::Xor(a.min(b), a.max(b)))
    }
    pub(crate) fn ite(&mut self, c: Bit, t: Bit, f: Bit) -> Bit {
        if !self.valid_bits(&[c, t, f]) || self.exhausted {
            return FALSE;
        }
        if c == TRUE {
            return t;
        }
        if c == FALSE || t == f {
            return f;
        }
        let yes = self.and(c, t);
        let no = self.and(c ^ 1, f);
        self.or(yes, no)
    }
    pub(crate) fn constant(value: u128, width: usize, signed: bool) -> Word {
        Word {
            bits: (0..if width <= MAX_WIDTH { width } else { 0 })
                .map(|i| {
                    if i < 128 && (value >> i) & 1 != 0 {
                        TRUE
                    } else {
                        FALSE
                    }
                })
                .collect(),
            signed,
        }
    }
    fn check_word(&mut self, a: &Word) -> Result<(), String> {
        if a.bits.is_empty() || a.bits.len() > MAX_WIDTH || !self.valid_bits(&a.bits) {
            self.exhausted = true;
            return Err("invalid bitvector width or node".into());
        }
        if self.exhausted {
            return Err("circuit exhausted or invalid".into());
        }
        Ok(())
    }
    fn check(&mut self, a: &Word, b: &Word) -> Result<(), String> {
        self.check_word(a)?;
        self.check_word(b)?;
        if a.bits.len() != b.bits.len() || a.signed != b.signed {
            self.exhausted = true;
            return Err("bitvector width or signedness mismatch".into());
        }
        Ok(())
    }
    pub(crate) fn word(&mut self, width: usize, signed: bool) -> Word {
        if width == 0 || width > MAX_WIDTH {
            self.exhausted = true;
            return Word {
                bits: Vec::new(),
                signed,
            };
        }
        Word {
            bits: (0..width).map(|_| self.fresh()).collect(),
            signed,
        }
    }
    pub(crate) fn eq_word(&mut self, a: &Word, b: &Word) -> Bit {
        if self.check(a, b).is_err() {
            return FALSE;
        }
        let mut equal = TRUE;
        for (&x, &y) in a.bits.iter().zip(&b.bits) {
            let different = self.xor(x, y);
            equal = self.and(equal, different ^ 1);
        }
        equal
    }
    fn unsigned_lt(&mut self, a: &[Bit], b: &[Bit]) -> Bit {
        // Each more significant differing bit overrides the previous result.
        let mut lt = FALSE;
        for (&x, &y) in a.iter().zip(b) {
            let different = self.xor(x, y);
            lt = self.ite(different, y, lt);
        }
        lt
    }
    pub(crate) fn lt_word(&mut self, a: &Word, b: &Word) -> Bit {
        if self.check(a, b).is_err() {
            return FALSE;
        }
        // Canonicalize reversed comparisons so order laws share the same
        // circuit instead of requiring exponential independent search.
        if a.bits > b.bits {
            let reverse = self.lt_word(b, a);
            let equal = self.eq_word(a, b);
            let not_less = self.or(reverse, equal);
            return self.not(not_less);
        }
        let lt = self.unsigned_lt(&a.bits, &b.bits);
        if !a.signed {
            return lt;
        }
        let sign = a.bits[a.bits.len() - 1];
        let different = self.xor(sign, b.bits[b.bits.len() - 1]);
        self.ite(different, sign, lt)
    }
    fn mux_vec(&mut self, c: Bit, a: &[Bit], b: &[Bit]) -> Vec<Bit> {
        a.iter().zip(b).map(|(&x, &y)| self.ite(c, x, y)).collect()
    }
    pub(crate) fn select(&mut self, c: Bit, a: &Word, b: &Word) -> Result<Word, String> {
        self.check(a, b)?;
        Ok(Word {
            bits: self.mux_vec(c, &a.bits, &b.bits),
            signed: a.signed,
        })
    }
    pub(crate) fn cast(&mut self, a: &Word, width: usize, signed: bool) -> Word {
        if self.check_word(a).is_err() || width == 0 || width > MAX_WIDTH {
            self.exhausted = true;
            return Word {
                bits: Vec::new(),
                signed,
            };
        }
        let fill = if a.signed {
            a.bits[a.bits.len() - 1]
        } else {
            FALSE
        };
        Word {
            bits: (0..width)
                .map(|i| a.bits.get(i).copied().unwrap_or(fill))
                .collect(),
            signed,
        }
    }
    fn add_bits(&mut self, a: &[Bit], b: &[Bit], mut carry: Bit) -> (Vec<Bit>, Bit) {
        let mut out = Vec::with_capacity(a.len());
        for (&x, &y) in a.iter().zip(b) {
            let p = self.xor(x, y);
            out.push(self.xor(p, carry));
            let g = self.and(x, y);
            let pc = self.and(p, carry);
            carry = self.or(g, pc);
        }
        (out, carry)
    }
    fn neg_bits(&mut self, a: &[Bit]) -> Vec<Bit> {
        let inv: Vec<_> = a.iter().map(|&b| b ^ 1).collect();
        self.add_bits(&inv, &vec![FALSE; a.len()], TRUE).0
    }
    fn abs_bits(&mut self, a: &Word) -> Vec<Bit> {
        let neg = self.neg_bits(&a.bits);
        self.mux_vec(a.bits[a.bits.len() - 1], &neg, &a.bits)
    }
    fn mul_full(&mut self, a: &[Bit], b: &[Bit]) -> Vec<Bit> {
        let mut acc = vec![FALSE; a.len() + b.len()];
        for (j, &y) in b.iter().enumerate() {
            if self.exhausted {
                break;
            }
            let mut row = vec![FALSE; acc.len()];
            for (i, &x) in a.iter().enumerate() {
                row[i + j] = self.and(x, y);
            }
            acc = self.add_bits(&acc, &row, FALSE).0;
        }
        acc
    }
    fn any(&mut self, bits: &[Bit]) -> Bit {
        bits.iter().fold(FALSE, |acc, &b| self.or(acc, b))
    }
    fn arithmetic(&mut self, op: &str, a: &Word, b: &Word) -> (Vec<Bit>, Bit) {
        let n = a.bits.len();
        if op == "mul" {
            // ab - sign(a)*b*2^n - sign(b)*a*2^n is the exact
            // signed product modulo 2^(2n). Correct only the high half.
            let mut full = self.mul_full(&a.bits, &b.bits);
            if a.signed {
                let mut high = full[n..].to_vec();
                for (sign, operand) in [(a.bits[n - 1], &b.bits), (b.bits[n - 1], &a.bits)] {
                    let correction: Vec<_> =
                        operand.iter().map(|&bit| self.and(sign, bit) ^ 1).collect();
                    high = self.add_bits(&high, &correction, TRUE).0;
                }
                full[n..].copy_from_slice(&high);
            }
            let mut overflow = FALSE;
            for &bit in &full[n..] {
                let extra = if a.signed {
                    self.xor(bit, full[n - 1])
                } else {
                    bit
                };
                overflow = self.or(overflow, extra);
            }
            return (full[..n].to_vec(), overflow);
        }
        let rhs: Vec<_> = b
            .bits
            .iter()
            .map(|&x| if op == "sub" { x ^ 1 } else { x })
            .collect();
        let (result, carry) = self.add_bits(&a.bits, &rhs, if op == "sub" { TRUE } else { FALSE });
        let overflow = if a.signed {
            let signs_differ = self.xor(a.bits[n - 1], b.bits[n - 1]);
            let sign_changed = self.xor(a.bits[n - 1], result[n - 1]);
            self.and(
                if op == "sub" {
                    signs_differ
                } else {
                    signs_differ ^ 1
                },
                sign_changed,
            )
        } else if op == "sub" {
            carry ^ 1
        } else {
            carry
        };
        (result, overflow)
    }
    pub(crate) fn no_overflow(&mut self, op: &str, a: &Word, b: &Word) -> Result<Bit, String> {
        self.check(a, b)?;
        let op = match op {
            "+" | "add" => "add",
            "-" | "sub" => "sub",
            "*" | "mul" => "mul",
            _ => return Err("overflow predicate supports add/sub/mul".into()),
        };
        let (_, overflow) = self.arithmetic(op, a, b);
        Ok(overflow ^ 1)
    }
    fn div_bits(&mut self, a: &[Bit], b: &[Bit]) -> (Vec<Bit>, Vec<Bit>) {
        let n = a.len();
        let mut rem = vec![FALSE; n + 1];
        let mut den = b.to_vec();
        den.push(FALSE);
        let inv: Vec<_> = den.iter().map(|&x| x ^ 1).collect();
        let mut quotient = vec![FALSE; n];
        for i in (0..n).rev() {
            rem.copy_within(0..n, 1);
            rem[0] = a[i];
            let (sub, ge) = self.add_bits(&rem, &inv, TRUE);
            rem = self.mux_vec(ge, &sub, &rem);
            quotient[i] = ge;
        }
        rem.truncate(n);
        (quotient, rem)
    }
    pub(crate) fn binary(
        &mut self,
        op: &str,
        mode: Option<&str>,
        a: &Word,
        b: &Word,
    ) -> Result<(Word, Bit), String> {
        self.check(a, b)?;
        if mode.is_some_and(|m| !matches!(m, "wrap" | "saturate")) {
            return Err("unknown arithmetic mode".into());
        }
        let n = a.bits.len();
        let mut valid = TRUE;
        let bits = match op {
            "add" | "sub" | "mul" => {
                let (result, overflow) = self.arithmetic(op, a, b);
                if mode == Some("saturate") {
                    let negative = if !a.signed {
                        FALSE
                    } else if op == "mul" {
                        self.xor(a.bits[n - 1], b.bits[n - 1])
                    } else {
                        a.bits[n - 1]
                    };
                    let bound: Vec<_> = (0..n)
                        .map(|i| {
                            if a.signed {
                                if i == n - 1 {
                                    negative
                                } else {
                                    negative ^ 1
                                }
                            } else if op == "sub" {
                                FALSE
                            } else {
                                TRUE
                            }
                        })
                        .collect();
                    self.mux_vec(overflow, &bound, &result)
                } else {
                    result
                }
            }
            "div" | "rem" => {
                valid = self.any(&b.bits);
                let aa = if a.signed {
                    self.abs_bits(a)
                } else {
                    a.bits.clone()
                };
                let bb = if a.signed {
                    self.abs_bits(b)
                } else {
                    b.bits.clone()
                };
                let (q, r) = self.div_bits(&aa, &bb);
                let mut result = if op == "div" { q } else { r };
                if a.signed {
                    let negative = if op == "div" {
                        self.xor(a.bits[n - 1], b.bits[n - 1])
                    } else {
                        a.bits[n - 1]
                    };
                    let neg = self.neg_bits(&result);
                    result = self.mux_vec(negative, &neg, &result);
                    let lower = self.any(&a.bits[..n - 1]);
                    let is_min = self.and(a.bits[n - 1], lower ^ 1);
                    let mut is_minus_one = TRUE;
                    for &bit in &b.bits {
                        is_minus_one = self.and(is_minus_one, bit);
                    }
                    let overflow = self.and(is_min, is_minus_one);
                    if mode.is_none() {
                        valid = self.and(valid, overflow ^ 1);
                    }
                    if op == "div" && mode == Some("saturate") {
                        let mut max = vec![TRUE; n];
                        max[n - 1] = FALSE;
                        result = self.mux_vec(overflow, &max, &result);
                    }
                }
                result
            }
            "bit-and" => a
                .bits
                .iter()
                .zip(&b.bits)
                .map(|(&x, &y)| self.and(x, y))
                .collect(),
            "bit-or" => a
                .bits
                .iter()
                .zip(&b.bits)
                .map(|(&x, &y)| self.or(x, y))
                .collect(),
            "bit-xor" => a
                .bits
                .iter()
                .zip(&b.bits)
                .map(|(&x, &y)| self.xor(x, y))
                .collect(),
            "shl" | "shr" => {
                // Codegen checks the count before the hardware shift (including
                // signed negative counts interpreted as unsigned). No masking.
                let bound = Self::constant(n as u128, n, false);
                // For width one, n itself still fits in the count word.
                valid = self.unsigned_lt(&b.bits, &bound.bits);
                let mut result = a.bits.clone();
                for (k, &sel) in b.bits.iter().enumerate() {
                    let distance = 1usize.checked_shl(k as u32).unwrap_or(usize::MAX);
                    let fill = if op == "shr" && a.signed {
                        a.bits[n - 1]
                    } else {
                        FALSE
                    };
                    let shifted: Vec<_> = (0..n)
                        .map(|i| {
                            let index = if op == "shl" {
                                i.checked_sub(distance)
                            } else {
                                i.checked_add(distance).filter(|&j| j < n)
                            };
                            index.map_or(fill, |j| result[j])
                        })
                        .collect();
                    result = self.mux_vec(sel, &shifted, &result);
                }
                result
            }
            _ => return Err(format!("unsupported bitvector operator: {op}")),
        };
        Ok((
            Word {
                bits,
                signed: a.signed,
            },
            valid,
        ))
    }
    fn bit_value(bit: Bit, model: &[bool]) -> bool {
        model.get((bit >> 1) as usize).copied().unwrap_or(false) ^ (bit & 1 != 0)
    }
    // Recompute gates from inputs, rather than trusting supplied gate values.
    fn evaluate(&self, inputs: &[bool]) -> Vec<bool> {
        let mut model = vec![false; self.nodes.len() + 1];
        for (i, gate) in self.nodes.iter().enumerate() {
            model[i + 1] = match *gate {
                Gate::Input => inputs.get(i + 1).copied().unwrap_or(false),
                Gate::And(a, b) => Self::bit_value(a, &model) && Self::bit_value(b, &model),
                Gate::Xor(a, b) => Self::bit_value(a, &model) ^ Self::bit_value(b, &model),
            };
        }
        model
    }
    pub(crate) fn eval(&self, bit: Bit, model: &[bool]) -> bool {
        Self::bit_value(bit, &self.evaluate(model))
    }
    pub(crate) fn value(&self, word: &Word, model: &[bool]) -> u128 {
        let model = self.evaluate(model);
        word.bits
            .iter()
            .take(128)
            .enumerate()
            .fold(0, |acc, (i, &b)| {
                if Self::bit_value(b, &model) {
                    acc | (1u128 << i)
                } else {
                    acc
                }
            })
    }
    pub(crate) fn satisfy(&mut self, condition: Bit) -> Result<Option<Vec<bool>>, String> {
        self.valid_bits(&[condition]);
        if self.exhausted {
            return Err("circuit exhausted or invalid".into());
        }
        if condition == FALSE {
            return Ok(None);
        }
        let mut clauses = Vec::new();
        // Constant literals are simplified explicitly; DIMACS zero is never a variable.
        fn clause(clauses: &mut Vec<Vec<i32>>, bits: &[Bit]) {
            if bits.contains(&TRUE) {
                return;
            }
            clauses.push(
                bits.iter()
                    .filter(|&&b| b != FALSE)
                    .map(|&b| {
                        let id = (b >> 1) as i32;
                        if b & 1 == 0 {
                            id
                        } else {
                            -id
                        }
                    })
                    .collect(),
            );
        }
        for (i, gate) in self.nodes.iter().enumerate() {
            let z = ((i + 1) as Bit) << 1;
            match *gate {
                Gate::Input => (),
                Gate::And(a, b) => {
                    clause(&mut clauses, &[z ^ 1, a]);
                    clause(&mut clauses, &[z ^ 1, b]);
                    clause(&mut clauses, &[z, a ^ 1, b ^ 1]);
                }
                Gate::Xor(a, b) => {
                    clause(&mut clauses, &[z ^ 1, a, b]);
                    clause(&mut clauses, &[z ^ 1, a ^ 1, b ^ 1]);
                    clause(&mut clauses, &[z, a ^ 1, b]);
                    clause(&mut clauses, &[z, a, b ^ 1]);
                }
            }
        }
        clause(&mut clauses, &[condition]);
        let mut solver = Solver { clauses, work: 0 };
        match solver.search(self.nodes.len()) {
            Ok(Some(assignment)) => {
                let inputs: Vec<_> = assignment.iter().map(|&v| v == 1).collect();
                let model = self.evaluate(&inputs);
                if !Self::bit_value(condition, &model) {
                    self.exhausted = true;
                    return Err("SAT model failed circuit validation".into());
                }
                Ok(Some(model))
            }
            Ok(None) => Ok(None),
            Err(e) => {
                self.exhausted = true;
                Err(e)
            }
        }
    }
}

struct Solver {
    clauses: Vec<Vec<i32>>,
    work: usize,
}
struct Decision {
    variable: usize,
    trail_start: usize,
    tried_false: bool,
}
impl Solver {
    fn search(&mut self, variables: usize) -> Result<Option<Vec<i8>>, String> {
        let mut assignment = vec![0i8; variables + 1];
        let mut trail = Vec::new();
        let mut decisions: Vec<Decision> = Vec::new();
        loop {
            let mut conflict = false;
            let mut choice;
            loop {
                let before = trail.len();
                choice = None;
                for clause in &self.clauses {
                    // Count empty clauses too, and every visited literal.
                    self.work += 1;
                    if self.work > WORK_LIMIT {
                        return Err("SAT work budget exhausted".into());
                    }
                    let mut satisfied = false;
                    let mut unassigned = 0;
                    let mut last = 0;
                    for &literal in clause {
                        self.work += 1;
                        if self.work > WORK_LIMIT {
                            return Err("SAT work budget exhausted".into());
                        }
                        let value = assignment[literal.unsigned_abs() as usize];
                        if value == 0 {
                            unassigned += 1;
                            last = literal;
                        } else if (value == 1) == (literal > 0) {
                            satisfied = true;
                            break;
                        }
                    }
                    if satisfied {
                        continue;
                    }
                    if unassigned == 0 {
                        conflict = true;
                        break;
                    }
                    if unassigned == 1 {
                        let variable = last.unsigned_abs() as usize;
                        assignment[variable] = if last > 0 { 1 } else { -1 };
                        trail.push(variable);
                    } else if choice.is_none() {
                        choice = Some(last.unsigned_abs() as usize);
                    }
                }
                if conflict || trail.len() == before {
                    break;
                }
            }
            if conflict {
                loop {
                    let Some(decision) = decisions.last_mut() else {
                        return Ok(None);
                    };
                    while trail.len() > decision.trail_start {
                        assignment[trail.pop().unwrap()] = 0;
                    }
                    if !decision.tried_false {
                        decision.tried_false = true;
                        assignment[decision.variable] = -1;
                        trail.push(decision.variable);
                        break;
                    }
                    decisions.pop();
                }
            } else if let Some(variable) = choice {
                decisions.push(Decision {
                    variable,
                    trail_start: trail.len(),
                    tried_false: false,
                });
                assignment[variable] = 1;
                trail.push(variable);
            } else {
                return Ok(Some(assignment));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn integer(x: u32, width: usize, signed: bool) -> i64 {
        if signed && x & (1 << (width - 1)) != 0 {
            x as i64 - (1i64 << width)
        } else {
            x as i64
        }
    }
    // Host integer oracle; independent of all circuit operations and evaluation.
    fn reference(
        op: &str,
        mode: Option<&str>,
        x: u32,
        y: u32,
        width: usize,
        signed: bool,
    ) -> (u128, bool, bool) {
        let a = integer(x, width, signed);
        let b = integer(y, width, signed);
        let mask = (1i64 << width) - 1;
        let lo = if signed { -(1i64 << (width - 1)) } else { 0 };
        let hi = if signed {
            (1i64 << (width - 1)) - 1
        } else {
            mask
        };
        let overflow_div = signed && a == lo && b == -1;
        let valid = match op {
            "div" | "rem" => b != 0 && !(mode.is_none() && overflow_div),
            "shl" | "shr" => y < width as u32,
            _ => true,
        };
        let math = match op {
            "add" => a + b,
            "sub" => a - b,
            "mul" => a * b,
            "div" if b != 0 => a / b,
            "rem" if b != 0 => a % b,
            "shl" if valid => (x as i64) << y,
            "shr" if valid => a >> y,
            "bit-and" => (x & y) as i64,
            "bit-or" => (x | y) as i64,
            "bit-xor" => (x ^ y) as i64,
            _ => 0,
        };
        let overflow = math < lo || math > hi;
        let result = if mode == Some("saturate") && matches!(op, "add" | "sub" | "mul" | "div") {
            math.clamp(lo, hi)
        } else {
            math
        };
        ((result & mask) as u128, valid, !overflow)
    }
    fn input_model(c: &Circuit, a: &Word, b: &Word, x: u32, y: u32) -> Vec<bool> {
        let mut model = vec![false; c.nodes.len() + 1];
        for (w, value) in [(a, x), (b, y)] {
            for (i, &bit) in w.bits.iter().enumerate() {
                model[(bit >> 1) as usize] = value & (1 << i) != 0;
            }
        }
        model
    }
    #[test]
    fn exhaustive_symbolic_numeric_semantics_widths_2_to_5() {
        for width in 2..=5 {
            for signed in [false, true] {
                for op in [
                    "add", "sub", "mul", "div", "rem", "shl", "shr", "bit-and", "bit-or", "bit-xor",
                ] {
                    for mode in [None, Some("wrap"), Some("saturate")] {
                        let mut c = Circuit::new();
                        let a = c.word(width, signed);
                        let b = c.word(width, signed);
                        let (out, valid) = c.binary(op, mode, &a, &b).unwrap();
                        let overflow = if matches!(op, "add" | "sub" | "mul") {
                            Some(c.no_overflow(op, &a, &b).unwrap())
                        } else {
                            None
                        };
                        for x in 0..1 << width {
                            for y in 0..1 << width {
                                let model = input_model(&c, &a, &b, x, y);
                                let (want, ok, no_overflow) =
                                    reference(op, mode, x, y, width, signed);
                                assert_eq!(
                                    c.eval(valid, &model),
                                    ok,
                                    "valid {op} {mode:?} w{width} signed={signed} {x} {y}"
                                );
                                if ok {
                                    assert_eq!(
                                        c.value(&out, &model),
                                        want,
                                        "value {op} {mode:?} w{width} signed={signed} {x} {y}"
                                    );
                                }
                                if let Some(bit) = overflow {
                                    assert_eq!(
                                        c.eval(bit, &model),
                                        no_overflow,
                                        "overflow {op} w{width} signed={signed} {x} {y}"
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    // Build a fixed-input SAT query without relying on eval to constrain gates.
    fn pin(c: &mut Circuit, a: &Word, b: &Word, x: u32, y: u32) -> Bit {
        let mut cube = TRUE;
        for (word, value) in [(a, x), (b, y)] {
            for (i, &bit) in word.bits.iter().enumerate() {
                let literal = if value & (1 << i) != 0 { bit } else { bit ^ 1 };
                cube = c.and(cube, literal);
            }
        }
        cube
    }
    #[test]
    fn sat_numeric_differential_exhaustive_small_inputs() {
        for width in 2..=5 {
            for signed in [false, true] {
                for op in ["add", "sub", "mul", "div", "rem", "shl", "shr"] {
                    for mode in [None, Some("wrap"), Some("saturate")] {
                        let mut base = Circuit::new();
                        let a = base.word(width, signed);
                        let b = base.word(width, signed);
                        let (out, valid) = base.binary(op, mode, &a, &b).unwrap();
                        let overflow_bit = if matches!(op, "add" | "sub" | "mul") {
                            Some(base.no_overflow(op, &a, &b).unwrap())
                        } else {
                            None
                        };
                        for x in 0..1 << width {
                            for y in 0..1 << width {
                                let (want, ok, no_overflow) =
                                    reference(op, mode, x, y, width, signed);
                                let mut c = base.clone();
                                let cube = pin(&mut c, &a, &b, x, y);
                                let expected = Circuit::constant(want, width, signed);
                                let equal = c.eq_word(&out, &expected);
                                let property = if ok { c.and(valid, equal) } else { valid ^ 1 };
                                let property = if let Some(bit) = overflow_bit {
                                    c.and(property, if no_overflow { bit } else { bit ^ 1 })
                                } else {
                                    property
                                };
                                let good = c.and(cube, property);
                                let model = c
                                    .satisfy(good)
                                    .unwrap()
                                    .expect("expected arithmetic witness");
                                assert_eq!(c.value(&a, &model), x as u128);
                                assert_eq!(c.value(&b, &model), y as u128);
                                if ok {
                                    assert_eq!(c.value(&out, &model), want);
                                }
                                let bad = c.and(cube, property ^ 1);
                                assert!(
                                    c.satisfy(bad).unwrap().is_none(),
                                    "SAT mismatch {op} {mode:?} w{width} signed={signed} {x} {y}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    #[test]
    fn constants_comparisons_casts_and_selection() {
        let mut c = Circuit::new();
        assert!(!c.eval(FALSE, &[true]));
        assert!(c.eval(TRUE, &[true]));
        assert!(c.satisfy(FALSE).unwrap().is_none());
        let model = c.satisfy(TRUE).unwrap().unwrap();
        assert!(c.eval(TRUE, &model));
        assert_eq!(c.not(FALSE), TRUE);
        for width in 1..=5 {
            for signed in [false, true] {
                let mut c = Circuit::new();
                let a = c.word(width, signed);
                let b = c.word(width, signed);
                let eq = c.eq_word(&a, &b);
                let lt = c.lt_word(&a, &b);
                let chosen = c.select(lt, &a, &b).unwrap();
                let extended = c.cast(&a, width + 2, signed);
                for x in 0..1 << width {
                    for y in 0..1 << width {
                        let model = input_model(&c, &a, &b, x, y);
                        let less = integer(x, width, signed) < integer(y, width, signed);
                        assert_eq!(c.eval(eq, &model), x == y);
                        assert_eq!(c.eval(lt, &model), less);
                        assert_eq!(c.value(&chosen, &model), if less { x } else { y } as u128);
                        let mask = (1i64 << (width + 2)) - 1;
                        assert_eq!(
                            c.value(&extended, &model),
                            (integer(x, width, signed) & mask) as u128
                        );
                    }
                }
            }
        }
        let a = Circuit::constant(u128::MAX, 128, true);
        let b = Circuit::constant(1, 128, true);
        let (out, _) = c.binary("add", Some("wrap"), &a, &b).unwrap();
        assert_eq!(c.value(&out, &[]), 0);
    }
    #[test]
    fn sat_matches_independent_gate_truth_tables() {
        // Including inverted edges, computed gates and both SAT and UNSAT queries.
        for n in 2..=5 {
            let mut base = Circuit::new();
            let vars: Vec<_> = (0..n).map(|_| base.fresh()).collect();
            let mut formulas: Vec<(Bit, Vec<bool>)> = vars
                .iter()
                .enumerate()
                .map(|(i, &v)| (v, (0..1 << n).map(|x| x & (1 << i) != 0).collect()))
                .collect();
            for step in 0..40 {
                let (a, av) = formulas[step % formulas.len()].clone();
                let (b, bv) = formulas[(step * 7 + 1) % formulas.len()].clone();
                let (bit, truth) = match step % 4 {
                    0 => (
                        base.and(a, b),
                        av.iter().zip(&bv).map(|(&a, &b)| a && b).collect(),
                    ),
                    1 => (
                        base.xor(a, b ^ 1),
                        av.iter().zip(&bv).map(|(&a, &b)| a ^ !b).collect(),
                    ),
                    2 => (
                        base.or(a ^ 1, b),
                        av.iter().zip(&bv).map(|(&a, &b)| !a || b).collect(),
                    ),
                    _ => (
                        base.ite(vars[0], a, b),
                        av.iter()
                            .zip(&bv)
                            .enumerate()
                            .map(|(x, (&a, &b))| if x & 1 != 0 { a } else { b })
                            .collect(),
                    ),
                };
                formulas.push((bit, truth));
            }
            for (bit, truth) in formulas {
                for inverted in [false, true] {
                    let f = bit ^ inverted as Bit;
                    let expected = truth.iter().any(|&v| v ^ inverted);
                    assert_eq!(base.satisfy(f).unwrap().is_some(), expected);
                    for (assignment, &v) in truth.iter().enumerate() {
                        let mut c = base.clone();
                        let mut cube = TRUE;
                        let mut model = vec![false; c.nodes.len() + 1];
                        for (i, &var) in vars.iter().enumerate() {
                            model[(var >> 1) as usize] = assignment & (1 << i) != 0;
                            cube = c.and(
                                cube,
                                if model[(var >> 1) as usize] {
                                    var
                                } else {
                                    var ^ 1
                                },
                            );
                        }
                        assert_eq!(c.eval(f, &model), v ^ inverted);
                        let query = c.and(cube, f);
                        assert_eq!(c.satisfy(query).unwrap().is_some(), v ^ inverted);
                    }
                }
            }
        }
    }
    #[test]
    fn dpll_matches_brute_force_cnf_including_backtracking() {
        let mut seed = 0x9e3779b9u32;
        let mut next = || {
            seed = seed.wrapping_mul(1664525).wrapping_add(1013904223);
            seed
        };
        for variables in 2..=5 {
            for _ in 0..500 {
                let mut clauses = Vec::new();
                for _ in 0..(next() % 18) {
                    let mut clause = Vec::new();
                    for _ in 0..(1 + next() % 4) {
                        let variable = (1 + next() as usize % variables) as i32;
                        clause.push(if next() & 0x100 != 0 {
                            variable
                        } else {
                            -variable
                        });
                    }
                    clauses.push(clause);
                }
                let satisfies = |assignment: usize| {
                    clauses.iter().all(|clause| {
                        clause.iter().any(|&literal| {
                            let value = assignment & (1 << (literal.unsigned_abs() - 1)) != 0;
                            value == (literal > 0)
                        })
                    })
                };
                let expected = (0..1 << variables).any(satisfies);
                let mut solver = Solver {
                    clauses: clauses.clone(),
                    work: 0,
                };
                let actual = solver.search(variables).unwrap();
                assert_eq!(actual.is_some(), expected);
                if let Some(model) = actual {
                    assert!(clauses.iter().all(|clause| clause.iter().any(|&literal| {
                        model[literal.unsigned_abs() as usize] == if literal > 0 { 1 } else { -1 }
                    })));
                }
            }
        }
    }
    #[test]
    fn errors_and_budgets_are_sticky() {
        for compare in [false, true] {
            for signed_mismatch in [false, true] {
                let mut c = Circuit::new();
                let a = c.word(2, false);
                let b = c.word(if signed_mismatch { 2 } else { 3 }, signed_mismatch);
                if compare {
                    c.lt_word(&a, &b);
                } else {
                    c.eq_word(&a, &b);
                }
                assert!(c.satisfy(FALSE).is_err());
                assert!(c.satisfy(TRUE).is_err());
            }
        }
        let mut c = Circuit::new();
        for _ in 0..=NODE_LIMIT {
            c.fresh();
        }
        assert!(c.exhausted);
        assert!(c.satisfy(FALSE).is_err());
        assert!(c.satisfy(TRUE).is_err());
        // One very long clause must charge literal visits, not merely clauses.
        let mut solver = Solver {
            clauses: vec![vec![1; WORK_LIMIT + 1]],
            work: 0,
        };
        assert!(solver.search(1).is_err());
        let mut c = Circuit::new();
        // Many independent clauses require >256 decisions; explicit stack only.
        let mut root = TRUE;
        for _ in 0..600 {
            let a = c.fresh();
            let b = c.fresh();
            let either = c.or(a, b);
            root = c.and(root, either);
        }
        // Whether the bounded search succeeds or exhausts, it must never say UNSAT.
        match c.satisfy(root) {
            Ok(Some(model)) => assert!(c.eval(root, &model)),
            Err(_) => {
                assert!(c.satisfy(FALSE).is_err());
                assert!(c.satisfy(TRUE).is_err());
            }
            Ok(None) => panic!("budget/depth exhaustion reported UNSAT"),
        }
    }
}
