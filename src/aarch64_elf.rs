//! Static AArch64 Linux ELF, with RX code and a non-executable GNU stack.
pub fn executable(words: &[u32], entry: usize) -> Result<Vec<u8>, String> {
    let size = words
        .len()
        .checked_mul(4)
        .and_then(|n| n.checked_add(4096))
        .ok_or("AArch64 ELF size overflow")?;
    if words.is_empty() || entry >= words.len() {
        return Err("AArch64 ELF entry must point into code".into());
    }
    let mut bytes = vec![0; size];
    bytes[..8].copy_from_slice(b"\x7fELF\x02\x01\x01\x00");
    put16(&mut bytes, 16, 2);
    put16(&mut bytes, 18, 183);
    put32(&mut bytes, 20, 1);
    put64(&mut bytes, 24, 0x401000 + (entry as u64) * 4);
    put64(&mut bytes, 32, 64);
    put16(&mut bytes, 52, 64);
    put16(&mut bytes, 54, 56);
    put16(&mut bytes, 56, 2);
    put32(&mut bytes, 64, 1);
    put32(&mut bytes, 68, 5);
    put64(&mut bytes, 80, 0x400000);
    put64(&mut bytes, 88, 0x400000);
    put64(&mut bytes, 96, size as u64);
    put64(&mut bytes, 104, size as u64);
    put64(&mut bytes, 112, 4096);
    put32(&mut bytes, 120, 0x6474e551);
    put32(&mut bytes, 124, 6);
    put64(&mut bytes, 168, 16);
    for (index, word) in words.iter().enumerate() {
        put32(&mut bytes, 4096 + index * 4, *word);
    }
    Ok(bytes)
}
fn put16(bytes: &mut [u8], at: usize, value: u16) {
    bytes[at..at + 2].copy_from_slice(&value.to_le_bytes());
}
fn put32(bytes: &mut [u8], at: usize, value: u32) {
    bytes[at..at + 4].copy_from_slice(&value.to_le_bytes());
}
fn put64(bytes: &mut [u8], at: usize, value: u64) {
    bytes[at..at + 8].copy_from_slice(&value.to_le_bytes());
}
