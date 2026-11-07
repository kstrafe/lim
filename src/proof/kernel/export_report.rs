//! Streaming audit receipts. Output never supplies theorem authority.
use super::*;
use std::io::{self, Write};

impl LeanExportReport {
    /// Render a receipt in memory. For large inventories, `write_json` avoids
    /// retaining a second complete serialized copy alongside the report.
    pub fn render_json(&self) -> String {
        let mut output = Vec::new();
        self.write_json(&mut output)
            .expect("writing replay JSON to a Vec cannot fail");
        String::from_utf8(output).expect("replay JSON is UTF-8")
    }

    /// Stream the same canonical JSON receipt to a writer. Errors propagate
    /// immediately; a partial write is not a successfully published receipt.
    /// Neither this output nor its hashes can bypass later proof checking.
    pub fn write_json<W: Write + ?Sized>(&self, output: &mut W) -> io::Result<()> {
        self.write_inventory(output, self.declarations.len(), |output, index| {
            write_declaration(output, &self.declarations[index])
        })
    }

    fn write_inventory<W: Write + ?Sized>(
        &self,
        output: &mut W,
        count: usize,
        mut declaration: impl FnMut(&mut W, usize) -> io::Result<()>,
    ) -> io::Result<()> {
        // Keep the former BTreeMap renderer's lexicographic field order and
        // escaping, so existing receipts remain byte-for-byte identical.
        output.write_all(b"{\"axioms\":")?;
        write_strings(output, &self.axioms)?;
        write!(output, ",\"bytes\":{},\"declaration_hash_scope\":\"export-prefix-through-record\",\"declarations\":[", self.bytes)?;
        for index in 0..count {
            if index != 0 {
                output.write_all(b",")?;
            }
            declaration(output, index)?;
        }
        output.write_all(b"]")?;
        // Preserve existing default receipts byte-for-byte. A selected input
        // profile is audit data, separate from proof authority and work.
        if self.limits != LeanExportLimits::default() {
            let limits = self.limits;
            write!(output, ",\"export_limits\":{{\"max_bytes\":{},\"max_declarations\":{},\"max_dependencies\":{},\"max_dependency_bytes\":{},\"max_expressions\":{},\"max_levels\":{},\"max_name_bytes\":{},\"max_names\":{},\"max_payload_bytes\":{},\"max_scratch_bytes\":{}}}", limits.max_bytes, limits.max_declarations, limits.max_dependencies, limits.max_dependency_bytes, limits.max_expressions, limits.max_levels, limits.max_name_bytes, limits.max_names, limits.max_payload_bytes, limits.max_scratch_bytes)?;
        }
        output.write_all(b",\"exporter_revision\":")?;
        write_string(output, EXPORTER_REVISION)?;
        output.write_all(b",\"format_version\":")?;
        write_string(output, LEAN_EXPORT_FORMAT)?;
        output.write_all(b",\"foundations\":")?;
        write_strings(output, &self.foundations)?;
        output.write_all(b",\"input_sha256\":")?;
        write_string(output, &self.input_sha256)?;
        output.write_all(b",\"lean_githash\":")?;
        write_string(output, LEAN_EXPORT_GITHASH)?;
        output.write_all(b",\"lean_version\":")?;
        write_string(output, LEAN_EXPORT_VERSION)?;
        if let Some(limits) = self
            .native_limits
            .filter(|limits| *limits != crate::NativeProofLimits::default())
        {
            write!(output, ",\"native_proof_limits\":{{\"max_bytes\":{},\"max_correspondence_bytes\":{},\"max_correspondence_nodes\":{},\"max_declarations\":{},\"max_directory_bytes\":{},\"max_render_nodes\":{},\"max_scratch_bytes\":{}}}", limits.max_bytes, limits.max_correspondence_bytes, limits.max_correspondence_nodes, limits.max_declarations, limits.max_directory_bytes, limits.max_render_nodes, limits.max_scratch_bytes)?;
        }
        write!(output, ",\"proof_budget\":{{\"transformation_bytes_per_phase\":{},\"transformation_bytes_total\":{},\"work_per_phase\":{}}},\"records\":{},\"schema\":\"lim-lean-replay-v1\",\"target\":", self.budget.phase_bytes(), self.budget.total_bytes(), self.budget.work(), self.records)?;
        write_string(output, &self.target)?;
        output.write_all(b",\"target_axioms\":")?;
        write_strings(output, &self.target_axioms)?;
        output.write_all(b"}")
    }
}

impl LeanExportReceipt {
    /// Stream checked inventory records without materializing the full report.
    /// Storage and writer failures abort the write; publish through an atomic
    /// output writer when the receipt must replace an existing file.
    pub fn write_json<W: Write + ?Sized>(&self, output: &mut W) -> io::Result<()> {
        self.summary
            .write_inventory(output, self.declarations.len(), |output, index| {
                let declaration = self.declarations.get(index).map_err(io::Error::other)?;
                write_declaration(output, &declaration)
            })
    }
}

fn write_declaration<W: Write + ?Sized>(
    output: &mut W,
    declaration: &LeanDeclarationReport,
) -> io::Result<()> {
    output.write_all(b"{\"dependencies\":")?;
    write_strings(output, &declaration.dependencies)?;
    output.write_all(b",\"identity\":")?;
    write_string(output, &declaration.identity)?;
    output.write_all(b",\"kind\":")?;
    write_string(output, &declaration.kind)?;
    write!(output, ",\"line\":{},\"name\":", declaration.line)?;
    write_string(output, &declaration.name)?;
    output.write_all(b",\"sha256\":")?;
    write_string(output, &declaration.sha256)?;
    output.write_all(b"}")
}

fn write_strings<W: Write + ?Sized>(output: &mut W, values: &[String]) -> io::Result<()> {
    output.write_all(b"[")?;
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            output.write_all(b",")?;
        }
        write_string(output, value)?;
    }
    output.write_all(b"]")
}

fn write_string<W: Write + ?Sized>(output: &mut W, value: &str) -> io::Result<()> {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    output.write_all(b"\"")?;
    let bytes = value.as_bytes();
    let mut start = 0;
    for (index, &byte) in bytes.iter().enumerate() {
        let escape: &[u8] = match byte {
            b'"' => b"\\\"",
            b'\\' => b"\\\\",
            b'\n' => b"\\n",
            b'\r' => b"\\r",
            b'\t' => b"\\t",
            0..=31 => &[],
            _ => continue,
        };
        output.write_all(&bytes[start..index])?;
        if escape.is_empty() {
            output.write_all(&[
                b'\\',
                b'u',
                b'0',
                b'0',
                HEX[(byte >> 4) as usize],
                HEX[(byte & 15) as usize],
            ])?;
        } else {
            output.write_all(escape)?;
        }
        start = index + 1;
    }
    output.write_all(&bytes[start..])?;
    output.write_all(b"\"")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn streaming_strings_preserve_existing_canonical_escaping() {
        let controls = (0u8..=31).map(char::from).collect::<String>();
        for value in ["", "ordinary text", "é🦀\"\\\n\r\t\0", &controls] {
            let mut bytes = Vec::new();
            write_string(&mut bytes, value).unwrap();
            assert_eq!(bytes, crate::diagnostic_json::quoted(value).as_bytes());
        }
    }
}
