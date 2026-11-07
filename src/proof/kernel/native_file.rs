//! Immutable, invocation-local proof text in bounded protected scratch pages.
use super::{core::scratch::Spool, Result};
use std::{
    cell::RefCell,
    fs::File,
    io::{self, Cursor, Read, Write},
    path::Path,
    rc::Rc,
};

pub(super) const FILE_BYTES: u64 = 128 * 1024 * 1024;
const PAGE: usize = 64 * 1024;

#[derive(Clone)]
pub(super) struct Snapshot(Rc<RefCell<Spool>>);

pub(super) struct Builder {
    spool: Spool,
    limit: u64,
}
impl Builder {
    pub(super) fn new(limit: usize) -> Result<Self> {
        if limit as u64 > FILE_BYTES {
            return Err("proof snapshot byte limit exceeds backing ceiling".into());
        }
        Ok(Self {
            spool: Spool::new()?,
            limit: limit as u64,
        })
    }
    pub(super) fn with_limit(limit: usize) -> Result<Self> {
        let limit = u64::try_from(limit)
            .map_err(|_| "proof snapshot byte limit exceeds backing ceiling")?;
        if limit == 0
            || limit > isize::MAX as u64
            || limit > super::core::scratch::MAX_SELECTED_BYTES
        {
            return Err("proof snapshot byte limit exceeds backing ceiling".into());
        }
        Ok(Self {
            spool: Spool::with_limit(limit)?,
            limit,
        })
    }
    pub(super) fn append(&mut self, bytes: &[u8]) -> Result<()> {
        if self
            .spool
            .len()
            .checked_add(bytes.len() as u64)
            .is_none_or(|n| n > self.limit)
        {
            return Err("formatted proof-source byte limit exceeded".into());
        }
        self.spool.append(bytes)?;
        Ok(())
    }
    pub(super) fn finish(self) -> Snapshot {
        Snapshot(Rc::new(RefCell::new(self.spool)))
    }
}

pub(super) enum Input {
    Memory(String),
    Paged(Snapshot),
}

impl Input {
    pub(super) fn open(path: &Path) -> io::Result<Option<Self>> {
        let mut input = File::open(path)?;
        if input.metadata()?.len() > FILE_BYTES {
            return Ok(None);
        }
        let threshold = super::native_source::SOURCE_BYTES;
        let mut prefix = Vec::with_capacity(threshold + 1);
        Read::by_ref(&mut input)
            .take((threshold + 1) as u64)
            .read_to_end(&mut prefix)?;
        if prefix.len() <= threshold {
            let text = String::from_utf8(prefix).map_err(|_| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    "stream did not contain valid UTF-8",
                )
            })?;
            return Ok(Some(Self::Memory(text)));
        }
        // Include the already consumed prefix in exactly the same snapshot.
        // Reopening the path could lose bytes from a pipe or a changed source.
        Snapshot::capture(Cursor::new(prefix).chain(input), FILE_BYTES)
            .map(|snapshot| Some(Self::Paged(snapshot)))
    }
}

impl Snapshot {
    /// Freeze an explicitly selected artifact input without a general-source
    /// fallback or retaining the entire source string. The same protected
    /// bytes supply inventory, checking, and later diagnostics.
    pub(super) fn capture_with_limit(mut input: impl Read, limit: usize) -> io::Result<Self> {
        let mut builder = Builder::with_limit(limit).map_err(io::Error::other)?;
        let mut buffer = [0; PAGE];
        loop {
            let count = match input.read(&mut buffer) {
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                result => result?,
            };
            if count == 0 {
                break;
            }
            builder.append(&buffer[..count]).map_err(io::Error::other)?;
        }
        Ok(builder.finish())
    }
    fn capture(mut input: impl Read, limit: u64) -> io::Result<Self> {
        let mut spool = Spool::new().map_err(io::Error::other)?;
        let mut buffer = [0; PAGE];
        loop {
            let n = match input.read(&mut buffer) {
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                value => value?,
            };
            if n == 0 {
                break;
            }
            if spool.len().saturating_add(n as u64) > limit {
                // The prefix is already consumed. Reopening a pipe or stdin
                // could silently skip it, so this must never request fallback.
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "proof snapshot byte limit exceeded while reading input",
                ));
            }
            spool.append(&buffer[..n]).map_err(io::Error::other)?;
        }
        Ok(Self(Rc::new(RefCell::new(spool))))
    }
    pub(super) fn len(&self) -> usize {
        self.0.borrow().len() as usize
    }
    pub(super) fn reader(&self) -> SnapshotReader {
        SnapshotReader {
            snapshot: self.clone(),
            offset: 0,
        }
    }
    pub(super) fn range(&self, start: usize, end: usize) -> Result<String> {
        if start > end || end > self.len() {
            return Err("proof snapshot range is invalid".into());
        }
        let mut output = vec![0; end - start];
        for (i, chunk) in output.chunks_mut(PAGE).enumerate() {
            self.0
                .borrow_mut()
                .read_into((start + i * PAGE) as u64, chunk)?;
        }
        String::from_utf8(output).map_err(|_| "stream did not contain valid UTF-8".into())
    }
    pub(super) fn text(&self) -> io::Result<String> {
        self.range(0, self.len())
            .map_err(|message| io::Error::new(io::ErrorKind::InvalidData, message))
    }
    pub(super) fn write_to(&self, mut output: impl Write) -> io::Result<()> {
        let mut buffer = [0; PAGE];
        let mut offset = 0;
        while offset < self.len() {
            let size = (self.len() - offset).min(PAGE);
            self.0
                .borrow_mut()
                .read_into(offset as u64, &mut buffer[..size])
                .map_err(io::Error::other)?;
            output.write_all(&buffer[..size])?;
            offset += size;
        }
        Ok(())
    }
    /// Read one physical line, only when formatting a positioned error. Its
    /// allocation is bounded by the frozen file ceiling, never retained by Source.
    pub(super) fn hunk(&self, path: &str, span: crate::Span) -> Result<String> {
        if span.start > span.end || span.end > self.len() {
            return Err("proof diagnostic span is invalid".into());
        }
        let mut start = span.start;
        let mut buffer = [0; PAGE];
        while start > 0 {
            let n = start.min(PAGE);
            self.0
                .borrow_mut()
                .read_into((start - n) as u64, &mut buffer[..n])?;
            if let Some(at) = buffer[..n].iter().rposition(|b| *b == b'\n') {
                start = start - n + at + 1;
                break;
            }
            start -= n;
        }
        let mut end = span.start;
        let mut newline = false;
        while end < self.len() {
            let n = (self.len() - end).min(PAGE);
            self.0
                .borrow_mut()
                .read_into(end as u64, &mut buffer[..n])?;
            if let Some(at) = buffer[..n].iter().position(|b| *b == b'\n') {
                end += at;
                newline = true;
                break;
            }
            end += n;
        }
        let mut line = self.range(start, end)?;
        if newline && line.ends_with('\r') {
            line.pop();
        }
        let selected_start = span.start - start;
        let selected_end = span.end.min(start + line.len()) - start;
        let selected = line.get(selected_start..selected_end).unwrap_or("");
        Ok(crate::render_source_hunk_line(
            &line, selected, path, span, "here",
        ))
    }
}

pub(super) struct SnapshotReader {
    snapshot: Snapshot,
    offset: usize,
}
impl Read for SnapshotReader {
    fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
        let n = output
            .len()
            .min(PAGE)
            .min(self.snapshot.len() - self.offset);
        self.snapshot
            .0
            .borrow_mut()
            .read_into(self.offset as u64, &mut output[..n])
            .map_err(io::Error::other)?;
        self.offset += n;
        Ok(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builder_keeps_its_limit_and_streams_with_bounded_short_writes() {
        struct ShortWriter {
            bytes: Vec<u8>,
            largest_request: usize,
        }
        impl io::Write for ShortWriter {
            fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
                self.largest_request = self.largest_request.max(bytes.len());
                let n = bytes.len().min(7);
                self.bytes.extend_from_slice(&bytes[..n]);
                Ok(n)
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        let original = vec![b'x'; PAGE * 2 + 3];
        let mut builder = Builder::new(original.len()).unwrap();
        builder.append(&original).unwrap();
        assert!(builder.append(b"!").unwrap_err().contains("byte limit"));
        let snapshot = builder.finish();
        let mut output = ShortWriter {
            bytes: Vec::new(),
            largest_request: 0,
        };
        snapshot.write_to(&mut output).unwrap();
        assert_eq!(output.bytes, original);
        assert!(output.largest_request <= PAGE);
    }

    #[test]
    fn damaged_snapshot_cannot_publish_over_an_existing_output() {
        let directory = crate::output::StagingDirectory::beside(
            &std::env::temp_dir().join("snapshot-publish-test"),
        )
        .unwrap();
        let path = directory.0.join("proof.lim");
        std::fs::write(&path, "previous checked proof").unwrap();
        let mut builder = Builder::new(PAGE * 2).unwrap();
        builder.append(&vec![b'x'; PAGE * 2]).unwrap();
        let snapshot = builder.finish();
        snapshot
            .0
            .borrow_mut()
            .overwrite_flushed(PAGE as u64, b"!")
            .unwrap();
        let error =
            crate::write_output_atomic_with(&path, |file| snapshot.write_to(file)).unwrap_err();
        assert!(error.to_string().contains("checksum"));
        assert_eq!(
            std::fs::read_to_string(&path).unwrap(),
            "previous checked proof"
        );
        assert_eq!(std::fs::read_dir(&directory.0).unwrap().count(), 1);
    }

    fn assert_hunk_matches_renderer(source: &str, span: crate::Span) {
        let directory = crate::output::StagingDirectory::beside(
            &std::env::temp_dir().join("snapshot-hunk-test"),
        )
        .unwrap();
        let path = directory.0.join("source.lim");
        std::fs::write(&path, source).unwrap();
        let snapshot = Snapshot::capture(File::open(&path).unwrap(), FILE_BYTES).unwrap();

        let expected = crate::render_source_hunk(source, "source.lim", span, "here");
        assert_eq!(snapshot.hunk("source.lim", span).unwrap(), expected);

        let diagnostic =
            crate::Diagnostic::new(crate::DiagnosticCode::Type, "snapshot").with_span(span);
        let rendered = crate::render_diagnostic(&diagnostic, source, "source.lim");
        let header = crate::render_diagnostic(
            &crate::Diagnostic::new(crate::DiagnosticCode::Type, "snapshot"),
            source,
            "source.lim",
        );
        assert_eq!(rendered.strip_prefix(&header), Some(expected.as_str()));
    }

    #[test]
    fn snapshot_keeps_original_bytes_and_detects_changed_scratch_pages() {
        let directory =
            crate::output::StagingDirectory::beside(&std::env::temp_dir().join("snapshot-test"))
                .unwrap();
        let path = directory.0.join("source.lim");
        let original = "; λ\n".to_owned() + &"x".repeat(PAGE * 2);
        std::fs::write(&path, &original).unwrap();
        let snapshot = Snapshot::capture(File::open(&path).unwrap(), FILE_BYTES).unwrap();
        std::fs::write(&path, "replacement").unwrap();
        assert_eq!(snapshot.text().unwrap(), original);
        snapshot.0.borrow_mut().overwrite_flushed(0, b"!").unwrap();
        assert!(snapshot.range(0, 1).unwrap_err().contains("checksum"));
    }

    #[test]
    fn snapshot_overflow_after_consumption_is_an_error_not_fallback() {
        let mut input = &b"invalid-prefix valid-suffix"[..];
        let result = Snapshot::capture(&mut input, 8);
        assert!(
            input.is_empty(),
            "this input cannot replay its consumed prefix"
        );
        let error = result.err().expect("consumed overflow must fail closed");
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("byte limit exceeded"));
        assert_eq!(
            Snapshot::capture(&b"exact"[..], 5).unwrap().text().unwrap(),
            "exact"
        );
    }

    #[test]
    fn snapshot_hunk_matches_renderer_for_unicode_tabs_and_crlf() {
        let source = "first\r\n\t界e\u{301}target\tend\r\nlast\r\n";
        let start = source.find("target").unwrap();
        assert_hunk_matches_renderer(
            source,
            crate::Span::new(start, start + "target".len(), 2, 5),
        );
    }

    #[test]
    fn snapshot_hunk_matches_renderer_across_page_boundaries() {
        let prefix = "p".repeat(PAGE + 17);
        let source = format!("{prefix}界TARGETtail\nnext\n");
        let start = prefix.len() + "界".len();
        assert_hunk_matches_renderer(
            &source,
            crate::Span::new(start, start + 6, 1, prefix.len() + 2),
        );
    }

    #[test]
    fn snapshot_hunk_uses_frozen_source_and_matches_empty_line_edges() {
        let source = "line\n";
        let directory = crate::output::StagingDirectory::beside(
            &std::env::temp_dir().join("snapshot-frozen-hunk-test"),
        )
        .unwrap();
        let path = directory.0.join("source.lim");
        std::fs::write(&path, source).unwrap();
        let snapshot = Snapshot::capture(File::open(&path).unwrap(), FILE_BYTES).unwrap();
        std::fs::write(&path, "changed\n").unwrap();

        for span in [crate::Span::new(0, 0, 1, 1), crate::Span::new(5, 5, 2, 1)] {
            assert_eq!(
                snapshot.hunk("source.lim", span).unwrap(),
                crate::render_source_hunk(source, "source.lim", span, "here")
            );
        }
    }
}
