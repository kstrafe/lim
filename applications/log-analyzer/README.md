# Native Lim log analyzer

Linux x86-64 application using the bundled stdin and String APIs. From the repository root:

```sh
bash scripts/limited-run.sh nix develop --command cargo build --bin lim
bash scripts/limited-run.sh target/debug/lim applications/log-analyzer/main.lim -o applications/log-analyzer/log-analyzer
bash scripts/limited-run.sh python3 applications/log-analyzer/tests/test.py
bash scripts/limited-run.sh bash -c 'applications/log-analyzer/log-analyzer < applications/log-analyzer/tests/fixtures/mixed.log'
```

The program streams UTF-8 stdin one line at a time. An uppercase `INFO`, `WARN`, or `ERROR` token must start at byte zero and be followed by space, tab, CR, or end of line. All other lines, including blank lines, count as OTHER. LF terminates a line; CRLF works because CR is a token boundary. A final nonempty line without LF counts once. Empty input has zero lines. It does not search message bodies or parse timestamps/bracketed levels.

Output always uses this order, decimal counts, and a final newline:

```text
TOTAL 7
INFO 2
WARN 1
ERROR 1
OTHER 3
```

Exit codes: 0 success; 1 stdin, UTF-8, or input allocation failure; 2 summary allocation/write failure; 3 total counter overflow. Read failure suppresses the summary; write failure may leave partial output. Counts cannot wrap: total is checked before incrementing and bounds every severity count. stdin/stdout are borrowed process streams; the program allocates no file handles. The owned input and output Strings are freed on every handled exit path.

Memory scales with the longest line, rather than the whole input. The existing reader performs a syscall for each byte, so this is a correctness-oriented tool, not a high-throughput collector. No compiler or shared library modifications are required.
