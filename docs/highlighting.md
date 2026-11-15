# Lexical highlighting maintenance

`lim-highlight.mjs` provides a small shared, lossless lexical colorizer. It recognizes line comments, escaped strings (including unfinished strings while editing), Lim character literals, numeric/boolean literals, `#` forms, scalar types and operators. It does not validate syntax or resolve names. Every source fragment is HTML-escaped before insertion.

The handbook generator calls `scripts/highlight-code.mjs` once for all Lim/Lisp code fences after Pandoc conversion. Generated spans contain the original text and no scripts or external resources. The generator now needs Node.js in addition to Pandoc and Python, all provided by the existing Nix shell. Other code fences retain their existing rendering.

The playground uses the same colorizer in a presentation-only overlay behind its native textarea. Input, selected examples and scrolling refresh it; copying and editing still use the original textarea. Without JavaScript, or with forced colors enabled, the textarea remains plain readable text. Colors adapt to the existing light/dark themes and print as dark text.

Run from the repository root, after coordinating the shared command slot:

```sh
bash scripts/limited-run.sh node scripts/check-highlighting.mjs
bash scripts/limited-run.sh python3 scripts/check-highlighting.py
bash scripts/limited-run.sh python3 scripts/build-reference.py
bash scripts/limited-run.sh python3 scripts/build-reference.py --check
bash scripts/limited-run.sh node scripts/check-highlighting-browser.mjs
```

The browser check uses locally installed Chromium without npm packages or compiler builds. It checks live updates, escaped HTML, scroll alignment, 320px and 390px page widths, and the offline handbook's browser Find and lack of external resources. Existing compiler/playground execution checks remain separate.

Validated in this snapshot: all commands above passed, including contrast of every generated token against its computed code background in both light and dark themes (at least 4.5:1). The initial boundary assertion was corrected to treat `#u64ish` as a generic `#` form, rather than a scalar type. A mobile screenshot was visually reviewed.
