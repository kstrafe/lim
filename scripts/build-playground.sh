#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
cargo build --locked --profile wasm --target wasm32-unknown-unknown -p lim-browser
lim_target_dir="${CARGO_TARGET_DIR:-target}"
cp "$lim_target_dir/wasm32-unknown-unknown/wasm/lim_browser.wasm" docs/lim-compiler.wasm
printf 'Built docs/lim-compiler.wasm (%s bytes)\n' "$(wc -c < docs/lim-compiler.wasm)"
printf 'Serve with: python3 -m http.server 8000
Open http://localhost:8000/docs/playground.html\n'
