# Third-party software

The website includes these independently licensed components. Copyright and
license notices are included in `licenses/` and in the bundled source headers.

- Monaco Editor 0.55.1: MIT, Microsoft. Source: https://github.com/microsoft/monaco-editor
- Brotli decoder 2.3.2 (`brotli-dec-wasm`): MIT OR Apache-2.0.
  Source: https://github.com/ustclug-dev/brotli-dec-wasm
- Solidity compiler 0.8.34 (`80d5c536`): GPL-3.0, Solidity contributors.
  Corresponding source: https://github.com/ethereum/solidity/tree/v0.8.34
- Lean 4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`): Apache-2.0,
  Microsoft and Lean contributors. Source: https://github.com/leanprover/lean4/tree/v4.24.0
- GMP 6.2.1: LGPL-3.0-or-later or GPL-2.0-or-later. Source:
  https://github.com/alisw/GMP/tree/v6.2.1
- Emscripten 4.0.15 and its C/C++ runtime libraries: their upstream licenses.
  Source: https://github.com/emscripten-core/emscripten/tree/4.0.15
- `@noble/hashes` 1.8.0, `buffer` 6.0.3, `path-browserify` 1.0.1 and
  `fflate` 0.8.2: MIT.

The Lean/GMP port, complete build instructions and pinned toolchain/source
references are in this repository's `web/tools/lean-wasm/`,
`web/tools/build-lean-browser.sh` and `web/browser/`. Rebuild or relink the browser
runtime with those scripts and the corresponding upstream source trees.
