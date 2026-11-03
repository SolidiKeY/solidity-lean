# Solidity Lean Verification

Verify open Solidity buffers with the repository's compiler frontend and
verifier. Run **Solidity Lean: Verify File** from the Command Palette.
**Discover Obligations** lists functions without running the verifier.
The Testing view can run a file or an individual overloaded function.

The default IDE path reports **correct**, **wrong** when it finds a concrete
counterexample, or **unknown** when the verifier cannot decide. It trusts the
verifier implementation and does not construct or replay a per-result Lean
certificate. Counterexamples show model inputs and initial state; constructor
reachability is a separate property. Unsupported readings remain unknown.
Import gaps, interrupted runs and backend errors remain visible.

Hover over a function to see its result and obligation reading. Edits clear
obsolete results and cancel verification. **Cancel Verification** stops active
jobs. Automatic verification after edits is enabled by default.

The backend API accepts `certify: true` for the separate certificate-producing
path; the command-line frontend also retains certified checking by default.
The optional precondition audit is available on that path. Direct results do
not establish that a specification's precondition is satisfiable.

Proof status refers to the selected obligation. Ordinary box proofs establish
partial correctness. Supported ordinary diamond loops check tuple `decreases`
annotations for defined components and strict lexicographic decrease after every
successful body turn. Unsupported shapes remain pending. Ordinary diamonds
accept exhaustion; separate successful-termination certificates are described in
[the loop notes](https://github.com/SolidiKeY/solidity-lean/blob/master/docs/loops.md#typed-tuple-measures).

Version 0.5.5 runs ordinary IDE requests through generated C, using a matching
native executable when available and WebAssembly otherwise. It supports plain
assertion obligations, scalar specifications, arrays, mappings and loops.
Undecided and unsupported programs remain unknown without starting Lean.
Explicit certificate/audit requests require the general frontend build.
Set `SOLIDITY_LEAN_DIRECT=0` to compare the general frontend.
The compact build is accepted only when its toolchain and complete project
source closure match the selected backend. [Measurements and limits](https://github.com/SolidiKeY/solidity-lean/blob/master/docs/native-extension-performance.md).

## Setup

Install Node.js 18 or later. Normal compiled checks need `node` on the editor's
process PATH and a matching packaged runtime. Building the verifier or requesting
certificates/audits also needs the Lean/Lake version in `lean-toolchain`.
Follow the repository's compiler setup in
[docs/solidity-testing.md](https://github.com/SolidiKeY/solidity-lean/blob/master/docs/solidity-testing.md),
including the pinned soljson compiler and `SOLKEY_ROOT` when needed. The
extension shares the existing compiler frontend and Lean proof commands; it does not install compilers.

Open the Solidity Lean repository as a trusted workspace, or set
`solidityLean.backendPath` to its directory. Set `solidityLean.nodePath` when
Node is not on PATH. `solidityLean.timeoutMs` bounds verification (default 600000 ms).
`solidityLean.automaticVerification` selects `onchange` (default), `onsave`, or
`never`; the older `verifyOnSave` setting selects save verification when enabled.
Verification uses the exact in-memory buffer without saving it.

To try the source extension, launch a development host:

```sh
code --extensionDevelopmentPath=/absolute/path/to/solidity-lean/vscode /absolute/path/to/solidity-lean
```

To build an installable package from this directory:

```sh
npx @vscode/vsce package
code --install-extension solidity-lean-0.5.5.vsix
```

## Standalone native verifier

Build the pinned Lean-generated C closure from the repository root:

```sh
LEAN_NUM_THREADS=1 python3 scripts/build-direct-native.py \
  /path/to/lean-4.24.0 /path/to/lean4-source .lake/direct-native
```

The Lean source checkout must match the pinned compiler commit. This executable
uses the Lean allocator and arithmetic runtime; it loads no Lean environment or
kernel. Workers keep it alive between requests. Source and binary hashes reject
stale builds. `SOLIDITY_LEAN_DIRECT_DIR` selects another build directory.
For packaging, copy `direct-check`, `build.json` and the Lean license notices to
`vscode/runtime/native`; package the portable WASM build and its notices under
`vscode/runtime/direct` as the fallback for other operating systems.

The complete 83-function comparison is in
[the TestSuite measurements](https://github.com/SolidiKeY/solidity-lean/blob/master/docs/testsuite-performance.md).

## Optional general-frontend native library

After building the backend, compile the optional library from the repository root:

```sh
lake build Solidity.Frontend.Testing
python3 scripts/build-frontend-plugin.py "$(lake env lean --print-prefix)"
```

Version 0.5.3 automatically loads a matching library from `.lake/frontend-native`.
It checks the Lean runtime, platform and backend source/artifact identities.
A stale library uses the ordinary backend until rebuilt. Native process failures
retry the ordinary backend within the request's original timeout. This path is
tested on Linux x64; compiled libraries are specific to their platform and Lean
runtime. Python and a C compiler are build-time requirements. This desktop
library does not run in the offline website.

`SOLIDITY_LEAN_NATIVE=0` disables native loading for a control run.
`SOLIDITY_LEAN_NATIVE_DIR` selects a separate build directory. Backend reports
record whether a library was active. Direct checking trusts the verifier;
explicit certified requests retain kernel and axiom checks. [Measurements](https://github.com/SolidiKeY/solidity-lean/blob/master/docs/native-extension-performance.md)
separate the modest gains from native loading from the larger gains from
skipping result certification. A 100× complete-check improvement is not claimed.

## Tests

From the repository root:

```sh
node --test vscode/test/*.test.cjs scripts/source-locations.test.mjs
node --test --test-name-pattern='editor reports' scripts/test-solidity.test.mjs
```

The first command checks controller behavior and real child processes with a
fixture backend. The second requires the configured compiler and built Lean API.
Run `lake build Solidity.Frontend.Testing` first. The real stdio LSP regression
also runs with:

```sh
LEAN_NUM_THREADS=1 SOLIDITY_LEAN_REAL_BACKEND="$PWD" node --test vscode/test/lsp-real.test.cjs vscode/test/project.test.cjs
```

It checks unsaved buffers, warm Lean reuse, compiler-backed language services,
cache identity, certified counterexamples, stale results, cancellation and
bounded concurrent workers.

The editor-host entry point uses the real VS Code API with a fixture backend:

```sh
code --user-data-dir /tmp/solidity-lean-test-profile \
  --extensions-dir /tmp/solidity-lean-test-extensions \
  --extensionDevelopmentPath=/absolute/path/to/solidity-lean/vscode \
  --extensionTestsPath=/absolute/path/to/solidity-lean/vscode/test/host.cjs \
  /absolute/path/to/solidity-lean
```

Use an isolated trusted test workspace/profile. Set
`SOLIDITY_LEAN_REAL_BACKEND=/absolute/path/to/solidity-lean` to additionally
compile and prove Solidity source through the real backend. Optional
`SOLIDITY_LEAN_NODE_EXECUTABLE` selects Node and `SOLIDITY_LEAN_HOST_RESULT`
names a JSON results file. Linux headless runs need an X server.

CI uses `vscode/test/run-host.cjs` with `@vscode/test-electron` installed only in
its temporary test directory. The Lean build job also runs the host against the
real compiler and verifier, including membership, entry audits, tuple diamond
proofs, lexical scope and certified witnesses. CI also runs the source regression
suite and frozen function listing. For an existing offline editor executable, set
`VSCODE_EXECUTABLE_PATH` instead; `VSCODE_TEST_USER_DATA_DIR` and
`VSCODE_TEST_EXTENSIONS_DIR` select isolated directories. The launcher requires
the host's fresh JSON success report as well as a successful process exit.
Set `VSCODE_TEST_NO_SANDBOX=1` only when the test environment requires Electron's
internal sandbox to be disabled.

The extension runs one persistent Solidity LSP per backend configuration. It
provides syntax highlighting, completion, definitions, references, document
symbols, signature help, highlights and guarded rename, plus proof diagnostics,
Testing results, gutters and status. Rename refuses declaration collisions and
specification-text references that need manual updates. Completion falls back to
live-text types for incomplete code. Receiver members, library extensions, workspace
symbols, compiler-validated formatting and quick fixes are built in. Quick fixes
offer explicit SPDX choices and safe unused declaration edits; documented or
specification-only parameters are preserved. Cross-file rename recompiles every
edited root and refuses stale or ambiguous edits. Specification-text renames
still require a manual update.

Each proof worker keeps a Lean language server and generated document alive,
reusing imported modules across edits. `solidityLean.workers` bounds concurrent
functions and files from 1 to 4 (default 1). Multiple workers use the checked
obligation list to schedule exact function signatures. Assertions within one
function remain serial; mixed audited/non-ready reports retain the sequential
audit path. Compiler
analysis has a separate worker. Exact checked reports are cached for unchanged
source, selection, proof options and backend generation. Changed source still
requires a proof; this cache is not Dafny's assertion-level cache. Compiler pins,
backend sources and Lean artifact identities invalidate sessions and reports.
Imports use original source units, exact dependency digests and unsaved buffers.
`solidityLean.includePaths` adds allowed import roots; `solidityLean.remappings`
accepts Solidity prefix/context remappings. Dependency edits clear stale reports
and Testing items even when the importing buffer itself is unchanged.

Multi-file contract-local specifications are supported for units without file
globals or enum/struct/UDVT declarations. Other multi-file specification namespaces,
loop annotations and compiler-code constants remain explicit proof-admission gaps.
Language services remain available for valid Solidity outside the proof profile.
See [the project/compiler record](../docs/feature-work/compiler-project-services.md).
Cancellation terminates active proof workers and their Lean children; new work
starts replacement workers. **Restart Language Server** clears sessions and
caches. Lean source files retain the Lean extension's proof-authoring tools.

## Dafny differential tests

The optional real-editor comparison harness runs equivalent Solidity and Dafny
verification scenarios, records editor/LSP observations, and measures repeated
latency and worker-count trials. See
[the harness guide](../docs/dafny-editor-parity.md) for pinned dependencies,
commands, report formats and known gaps. `npm run parity:check` validates the
source inventory offline; `npm test` includes harness regression tests. This
comparison does not establish full feature or solver parity.
