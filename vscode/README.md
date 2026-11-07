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

`npm run parity:stdio -- --dafny /path/to/dafny --output /path/to/new-results`
runs the real servers without Electron. It defaults to language-service checks;
`--scope full` adds verification and requires a freshly built local backend.
`parity:check` also checks the independent upstream test-discovery ledger. The
manual editor-parity workflow offers both transports. Stdio results do not
establish VS Code UI behavior.

Startup checks the configured Node executable against the existing Node18+ requirement and verifies that the backend directory contains readable `scripts/test-solidity.mjs` and `lean-toolchain` files. Failures offer settings or an explicit Node download-page link; the extension does not install or replace executables. The version item shows actual server initialize identity (or unknown), Node runtime and extension metadata. Initialization is not proof/backend readiness: compiler/runtime/toolchain checks still occur when their operations run. Resource configuration changes restart affected owners while retaining healthy clients.

After LSP initialization, the version item waits separately up to five seconds for the running server's `solidityLean/serverVersion` metadata notification. Missing/malformed data yields unknown; a late notification cannot replace that settled result. The separate initialization deadline remains30seconds. Timers and subscriptions are released on decision, failure or disposal. Early metadata retains normalized name/version only; more than128 candidates or64KiB fails explicitly as startup metadata overflow. These transport bounds do not change version-support or proof budgets.

The status summary distinguishes document compilation/queue/running phases from reported function outcomes. Completion counts include reported proved/direct-correct/failed outcomes, not a count of kernel proofs; unknown, unsupported, stale, cancelled, skipped and audit-qualified results stay explicit. Direct checks are labeled separately. Status packets carry source hashes and reopen synchronization identities. The menu offers local output inspection and a repository-derived issue draft with current version metadata and no automatically attached source; it never submits the issue. Qualified status actions open the project documentation index and proof guide; this does not submit an issue or supply missing proof metadata.

## Testing hierarchy and editor context

Accepted function results appear under their current compiler symbol ancestors when matching symbols are available. A row verified in a derived contract can refer to a base declaration; its label retains the verification contract and its description identifies that distinction. Missing or historical symbols use a labeled result grouping without inventing parent locations. Parent selection and exclusion apply to their descendants.

The trusted Solidity-file context menu exposes compiler-AST Build/import options, concrete typed-model Run/Test, verification, discovery, cancellation, output, status and restart actions. Compiler artifacts and concrete outcomes remain distinct from verification. Positioned verification traces and full Dafny command equivalence remain incomplete.

Owned worker retirement now waits for closure before reusing capacity. The matching local server/client negotiate process ownership for compiler workers and builds; an existing build command starts only after ownership acknowledgement. Cleanup failures remain visible and can block replacement admission. Legacy servers/platforms without these ownership observations do not establish the same crash-cleanup guarantees. This lifecycle infrastructure does not certify proofs, solver retention or rendered Dafny parity.


### Concrete execution contract (human decision Q-CLI-01)

Build Compiler Artifact saves the current file and runs the pinned compiler,
writing an AST plus source-hash manifest under
`solidityLean.compilerOutputDir` (default `bin`, relative to this file's workspace folder, or an absolute path). Each build writes a fresh source-named child directory; the report records that directory and the source hash. This setting affects Build and custom Build only; concrete Run/Test retain their existing artifact storage. It does not prove obligations or claim an EVM
binary. Concrete Run uses the existing `scripts/solidity-lean.mjs run` typed-model
executor (`Solidity.Frontend.Cli`), with an explicit `Contract::function(signature)`
selection and JSON arguments (booleans or exact integer strings). Initial state
defaults to that CLI's empty state; concrete JSON test cases can specify its
primitive storage/transaction state. Constructor calls and unsupported model
inputs remain unsupported; execution is not kernel proof or EVM equivalence.

Concrete Test reads a user-selected JSON file:

```json
{"schemaVersion":1,"cases":[{"name":"increment","target":"Counter::inc(uint256)","args":["1"],"state":{"storage":{"count":"41"}},"expect":{"status":"ok","text":"ok\nreturns 42\ncount = 42"}}]}
```

The example's exact text must match that contract's actual CLI result. Each case
executes independently in the typed model and compares exact status/text;
`unsupported`, `error` and `diverge` never pass. Expected `revert`/`panic` may be
asserted explicitly. No test success is published as verification evidence.
Cases share the existing overall command timeout; jobs are canceled on edit,
close, relevant resource configuration changes or extension disposal. Save/prompt
ownership and stale results are checked. Custom include-path/remapping settings
are explicitly refused for concrete CLI execution until that public CLI exposes
them; compiler Build supports the existing compiler configuration.

Proof-help offers the project documentation index (`docs/README.md`) and proof
guide (`docs/calculus.md`). No proof-help exclusion or parity waiver follows.

Build uses **Ctrl+Shift+B** (**⇧⌘B** on macOS); Run uses **F5**; concrete Test uses
**Shift+F5**. These bindings apply only to a focused, file-backed Solidity editor
in a trusted workspace and invoke the documented compiler-AST/concrete typed-model
commands. They do not turn compilation or concrete tests into proof results.
Custom compiler import options use **F6**. Verification-trace shortcuts remain unavailable without a positioned producer.

The existing parity launcher supports `--suite commands --targets local` for a
native Linux Ctrl+Shift+B observation in real VS Code. It starts with an unsaved
buffer containing Unicode text, checks saving as UTF-8 with CRLF line endings,
verifies compiler AST source identity, and captures the renderer. UTF-16 describes
LSP position units, not the file encoding. Automatic verification is disabled.
This suite does not measure proof
performance or establish Dafny compile/run/test equivalence; Run/Test and macOS
key dispatch still require native observations.

**Build Compiler Artifact with Import Options** (**F6**) accepts a JSON object
containing only `includePaths` and `remappings`, initially populated from this
resource's settings. For example:

```json
{"includePaths":["vendor with spaces"],"remappings":["alias/=lib/"]}
```

Omitted fields retain resource defaults; an empty array clears that field for
this invocation. Relative include paths resolve against the project root and
are passed as absolute paths. The command does not modify workspace settings.
Unknown fields, runtime/proof options and malformed values are rejected; no
shell string is executed. The artifact is a compiler AST, not a binary or proof.
This finite JSON contract differs from Dafny's arbitrary custom CLI string;
full custom-build equivalence and native F6/macOS observations remain open.


Offline CI without H44 data may run `node vscode/parity/discover.cjs --check`
and `node vscode/parity/audit.cjs --check`. They explicitly report **digest-only**:
the committed inventory descriptor and restore manifest are consistent, but full
feature/source/evidence reconciliation did not run. With a full payload present,
these commands perform their original full checks; corrupt or symbolic paths
fail. `--check-source`, `inventory-check` and `parity-gate` always require the
checksum-bound full inventory and remain failing when it is absent.

Native hover and large-file recording tests explicitly skip only when their
entire H44 input set is absent. Partial, malformed or linked recordings fail.
Injected transport and assertion-rejection tests run without that data and do
not certify compiler, proof or rendered correspondence. Restore both bulk
bundles for the complete parity checks. A script-only CI pass does not establish
parity, runtime equivalence or a kernel proof.


The existing native launcher also supports `--suite custom-import-actions` with
one worker/obligation and one trial. It is a separate compiler-only import
fixture; the annotated `custom-commands` fixture remains unchanged and its
admission failure remains recorded. The local case accepts resource-scoped
include paths/remappings from the actual F6 prompt, observes cancellation and
its save, then makes a new dirty edit before the accepted Build. URI, version,
source-object session, exact source/dependency bytes and artifact receipts are
checked. The paired Dafny case preserves its default CLI build arguments and
records actual terminal output/exit and compiler artifacts. Both cases capture
real menus, DOM, accessibility and screenshots in a trusted file workspace.
Untrusted/untitled/menu-click variants, upstream cancellation and macOS remain
separate unfinished observations. These instrumented trials do not establish
proof performance, EVM equivalence or complete menu/trace parity.

Starting another source command now retires the invalidated older command
before asking a prompt that might be cancelled. Retirement still uses the
existing ownership checks and deadline; new work cannot bypass a failed cleanup.
