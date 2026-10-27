# Solidity Lean Verification

Verify saved Solidity files with the repository's compiler frontend and
kernel-checked Lean proofs. Run **Solidity Lean: Verify File** from the Command
Palette. **Discover Obligations** lists functions without attempting proofs.
The Testing view can run a file or an individual overloaded function.

Pending obligations appear as warnings: they are open proof goals, not certified
counterexamples. Import gaps, interrupted runs and backend errors remain visible.
Hover over a function to see its result and obligation reading. Edits clear
obsolete results and cancel verification. **Cancel Verification** stops active
jobs; verify-on-save is optional and disabled initially.

Enable `solidityLean.auditPreconditions` to check that specified functions have
possible entry states. A proved postcondition with an impossible entry is shown
as a vacuous-specification warning. Unknown audits require attention too. This
option is off by default and discovery does not run audits. See the repository's
verification notes for the certificates and their model limits.

Enable `solidityLean.counterexamples` to search open goals for a certified model
prestate. A refuted result is an error diagnostic and a failed test. Its hover,
output and failure details show the model parameter names, exact decimal values,
initial model state and certificate declaration. Source names appear only when
the backend provides a declaration mapping. These certificates concern the
verification model; constructor reachability is a separate property. Discovery
does not search for model prestates. The option is disabled initially.

Proof status refers to the selected obligation. Ordinary box proofs establish
partial correctness. Supported ordinary diamond loops check tuple `decreases`
annotations for defined components and strict lexicographic decrease after every
successful body turn. Unsupported shapes remain pending. Ordinary diamonds
accept exhaustion; separate successful-termination certificates are described in
[the loop notes](https://github.com/SolidiKeY/solidity-lean/blob/master/docs/loops.md#typed-tuple-measures).

## Setup

Install Node.js 18 or later and the Lean/Lake version in the repository's
`lean-toolchain`. Both `node` and `lake` must be on the editor's process PATH.
Follow the repository's compiler setup in
[docs/solidity-testing.md](https://github.com/SolidiKeY/solidity-lean/blob/master/docs/solidity-testing.md),
including the pinned soljson compiler and `SOLKEY_ROOT` when needed. The
extension uses that existing runner; it does not install compilers.

Open the Solidity Lean repository as a trusted workspace, or set
`solidityLean.backendPath` to its directory. Set `solidityLean.nodePath` when
Node is not on PATH. `solidityLean.timeoutMs` bounds the whole verification job
(default 600000 ms); `solidityLean.verifyOnSave` enables automatic checking.
Verification saves a modified file before compiling it.

To try the source extension, launch a development host:

```sh
code --extensionDevelopmentPath=/absolute/path/to/solidity-lean/vscode /absolute/path/to/solidity-lean
```

To build an installable package from this directory:

```sh
npx @vscode/vsce package
code --install-extension solidity-lean-0.3.0.vsix
```

## Tests

From the repository root:

```sh
node --test vscode/test/*.test.cjs scripts/source-locations.test.mjs
node --test --test-name-pattern='editor reports' scripts/test-solidity.test.mjs
```

The first command checks controller behavior and real child processes with a
fixture backend. The second requires the configured compiler and built Lean API.
Run `lake build Solidity.Frontend.Testing` first.

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

This extension provides source verification results. General Solidity completion,
navigation and syntax highlighting can come from another Solidity language
extension. Lean source files retain the Lean extension's proof-authoring tools.
