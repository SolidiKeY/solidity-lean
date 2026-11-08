# Solidity Lean extension

Run **Solidity Lean: Verify File** in a Solidity buffer. **Discover Obligations**
lists functions; the Testing view selects a file or overloaded function.
Results use the exact unsaved buffer. Edits invalidate old results.

Ordinary compiled checks return correct, wrong with a model counterstate, or
unknown. They trust the verifier executable and do not produce a fresh Lean
certificate. `certify: true` selects the separate certificate-producing backend
path. Neither a counterstate nor a successful diamond establishes constructor
reachability; ordinary diamonds accept exhaustion. See
[correctness.md](../docs/correctness.md).

## Setup

Install Node.js and use a matching packaged verifier. Certificates or verifier
builds also require the pinned Lean/Lake and Solidity compiler; see
[solidity-testing.md](../docs/solidity-testing.md). Open the repository as a
trusted workspace or configure `solidityLean.backendPath` and, if necessary,
`solidityLean.nodePath`. Settings and commands are authoritative in
[package.json](package.json).

```sh
code --extensionDevelopmentPath=/path/to/solidity-lean/vscode /path/to/solidity-lean
# From vscode/:
npx @vscode/vsce package
```

Build native/browser runtimes with the instructions in
[compact-verifier.md](../docs/compact-verifier.md). Packaged runtimes must retain
their dependency licenses and current source/toolchain hashes.

## Tests

From the repository root:

```sh
node --test vscode/test/*.test.cjs scripts/source-locations.test.mjs
```

Compiler-backed language-service integration checks require the existing pinned solc setup:

```sh
SOLKEY_ROOT=/path/to/solkey npm --prefix vscode run test:compiler-ranges
```

This command fails if the compiler or its checksum pin is missing; it does not build Lean.
The ordinary unit-test command above needs no compiler for its source-range refusal controls.

Real-backend tests additionally need the built `Solidity.Frontend.Testing` API
and compiler setup. Follow the guarded build workflow in
[contributing.md](../docs/contributing.md). Optional comparison tooling is in
[vscode/parity](parity/).

For the existing bounded `contribution-menus` runner, `--menu-anchor visible-scrollport-v1`
selects H199's separate editor-scrollport admission. It retains the original mouse
point and three-second readiness deadline, requires observed clipping and owned
`elementFromPoint` hits in two observations before mouse press, and records raw
probe failures. The original press/release sequence then opens the menu; a menu
overlay is never admitted as an editor hit.
Omitting the option retains strict full-rectangle admission. Tabs keep their strict
public-resource checks; trust-transition/recovery runs reject this option. DOM
endpoints do not certify raster glyphs or mutation ABA, and this option does not
waive the original failed run or either independent row judgment.

Compiler quick fixes support `codeAction/resolve`. Wire clients retain eager
edits for compatibility; the VS Code provider defers branded actions and resolves
them against the latest listing and current source, diagnostics and dependencies.
Expired or unknown handles refuse edits. This is compiler-action support, not
Dafny proof/plugin action equivalence.

The existing native runner's `--suite compiler-code-actions --targets local`
observation requires one worker/obligation/trial, zero warmups and protocol on.
It reuses the original `Fixes.sol` fixture and records actual VS Code provide,
resolve and apply APIs plus owned LSP traffic, stale refusal and byte restoration.
It does not certify a rendered lightbulb/menu, raster identity or proof outcome.

Document language services and source commands require a file-backed Solidity
document in Solidity language mode. Changing a `.sol` editor to plaintext stops
automatic document work and removes its document providers; global workspace
symbol search keeps its existing resource configuration.

`--suite editor-language-scope --targets local,dafny` records public language
changes, symbol APIs and owned LSP traffic for source/plaintext/restored phases.
Use one worker/obligation/trial, zero warmups and protocol on. Each target keeps
its original fixture and settings; this API observation does not certify rendered
UI, verification outcomes, runtime equivalence or whole parity.

That suite also observes calls to registered document-symbol providers, retaining
source sessions and public close-event counts without replacing their returned
promises. These diagnostics do not prove which result the aggregate symbol API
consumed. Unknown return objects and recording failures remain explicit; the
strict request-correlation check is unchanged.

`--suite workspace-symbols --targets local,dafny` uses the original one-function
fixtures for ordered function/absent/function workspace-symbol API queries.
Use one worker/obligation/trial, zero warmups and protocol on. Raw API diagnostics
and owned process/source/session protocol records remain separate from rendered
search, cancellation UI, verification and the original row judgments.

`workspace-symbols-resolved` is a separate readiness-bound case: it waits within
the original operation deadline for the current source's actual compiler-ready
notification (local) or `ResolutionSucceeded` notification (Dafny) before querying.
It keeps the immediate-query case and its failures separate. Resolution readiness
establishes neither a verification verdict nor whole-row parity.
