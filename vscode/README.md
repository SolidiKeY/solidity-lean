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

Real-backend tests additionally need the built `Solidity.Frontend.Testing` API
and compiler setup. Follow the guarded build workflow in
[contributing.md](../docs/contributing.md). Optional comparison tooling is in
[vscode/parity](parity/).
