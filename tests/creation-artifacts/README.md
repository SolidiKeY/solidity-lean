# Creation artifact vectors

From the repository root, install the locked external test dependencies before
running the vector gate:

```sh
npm ci --ignore-scripts --no-audit --no-fund --prefix tests/creation-artifacts/evm
node scripts/check-creation-artifacts-vectors.mjs
```

The runner resolves packages from `evm/node_modules`, which is ignored by Git.
Repeat the install in each fresh checkout; no `NODE_PATH` is required. These
packages are test dependencies only and do not enter the Lean package.

The 16 Osaka CREATE transactions check installed runtime code or exact revert
bytes against `vectors.jsonl`, exported by `Export.lean`. A missing dependency
fails the gate before any transaction runs. Passing these finite external
tests does not establish whole pinned-EVM or source preservation proofs.
