# Optional EVM reference replay

This Node package executes pinned compiler bytecode separately from Lean source
replay. Source, lockfile and tests define its admitted vectors and settings.
A reference match does not prove compiler correctness or discharge a Lean
import gap.

```sh
npm ci --ignore-scripts --prefix scripts/evm-reference
SOLC_REFERENCE=/path/to/pinned/soljson.js \
  node --test --test-concurrency=1 scripts/evm-reference/{replay,payment-replay}.test.mjs
node scripts/evm-reference/replay.mjs --compiler /path/to/pinned/soljson.js \
  --filter EXACT_PINNED_FIXTURE_PATH --out .lake/reference-result.json
```

The runner authenticates snapshot/compiler identities. `--filter` selects an
exact fixture path. Keep output separate from historical upstream results.

The test host uses Osaka, a 1,024-word stack and the upstream 100-million gas
allowance. Code/initcode size caps are disabled to match the upstream test host;
this is not mainnet deployment behavior. The separate five-million-instruction
host limit and process timeouts are blocked/inconclusive outcomes, never EVM
failure observations. Unknown settings, exceptions or unadapted observations
remain blocked. Preserve actual return/revert bytes and complete profile/vector
denominators.

Generated differential cases use `generated.mjs`; payment vectors use
`payment-replay.mjs`. Their source and tests define options. All reference
results remain executable observations rather than kernel proof substitutes.
Use the repository's writer lock/resource limits and keep caches on disk.
