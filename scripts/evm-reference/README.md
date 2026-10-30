# Optional bounded EVM reference replay

This package executes pinned solc bytecode on `@ethereumjs/evm`, separately from
Lean replay. A reference match does **not** discharge a Lean import gap, turn
model exhaustion into a failure, or prove compiler/model correctness. The core
Lake package remains dependency-free. Install the exact lock with:

```sh
npm ci --ignore-scripts --prefix scripts/evm-reference
SOLC_REFERENCE=/absolute/path/to/soljson-v0.8.38+commit.1835d247.js \
  node --test scripts/evm-reference/replay.test.mjs
node scripts/evm-reference/replay.mjs \
  --compiler /absolute/path/to/soljson-v0.8.38+commit.1835d247.js \
  --filter test/libsolidity/semanticTests/operators/userDefined/recursive_operator.sol \
  --out .lake/upstream/recursive-reference.json
```

The replay and payment regression tests also accept the repository-local
`.lake/soljson/` cache or `SOLJSON_DIR`; `SOLC_REFERENCE` takes precedence.
See [payment test setup](../../docs/solidity-upstream-tests.md#reproduce) for
the exact compiler filenames, unchanged hashes and source-test prerequisites.

`--filter` requires one exact pinned semantic-fixture path. The archive and all
11,622 source files are verified before execution. The compiler bytes and full
version are checked. Each required legacy/viaIR pipeline compiles independently
with optimization disabled and CBOR metadata omitted, executes creation code,
and retains every supported scalar vector in order. Canonical compiler method
identifiers select the bytecode entry. Calls share state; the VM rolls failures
back. Each vector resets transaction warmth and original-storage caches.

The VM uses Osaka, a 1,024-word operand stack, and the pinned upstream
`test/ExecutionFramework.h:275` message-execution gas allowance of 100,000,000.
This is not a reduced gas budget selected to force a failure. Contract/initcode
size caps are disabled explicitly to match `test/EVMHost.cpp:418–441`, which
charges code-deposit gas without enforcing those caps. This is a test-host rule,
not mainnet deployment behavior. No gas/log/environment assertions are adapted.
Host-dependent source behavior, constructor logs, unknown exceptions, unsupported
opcodes, noncanonical ABI, and unsupported fixture settings remain blocked.
Successful creation retains runtime-code length/hash; failed creation retains
its exact return bytes.

A separate five-million-instruction host budget bounds interpreter work. Hitting
it is **blocked**, never `FAILURE`; a process timeout is likewise inconclusive.
For batch work place each exact invocation under a 120-second process supervisor,
retain logs and synthesize a blocked report on timeout. Actual EVM stack-overflow,
out-of-gas and empty-data revert are machine observations, with exact exception,
return bytes, executed instruction count and maximum stack height retained.
Nonempty failure data cannot match an upstream empty-data `FAILURE` expectation.

Reports retain archive, compiler, runner, imported adapter, dependency-lock,
compiler-input, source and creation/runtime-bytecode hashes. Keep reports outside
historical `tests/upstream/results`. Refer to the Group 03 continuation in
`docs/feature-work/numeric-operators.md` for per-fixture Lean and reference results.

## Generated typed differential cases

After `source /workspace/.setup/activate.sh` (or selecting Lean 4.24.0):

```sh
lake build solcases Solidity.Examples.SolCases
lake exe solcases 0
SOLC_REFERENCE=/absolute/path/to/soljson-v0.8.38+commit.1835d247.js \
  node --test scripts/evm-reference/generated.test.mjs
node scripts/evm-reference/generated.mjs --compiler /absolute/path/to/soljson-v0.8.38+commit.1835d247.js --seed 0 --out .lake/generated/seed-0.json
```

The exact pinned compiler hash/version is checked before execution. The optional
`--index N` selects one reproducible case. All four legacy/viaIR × optimizer
off/on variants always run. A failed case shrinks within its template and
boundary pool using regenerated Lean expectations; any mismatch cause is
retained, without claiming cause-preserving minimization. Reports preserve
sources, bytecode, layout, full adapted observations and hashes. Unknown syntax,
layout, exceptions or logs are blocked. No JavaScript arithmetic model supplies
expected results. See [scope and evidence](../../docs/feature-work/generated-differential.md).

Payment-specific replay is additive: `payment-replay.mjs --compiler FILE --filter
EXACT_PINNED_PATH --out FILE` uses the same pinned compiler/snapshot and unchanged
100-million gas / five-million instruction ceilings. It retains constructor or
empty-calldata funding, actual CREATE and receive frames, ordered return/revert
bytes, and every original gas row across required and named optimized profiles.
Gas follows the pinned EVMHost and ExecutionFramework accounting; failed creation
with nonempty output is blocked because its deposit accounting differs from this
engine. Unknown settings/observations and host limits stay blocked. It records
executed frame steps, runtime hashes, compiler inputs and dependency provenance.

This tool supplies independent compiled-bytecode observations, never Lean source
coverage, a callback theorem or a compiler correctness proof. It does not modify
the existing `replay.mjs` host policy or the core payment/callback semantics.
Run `node --test --test-concurrency=1 scripts/evm-reference/{replay,payment-replay}.test.mjs`
with `SOLC_REFERENCE` pointing to the pinned compiler. Keep caches and `TMPDIR`
on disk and run under the documented writer lock and aggregate resource cap.


The upstream source runner uses the payment adapter only after complete-shape
validation in Lean. Whole payment-fixture success requires fresh provenance-
matched reference evidence for both pipelines, every functional observation and
any gas rows; an unmetered typed source match alone stays pending. The SDK is
therefore needed to finish those payment rows, while the Lean core remains
independent of it. Install from this package's lockfile with npm ci --ignore-scripts.
The source witnesses reproduce with scripts/payment-source-fixtures.mjs --check
and SOLC_REFERENCE pointing to the pinned0.8.38 compiler.
