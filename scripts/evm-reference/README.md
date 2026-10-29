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

`--filter` requires one exact pinned semantic-fixture path. The archive and all
11,622 source files are verified before execution. The compiler bytes and full
version are checked. Each required legacy/viaIR pipeline compiles independently
with optimization disabled and CBOR metadata omitted, executes creation code,
and retains every supported ABI vector in order. Canonical compiler method
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


The direct-self-try reference adapter records and checks the actual deployment
address. Its opt-in `direct-self-try-reference` context permits non-scalar
callee signatures and recursively whitelisted memory/arithmetic/return/revert
Yul in compiled bytecode only. Native Lean replay rejects that context kind.
Constructors/effectful initializers and context/world instructions remain
refused. Supported raw calldata vectors compare complete expected ABI or revert
bytes; wrong bytes and invalid byte values are negative controls. Existing gas,
instruction, settings and expectation policies are unchanged. The
[conditional try/catch record](../../docs/feature-work/diamond-try.md#human-approved-conditional-account-and-native-adapter-repair)
separates sixteen original reference passes from four native passes and records
the remaining blocked pipelines and model decoder boundary.


The creation-try source context additionally records actual nested CREATE receipts
(address, actual failed halt/revert bytes or runtime code hash/size). This is
compiled-bytecode evidence, separate from kernel proofs and native source
admission. It does not enable a historical profile or alter panic decoding.


Linked-try replay admits the exact validated library directive, deploys the real library then links/deploys the caller on the same machine using pinned compiler linkReferences. It records actual code/delegate context and full return/revert bytes, including prerequisite receipts on failed checks. This is separate compiled-bytecode evidence; no historical profile or general library/ABI admission is enabled.
