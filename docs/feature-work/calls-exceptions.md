# Calls and exceptions

Eager error and event operands, exact self-call panic and catch data, and
fixed-byte custom-error words. Frontend only: no `Stmt`, `Fml`, `THalt`, taclet
or frame constructor changed, and existing soundness covers the emitted
declarations, branches and literal reverts. Regressions:
`tests/solc/CallExceptions.sol`, `Examples/Tactics/CallExceptions.lean`.

## Supported

- **`require(c, E(args))`** (`RawStmt.requireWith`) evaluates the error's
  arguments on both outcomes. The cheap `require(c)` lowering is kept only when
  every omitted argument is raw-pure and its typed value has `mayHalt = false`:
  `p.x` and `a.length` can fail through unset aliases or memory. A synthesis
  failure in this early check means "cannot omit", not a rejection.
- **`revert E(args)`** evaluates its operands before dropping data; a
  self-frame revert keeps the ABI payload. `eagerArgsWith` finishes one
  argument's hoisting and evaluation before the next. Encoded values are
  captured before later effects; reference operands are always bound, so unset
  references still fail. Captures keep the declared primitive parameter types;
  literals keep their contextual types. A computed string reason is not
  evaluated before a failing condition. Discarded event operands take the same
  path.
- **Fixed-byte error words.** `bytesM` to `bytesN` right-padding is applied
  while source widths are visible, before byte lowering and eager captures;
  `revertErrParts` shifts the compact value to the left of its ABI word with a
  direct 256-bit uint operation. A raw `uint256(...)` cast after hoisting is
  not accepted by `synth`, so the shift must not be written as one. Other word
  kinds keep their encoding.
- **Self-frame panics.** Enum conversion emits literal `Panic(0x21)` bytes and
  the terminal branch of internal-function dispatch `Panic(0x51)`, reaching the
  existing data/panic classification and catch rules. Dispatch evaluates each
  argument once at its formal type before selecting a target.
- **Catch transport.** `TRun.catchBytes_self_data` carries the callee's
  `THalt.ofData d` for any immutable byte list (empty included) at a nonzero
  self address; `TRun.catchData_self_data` connects those bytes with the typed
  catch allocation from the caller's state. Address and decoder premises, the
  allocation and the heap extension stay explicit.
- **Events.** Unqualified direct positional `emit`s resolve their exact
  `EventDefinition`, check arity and evaluate the operands in source order (both
  pipelines); the log is abstract. The `emitArg` theorem pins operand panics.

## Refused, and why

- **Named event argument lists**: solc's order differs by pipeline.
  `emit Seen({second: mark(1), first: mark(2)})` runs 2 then 1 in legacy and 1
  then 2 in via-IR, while the positional form runs 1 then 2 in both. This is
  specific to events, not inferred from binary or `addmod` order.
- Qualified event names; missing, ambiguous or wrong-kind declaration
  identities.

## Cost

Extra captures (error operands, reason conditions, indirect calls) change
printed fresh names and enlarge indirect-call proof terms. Measure affected
examples rather than raising heartbeats.

## Left

- Callback catches, recursive memory returns with owned writes,
  reference-valued function types, static-call world semantics, external
  aggregate return decoding. Unknown memory payloads keep the conservative
  `allocAll`.
- Legacy/via-IR scheduling of the function expression itself (the named-value
  legacy order is kept).
- Observable event logs.
- An ownership-aware callback frame must keep `withinM`; `withinW` admits
  other shapes.

## Reproduction

```sh
node scripts/solc-ast.mjs --compiler-file /path/to/soljson-v0.8.38+commit.1835d247.js \
  --compiler-sha256 6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390 \
  --source tests/solc/CallExceptions.sol --out tests/solc/CallExceptions.ast.json \
  --evm-version cancun --wrapper Solidity/Examples/Tactics/CallExceptions.lean
node scripts/check-call-exception-vectors.mjs COMPILER_FILE EXTERNAL_NODE_MODULES
```

The runner checks complete panic and custom-error returndata for 0.8.38 and
0.8.34, legacy and via-IR, executing installed runtime code at a
non-precompile address. The source's raw-catch checks inspect only length,
selector and code bytes.

### Upstream Group 10: retained payload adapter (2026-10-26)

The Group 10 adapter compares complete retained failure bytes, executes typed
ABI wrappers once, and keeps earlier observations on inconclusive exits.
Canonical aggregate probes run separately and cannot certify lazy decoder
failures. It does not change exception
semantics or infer a concrete panic code from `.panic`. Implementation,
validation, review and remaining scope are recorded in
[ABI M3](abi-hashes.md#m3-upstream-group-10-exact-retained-revert-data-2026-10-26).

### Group 10 external-entry observation (2026-10-27)

The upstream adapter can retain exact source failure data at an external
entry without pretending the call is a self-call. `retainFailureData` is a
separate elaboration policy and a callee-cache identity component; sender,
value, constructor initialization, internal-call order and rollback remain
unchanged. Existing typed panic guards and revert encodings are reused.
`entryProgParts` enables this policy only for the source capture statements;
ABI input/probe/output code retains its ordinary policy. The adapter supplies
checked literals or ABI-decoded locals, not arbitrary failing top-level raw
argument expressions. Generic model panic stays inconclusive.

The guard failure/success/priority lemmas use only standard Lean axioms;
execution controls reject wrong codes, empty or extended payloads and changed
caller/value, and verify rollback after a nested narrow overflow. This adds no
core exception or taclet constructor and does not claim universal solc/model
equivalence. See ABI M4 for the continuation evidence and remaining exclusions.

The complete continuation replay retains 175 agreeing fixtures (57 additional,
zero regressions), 102 failures and 160 blocks across the assigned 437 paths.
Exact before/after observations and every required pipeline are preserved in
`tests/upstream/group10-resume-results.json`; the final validation record is
`tests/upstream/group10-resume-validation.json`. Named-error payload order,
modular-zero and exponentiation panic data remain explicit execution failures,
not exclusions or inferred generic-panic successes.

M5 repairs those five admitted execution mismatches, preserving M4 as a
historical completed replay. Named errors now capture typed operands in the
pipeline order before arranging their final ABI words, with storage aliases
retained until encoding. Modular-zero and checked unsigned power retain their
exact panic data; nominal fixed-byte complement retains its width. See
[ABI M5](abi-hashes.md#m5-repair-the-five-admitted-execution-mismatches-2026-10-27)
for kernel controls, final selected replay and remaining failures. This does
not extend custom-error encoding to arbitrary array or struct arguments.

The Group10 aggregate custom-error continuation is recorded in
[ABI M6](abi-hashes.md#m6-aggregate-custom-errors-and-compound-decoder-metadata-2026-10-27).
It reuses the typed aggregate ABI encoder and raw memory-revert path, preserving
reference locations, delayed reads, source ordering and rollback. Historical
M5 evidence is unchanged; current and retained evidence remain distinct.

## External try execution witnesses

The [partial step-11 record](diamond-try.md) contains deterministic normal-return
witnesses, caller-failure controls and the universal callback-diamond obstruction.
Diamond rules/source automation and the blocked upstream fixture pipelines
remain open; the record does not increase source support.
