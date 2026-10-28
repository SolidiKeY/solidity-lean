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


### Step 4 increment: unsigned-power self-call data (2026-10-28)

Starts at current master `f4dee4a29c2e208b36db4a4161a4723c735cd775`, on
`codex/revert-payload-settings`, in its own managed clone. This increment
extends existing unsigned-power lowering and byte transport; it adds no
statement, halt, rule, panic representation, dependency or source profile.
Group 10's adapter/checkpoints and recursive graph migration are untouched.

**Implemented.** Default checked unsigned `**` in an ordinary self-call frame
now uses the existing retained-entry expansion: capture both operands in the
pipeline order, handle zero/one/exponent-zero after evaluation, reject the
256-bit cutoff with literal `Panic(0x11)`, and otherwise use checked
multiplications. Local declarations, assignments, nested binary expressions,
internal callees, selected short-circuit/conditional arms and array indices
reach that expansion. The new eligibility helper only requests existing
lowerings; untaken arms remain untaken. An earlier operand or nested array
base is captured before newly inserted guards, preserving its failure priority.

`tests/solc/SelfPowerData.sol`, its two pinned ASTs, and
`Solidity/Examples/Tactics/SelfPowerData.lean` cover cutoff and actual
multiplication overflow, narrow overflow, fitting powers, shortcut operand
failures, pipeline-specific competing failures, complete 36-byte raw data,
rollback and successful writes. Wrong code/raw-byte/priority assertions remain
failing controls. Completed finite kernel runs are transported by
`Prog.runF_approx`; exhaustion cannot establish their return conclusions.
These are concrete certificates, not a universal source/compiler or generated
loop equivalence theorem. Existing mathematical recurrence/cutoff proofs remain
in the [historical Group 10 M5 controls](abi-hashes.md#m5-repair-the-five-admitted-execution-mismatches-2026-10-27).

**Review.** Independent read-only finder and skeptic reviews, without a Lean
server, identified and resolved three issues: restrict the new top-level route
so signed and explicit checking modes retain their reading; capture earlier
reads before later inserted guards; and cover pure powers skipped by
conditional/index triggers. The original return-ternary shape already passed;
the new ternary fixture targets a local initializer instead. Both selections
and earlier-base bounds failure are tested. A recursion-depth diagnostic while printing a failed finite certificate was
traced by executing it: the nested via-IR shape was actually failing. The
missing hoist was repaired without raising any proof or recursion limit.
Final code reviews found no remaining confirmed defect.

**Remaining scope.** No new panic code or `revertStrings` setting is admitted.
Signed magnitude-overflow payloads remain limited; explicit `checked` and
`ignoringOverflow` modes keep their existing policy. Failures outside self-call frames and without retained-entry observation
keep their prior abstract halt/data reading.
Allocation `0x41` is not implemented: resource exhaustion stays distinct and
`THalt.exhausted` policies are unchanged. Malformed-storage `0x22` remains tied
to excluded low-level corruption; no new `0x00` case is claimed. The source
provenance boundary still rejects `debug.revertStrings` as an unknown compiler
setting, and the upstream runner retains `unadapted fixture setting:
revertStrings=debug`. Explicit default/strip/debug/verbose-debug settings are
not added by this increment; omitted default settings continue to work.
Full coverage-plan step 4 remains partial.

**Compiler evidence.** `scripts/check-self-power-data.mjs` pins solc 0.8.38 and
checks exact bytes and exception status under legacy and via-IR. It also
preserves every original observation of upstream `tryCatch/panic.sol` and
`revertStrings/empty_v2.sol`, forwarding the latter's debug setting only to the
compiler. Those EVM observations do not certify Lean support for that setting.
AST analysis uses optimizer disabled; reference EVM runs use optimizer enabled,
both recorded explicitly. Historical Group 10 reports are unchanged. New
before/after, command, resource, compiler and final validation evidence belongs
in `tests/upstream/revert-power/`.
