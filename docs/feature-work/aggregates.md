# Aggregates

Inline arrays, fixed memory snapshots, reference tuples and slice effects.
Inventory status: partial. Primitive slice materialization, internal
passing/returns and hashing are in
[calldata-slice-copies.md](../calldata-slice-copies.md); calldata aliases in
[calldata-slice-copies.md](../calldata-slice-copies.md#calldata-origins-and-aliases).

## Supported

- **Inline arrays** allocate fixed memory, then evaluate and store each element
  in source order. The type starts at the first mobile element type and folds
  Solidity's implicit common type, independently of the target (`[1,256]` is
  `uint16[2]`; a `uint16[2]` target does not make `[1,2]` stop being
  `uint8[2]`). Numeric, Boolean, fixed-byte, finite nested-array and struct
  elements. Storage reference elements copy at each element's evaluation;
  memory references alias (`Examples/Tactics/Aggregates.lean`,
  `AggregatesImport.lean`).
- **Fixed memory snapshots** (`Src.fixedCopyMem`, with its `MPath` and
  `FixedCopy` witness) compose memory-to-storage copying with the fixed-shape
  conversion; `Src.lower_valueT` and `Src.valueT_wk` cover them. They may copy
  into compatible dynamic or longer fixed storage arrays, reference pushes and
  deferred getter receivers. Storage value copies may widen numeric element
  widths; aliases and memory bindings keep exact shapes. Evaluation stays after
  the receiver's effects when the native receiver statement defers it.
- **Tuples.** Local memory and storage-alias tuple targets capture every RHS
  reference before rebinding. Calldata read-only propagation includes nested
  assignment roots and is computed to a finite fixed point.
- **Slices** (`Examples/Tactics/AggregateSlices.lean`). The base is captured
  before the endpoints and stays stable through rebinding; nonconstant bounds
  are read once; relative bounds are checked before outer offsets are added.
  An invalid relative index uses the base's out-of-range index, so the bounds
  `Panic(0x32)` is kept without evaluating an overflowing offset. Endpoint range
  failures are ordinary reverts. Legacy schedules right-first and via-IR
  left-first. Reference: solc 0.8.38
  `YulUtilFunctions::calldataArrayIndexRangeAccess`.
- Reference pushes check captured source widths against the receiver or the
  deferred getter's return metadata.

## Refused, and why

- Byte-width widening in a snapshot copy: it needs shifting values.
- Multiple nonlocal, effectful/dependent and duplicate tuple targets.
- A whole literal as an assignment target (indexed temporary elements stay
  writable).
- The generic fixed-copy adapters are Lean-only: the KeY fragment and the EVM
  compiler exclude them, as they exclude the storage fixed-copy adapters.

## Cost

Stable slice captures and relative checks made a nested slice read cost more
to check (one sample: 0.90 s to 1.06 s); no heartbeat limit was raised.

## Left

- Reference-element slices, general writable whole-calldata copies, external
  calls with reference arguments.
- Heterogeneous reference-return tuples (a function-return interface).
- Nominal enum/UDVT and function-valued element identities; recursive shapes
  ([recursive-types.md](recursive-types.md)).

## Group 07 upstream repair (2026-10-26)

The following records the initial handoff at `3a6a037d`. The continuation
below supersedes its remaining-gap and final-validation status.

This lane starts at `006fcd593f5beeb540e7adf2bc76de4638566924` on
`group07-tuples-references`. The historical corpus reports remain unchanged.
All eleven assigned fixtures were reproduced independently before editing,
with `--batch-size 1`, their full snapshot paths, and separate output directories.
Every fixture still had frontend gaps in both required source pipelines.
The attached managed executor passed Lean 4.24.0, Lake 5.0.0 and
`lake build Solidity.KeySort`; the archive verified all 11,622 files.

The lowering now uses existing intrinsic statements for tuple conditionals,
reference-valued empty push operands, discarded unary expressions and scalar
local deletion. Literal-string conditionals use a fresh memory binding and evaluate only the
selected literal branch. Tuple RHS values are captured before primitive overlapping
writes, whose order is right to left. The new overlapping-target path accepts
only names, fields and literal indices; general dependent/effectful LHS
locations still need typed location captures. Reference alias restrictions and
mixed storage/memory conditional rejection remain explicit. Per-component
capture declarations and assignments retain width/shape admission.

Generated push aliases retain complete element shape metadata. A pushed-member
store from a scalar stack local is admitted only when its receiver is pure;
receiver mutation, ordinary calls and callback-capable expressions remain
unsupported there. No runtime representation, calculus rule, core dependency,
axiom, search budget or heartbeat limit changed. These are frontend emissions
of existing statements and their existing soundness theorems.

The upstream replay adapter now resolves generated public getters by source
getter identity and ABI signature. Signature normalization preserves the source
function name byte for byte. Every original stateful observation, constructor,
rollback and required pipeline remains in the runner; unsupported observations
and resource exhaustion retain their original inconclusive treatment.

`Calls.duplicateCallTarget`, `Calls.duplicateStorageTarget` and `Calls.lazyTuple`
prove emitted-program properties for arbitrary typed states, including false
alternative output controls and an untaken division. `Checked.lean` pins tuple
reference-width rejection. The separately compiled `tests/solc/Group07.sol`
uses the SHA-checked 0.8.38 compiler; `tests/upstream/Group07.lean` kernel-checks
its emitted programs, including lazy discarded tuple branches, checked rejection,
unchecked negation, overlapping memory writes, owned strings and push aliases.
Its standalone checked-narrow control uses the existing ordinary-revert guard;
it does not certify Solidity's ABI Panic(0x11) encoding. Its effectful push
receiver remains explicitly unsupported. These certificates
are not a universal source/compiler correctness theorem. Runtime agreement is
observational evidence only.

The read-only finder identified generated push prefixes escaping discarded
components/branches. `localStmt` now isolates and drains each prefix at its
operand position. The independent skeptic confirmed this fix and identified
three further boundaries: getter names containing ABI type spellings, receiver
mutation before reading a local RHS, and nominal/string metadata on fresh push
aliases. All were fixed and inspected again without opening Lean workers.
Getter identity and model-alias rejection are pinned in `Replay.lean`.

Validation and exact per-fixture provenance are recorded in
[`tests/upstream/group07-validation.json`](../../tests/upstream/group07-validation.json).
Long logs are retained under `/workspace/.setup/logs/group07-*` in the managed
executor. Early overlapping build runs produced bus errors and out-of-date
artifact failures; they are inconclusive, not passing checks or demonstrated
model failures. Final validation is serialized over the final source state.

Initial handoff fixture results (each row requires both legacy and via-IR):

| Path under `test/libsolidity/semanticTests/` | Before | After |
|---|---|---|
| `array/push/push_no_args_struct.sol` | broken | working |
| `builtinFunctions/erc7201_param_ternary_operator.sol` | broken | working |
| `expressions/conditional_expression_storage_memory_2.sol` | broken | explicit unsupported mixed-reference join |
| `expressions/conditional_expression_tuples.sol` | broken | working |
| `expressions/tuple_from_ternary_expression.sol` | broken | working |
| `variables/mapping_local_tuple_assignment.sol` | broken | working |
| `viaYul/comparison_functions.sol` | broken | working |
| `viaYul/conditional/conditional_tuple.sol` | broken | working |
| `viaYul/local_tuple_assignment.sol` | broken | working |
| `viaYul/negation_bug.sol` | broken | working |
| `viaYul/tuple_evaluation_order.sol` | broken | working |

None was already fixed on the starting master. The mixed-reference row remains
`broken` with its explicit frontend gap in the runner, not passing or silently
excluded. There are no adapter/resource-blocked rows in the final isolated run.
Earlier resource/artifact failures remain in their separate output directories.
The prior isolated commands took 3.04–4.75 seconds per fixture, including both
pipelines, with unchanged 120-second process limits and loop fuel 1,000. These
are wall observations, not a controlled before/after performance benchmark.

The lane has no dependency on unpublished group changes. Integration touches
shared frontend/elaborator files and the narrow getter lookup in
`Tools/Upstream.lean`; adjacent edits to tuple admission, ternary hoisting or
source-signature lookup require ordinary merge review. The optional Bridge and
obsolete SolKey reader are unchanged. No pushes or merges to master are made.

The native indexed-push control uses `(rows[i++].push)()` and proves that
`i` increments once. The importer's unparenthesized indexed push-call spelling
remains an explicit printer gap; its unsupported report is pinned separately.
Six kernel-certificate headlines and all three universal tuple theorems have
only `propext`, `Classical.choice` and `Quot.sound` in their axiom sets. The
trust inventory's full 25-finding list is identical to starting master. Lean
MCP diagnostics are unavailable; configured per-file Lean commands use
`--tstack=131072`. A refreshed fixture run after updating the obsolete source
rejection pin took 5.88–10.78 seconds per fixture with the broad build running;
its source/model hashes are the final hashes in the validation JSON.

Final gate outcome: the full frozen corpus check passes with
`LEAN_NUM_THREADS=1`: all 774 obligations retain their scoreboard, generated
modules and verdicts, and `SolidityCorpus` builds. Replay and all ten emitted
program certificates pass on the final source. The strict automation, module
reachability, layering and upstream Node tests pass. The frozen sort checker
matches all 131 read-bearing annotations across 377 parsed taclets.

The full default library gate is **blocked, not passed**. Combined proof work
first reached less than 1 GiB available executor memory; the owned
`DecisionArrays` worker was stopped, and the corpus's `Derived17` worker was
also stopped when pressure returned. A serial single-thread corpus retry
subsequently passed, including `Derived17`. The serial full-library retry was
then interrupted by a managed executor reconnect while `DecisionArrays` was
still incomplete. Its source is byte-identical to starting master, but a
controlled baseline performance comparison was not completed, so this resource
cost is not classified as an unrelated baseline failure. No heartbeat, search
or proof limits were raised, and no interrupted build is counted as a pass.

After reconnection, `lake build Solidity.KeySort SolkeyTestSuite` passes
(249 jobs), and the rebuilt frozen sort checker passes. Final read-only finder
and independent skeptic reviews found no new concrete code defect; both
confirmed fixture/evidence hashes without opening Lean workers. Their stale
build-status and timing-label findings were corrected before the handoff.

## Group 07 continuation: mixed references (2026-10-27)

This continues the same `group07-tuples-references` lane from `9c8b45d4`
and `3a6a037d`; no restart, push or master merge is involved. The original
review patch remains byte-identical (SHA-256
`b55bde20dafadca8a13ae7967c1799ad06f7f2d69d77c7353498f56ae46d16c4`).

The final assigned import gap is implemented using existing intrinsic memory
statements. Both branch endpoints must agree as `RefTy`, transported by their
checked equality, and their complete width/nominal shape metadata must agree.
The join is memory: its selected storage operand is copied at that evaluation
point; its selected memory operand aliases the existing object. A fresh default
object seeds the join without reading an untaken, possibly invalid path; it is
unreachable after rebinding. Existing `mapFree` and `defaultOkS` admission remains.
No runtime representation or external dependency changed.

Nested/effectful branches are lowered inside the selected typed branch. Type-only
probes restore both local/capture state and `CallMemo`, so they neither emit
runtime effects nor retain speculative declaration identities. Complete metadata
is restored before checking branch assignments. A storage-returning call used
as a memory value now captures its typed storage result and copies it; the
reference-call statement shortcut no longer treats it as memory-returning.
Condition, receiver/index and selected calls are evaluated once.

The independently proved `CloseS.readId_copySt_fixed` fills the precise closer
gap found by the universal snapshot control. For every typed heap, fixed-array
length, primitive type, source value and index, reading the copy returns the
source word, or exactly `none` past bounds. Its proof reuses the typed mirror
relation; it does not infer an unrestricted dynamic-array shadow read. It is a
Lean-only fixed-array specialization of `readFromCopyToStorage` and is recorded
in the rule map. The rewrite removes the copy/read head and has no reverse
rule or expanded search budget. Its axioms are only `propext` and `Quot.sound`.

`Group07Mixed.sol` is separately compiled with the SHA-checked 0.8.38 compiler
into distinct legacy/viaIR ASTs with real compiler provenance. All 22 source
certificates pass, covering memory identity, storage snapshots in both arm
orders, lazy invalid paths, exact selected failures, one condition evaluation,
effectful indices, nested joins, selected storage/memory-returning calls,
string metadata and copied-array bounds. The three universal emitted-program
properties (identity, snapshot and bounds failure) pass with only `propext`,
`Classical.choice` and `Quot.sound`. Local arithmetic helper proofs keep the
original bounds property and heartbeat limits. Ordinary writable calldata
escape and mismatched reference widths remain explicit negative controls.
Failure controls certify the model's existing revert/panic classification,
including its bounds-as-revert reading; they do not certify Solidity ABI
Panic codes or data. These checks do not claim universal source/compiler equivalence.

Finder and skeptic reviews used no Lean workers. They confirmed two issues
which were fixed before validation: restoring the second state layer during
probes, and installing full shape metadata before branch assignment checks.
They then reviewed the call-copy path and generic copy law without finding a
further concrete defect. A documentation escaping typo was corrected. Distinct
legacy/viaIR wrapper hashes were independently checked against their own ASTs.

All eleven assigned fixtures now pass every original observation in both required
pipelines. The ten previously fixed rows retain identical observed vectors;
all 60 final observations are recorded. No assigned row is blocked or excluded.

| Path under `test/libsolidity/semanticTests/` | Lane at `3a6a037d` | Final legacy / viaIR |
|---|---|---|
| `array/push/push_no_args_struct.sol` | already fixed | working / working |
| `builtinFunctions/erc7201_param_ternary_operator.sol` | already fixed | working / working |
| `expressions/conditional_expression_storage_memory_2.sol` | broken: mixed reference join | working / working |
| `expressions/conditional_expression_tuples.sol` | already fixed | working / working |
| `expressions/tuple_from_ternary_expression.sol` | already fixed | working / working |
| `variables/mapping_local_tuple_assignment.sol` | already fixed | working / working |
| `viaYul/comparison_functions.sol` | already fixed | working / working |
| `viaYul/conditional/conditional_tuple.sol` | already fixed | working / working |
| `viaYul/local_tuple_assignment.sol` | already fixed | working / working |
| `viaYul/negation_bug.sol` | already fixed | working / working |
| `viaYul/tuple_evaluation_order.sol` | already fixed | working / working |

Final isolated commands took 3.26–5.06 seconds per fixture, with process limits
120 seconds, batch size one and loop fuel 1,000 unchanged. This is not a
controlled performance comparison. Final model SHA-256 is
`19ae854dcfcc11baa01898ac1164793365aba291a7401c311453a3ee9e80999b`.
Exact commands, source/compiler/archive/runner/model hashes, complete before/
after reports, prior handoff evidence and control hashes are in the validation
JSON. The pinned archive, historical results and all upstream expectation bytes
remain unchanged.

The frozen corpus gate passes on the final model: all 774 obligations retain
exact classifications, generated files and scoreboard have no drift, and the
257-job `SolidityCorpus` build succeeds. The previously interrupted `Derived17`
passes in 116 seconds when built alone. Existing replay, the prior ten source
certificates and the new mixed-reference certificate file all pass again.
Strict automation, reachability, layering and the 14 upstream Node tests pass.
The full trust finding list remains identical (25), and the same 13 missing
vendor/external documentation references remain.

The first resumed full-library gate exhausted its 5,400-second outer wall
allowance at unchanged `DecisionArrays`; this attempt is incomplete, not a
pass. `DecisionHashes` (288 seconds) and `Decision` (780 seconds) had passed.
The serial cache continuation with a 3,600-second outer allowance passed in
2,338.46 seconds: default library 649 jobs, `SolkeyTestSuite` 249 jobs, and all
377 frozen sort taclets (131 read-bearing). `DecisionArrays` passed its exact
`["proved", "refuted", "proved"]` verdict pin in 2,262 seconds; `DecisionMemory`
then passed in 59 seconds. No full-gate result remains pending. Direct file-backed
profiling established that `DecisionArrays`' theorem checks finish in about
1.2 seconds or less; its final verdict evaluation is the slow stage, consistent
with the historically documented roughly 1,500-second cost in
`docs/automation.md`; that estimate is not a controlled comparison with this
cloud run. An admission-only diagnostic found that only the array-block
reduction accepts each of the three formulas, excluding the suspected earlier
pipeline countermodel path as the cause here.
`Elab.async false` stays unchanged because history records stack overflow with
concurrent verdict evaluation. No proof, heartbeat, fixture timeout or loop-fuel
limit was increased. Both status files and complete logs are linked in the JSON.

Long builds use one worker. The existing corpus probe unconditionally launches
its contract probes with `Promise.all`; at least three short-lived Lean
processes were observed before they finished, exceeding the requested two-worker
cap despite `LEAN_NUM_THREADS=1`. This exception is recorded explicitly; there
was no overlapping library build, and subsequent phases returned to one worker.

Final read-only evidence review found no remaining concrete defect. The finder
matched all current reports, hashes, observation vectors and preserved inputs;
the independent skeptic matched proof counts, axiom audits, failure boundaries
and remaining exclusions. Neither opened Lean workers. The implementation is
committed locally as `391a5a74`, following preserved `9c8b45d4` and `3a6a037d`;
the final follow-up records validation only. No push or merge is performed.
