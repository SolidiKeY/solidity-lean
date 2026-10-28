# Aggregates

Inline arrays, fixed memory snapshots, reference tuples and slice effects.
Inventory status: partial. Primitive and fixed primitive-row slice materialization, internal
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

- Other reference-element slices (structs and nested/dynamic rows), general
  writable whole-calldata copies, external
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
alternative output controls and an untaken division. `Examples/Tactics/Checked.lean` pins tuple
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

## Coverage-plan step 3: fixed primitive-row slices (2026-10-27)

This independent lane is `codex/step03-aggregate-slices`, based on current
`origin/master` at `f4dee4a29c2e208b36db4a4161a4723c735cd775`. It preserves
cloud groups 01–10 and does not migrate recursive types or repair ABI replay.
The attached managed executor ran Lean 4.24.0 and Lake
5.0.0-src+797c613. The `Solidity.KeySort` smoke build passed. Before editing,
a native fixed-row slice was reproduced as refused while the flat primitive
control was admitted; the checked probe took 1.217 seconds and sampled
737,533,952 bytes peak RSS. The pinned 0.8.38 compiler independently admitted
fixed primitive rows in both pipelines and refused dynamically encoded rows.

`Syntax/Elab/SliceCopy.lean` expands fixed primitive-row elements into fresh
row allocation, an inner copy loop and installation in the result. It uses
existing intrinsic statements and their existing rules/soundness; there is
no new statement, rule, runtime representation or core dependency. Outer
base identity, endpoint captures, relative checks and lazy placement keep
the existing slice lowering. The new source fixture retains every assertion
and is generated independently for legacy and via-IR. Its certificates use
`Prog.runF_approx` through the existing fuel-observation theorem; divergence
cannot satisfy a success or failure observation. They are emitted-program
certificates, not a universal Solidity/compiler equivalence theorem.

Nominal enum/UDVT source slices now retain an explicit refusal before erased
source types can reach the primitive-row path. This conservative source
boundary includes readonly nominal slices. Both nested identifiers and
historical identifier-free type strings are checked. Address rows preserve
the inherited address carrier/ABI marker; payable, contract and native
nominal address separation are not new guarantees. Struct/nested reference
rows, general writable whole-calldata copies, external reference interfaces
and effectful/dependent nonlocal tuple targets remain outside this increment.

Independent read-only finder and skeptic reviews used no Lean workers. Their
confirmed findings were fixed: the rebinding test now uses a distinct shorter
array, and the EVM replay requires the exact `revert` exception rather than
accepting an empty out-of-gas result. They verified per-iteration row freshness,
`[][]` width/byte/address metadata and the source nominal-name fallback.
Rollback is an EVM transaction observation (`invalidRange` followed by
`getMarker() == 0`); the kernel failure certificate alone proves halt class.

Inline arrays containing slice values also retain their independently
inferred element type. The type reader recursively peels only the descriptor,
without evaluating endpoints. A projected inline array obtains its shape
while hoisting; declarations, assignments and reference arguments still pass
strict shape checks before destination/formal metadata can erase the source.
Negative initializer, assignment and argument controls reject width changes;
same-width controls remain admitted. Direct, named and nested source views,
a taken mutator call and an untaken invalid call are all retained.

The final focused build passes in 201.28 seconds with 2,513,592,320 bytes
kernel-charged peak memory. All 30 emitted-program certificates and all 30
axiom audits pass; the sets contain only `propext`, `Classical.choice` and
`Quot.sound`. The separate EVM replay passes 32 observations (16 per pipeline)
in 2.405 seconds with 295,964,672 bytes peak; it retains input words, exact
failure bytes and rollback observations. The 39 affected Node tests pass.
Trust matches all 240 inventoried sites with zero findings, reachability has
702 modules and no orphans, layering has 152 core modules and no front-end
reachability, strict automation has zero pending rows, and generated inventory
checks pass. These are final-source results, not interrupted-attempt evidence.

All six original slice-directory fixtures were reproduced on the starting
commit in this task's own detached worktree. No source/expectation, runner,
archive, pipeline, 120-second fixture timeout or 1,000 loop fuel was changed.
Both prior working fixtures retain byte-for-byte identical observed vectors.
The final replay is 57.7 seconds with 590,249,984 bytes peak and no resource
stop. It exits 1 for three explicitly broken rows; this is not a whole-directory
passing gate. Every required legacy/via-IR variant remains in the reports.

| Original path under `test/libsolidity/semanticTests/array/slices/` | Before | Final legacy / via-IR |
|---|---|---|
| `array_calldata_assignment.sol` | working | working / working |
| `array_slice_calldata_as_argument_of_external_calls.sol` | broken | broken / broken: ordinary calldata return-as-memory refused |
| `array_slice_calldata_to_calldata.sol` | broken | broken / broken: ordinary return copies and struct-element materialization refused |
| `array_slice_calldata_to_memory.sol` | broken: inline slice type inference | working / working: all three original vectors in each pipeline |
| `array_slice_calldata_to_storage.sol` | working | working / working |
| `calldata_array_slicing.sol` | broken | broken / broken: existing printed-text parse refusal (`expected '='`) |

The initial full `run-lean.sh` attempt passed all 687 default build jobs but
hit its unchanged 7,200-second outer timeout during `TestSuite/Derived20.lean`.
That attempt is blocked, not passing: 7,200.130 seconds, 12,884,901,888 bytes
kernel-charged peak, 551 memory-limit events and no OOM kill. An unchanged-limit
cache continuation then passed `run-lean.sh` in 184.408 seconds with
1,250,676,736 bytes kernel-charged peak and no limit/OOM events. It completed
the 260-job `SolkeyTestSuite` target and the actual sort comparison: 377 parsed
taclets, all 131 read-bearing annotations matched. The reports retain both
attempts separately; no timeout or resource stop is counted as passing.
Commands, complete original
before/after observations, all new EVM inputs/results, source/compiler/model
hashes, axiom audits and resource measurements are in
[`tests/upstream/step03/validation.json`](../../tests/upstream/step03/validation.json)
and its linked sibling JSON files. The final model hash is
`be4ab09309dc97d966038e71ca23811a94cae995684ecc9f873506ba957a0818`.
Independent read-only evidence reviews reproduced both model hashes and all
counts without Lean workers and found no remaining code or evidence defect.
The path checker retains exactly the same 20 missing archived/external
references as the starting worktree; these historical records are unchanged.

The VM has no direct systemd scope or writable delegated cgroup. Under an
initial address-space limit, unchanged `Calculus/TermSize.lean` failed creating
a thread below 2 GiB sampled RSS; that attempt is incomplete, not a pass.
Final checks instead run in the same managed VM using the actual repository,
toolchain and cache mounted into a digest-pinned validation container. Its
observed `memory.max` is 12,884,901,888 bytes and `memory.swap.max` is zero;
the kernel cap covers every child process and detached replay group. The
unchanged `TermSize` passes there. No proof, heartbeat, fixture timeout or
loop-fuel limit was increased. No interrupted or resource-stopped check is
passing evidence.

Shared implementation edits are limited to `Frontend/SolcJson/Body.lean`
(nominal refusal), `Syntax/Elab/Lower.lean` (pure inference),
`Syntax/Elab/Arms.lean` (copy/preflight integration),
`Syntax/Elab/Stmt.lean` (argument checks), `Syntax/Elab/Context.lean`
(comments), `Solidity.lean` (module registration), and regenerated
`Language/Features.lean` evidence. No interpreter, scoped statement, rule,
soundness or world/environment/log policy module changed. The feature catalog
remains `partial`; tuple-target and nominal/recursive/reference-interface
gaps listed above are not claimed complete.
