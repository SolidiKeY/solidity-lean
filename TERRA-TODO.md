# V15 H14 routine proof packet — EnvironmentTasksV1

Generated signatures: `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentTasksV1.lean`.
Regenerate/check with `python3 scripts/roadmap-v15-generate-environment-tasks.py --check`.
The JSON specification and generator own the frozen v1 signatures; announce V2 before changing them.
The frozen task module supplies no theorem, instance or axiom. Separate Sol producer lemmas now exist in `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentObservationProducer.lean`; they require LocalFacts at the actual site. Minimal finite clients exist in `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentObservationWitness.lean`. Universal routine facts and the unconditional frozen claims remain unproved.

Implement in NEW module `SolidityBridge.RoadmapV15.P10.EnvironmentObservationBatch`:

| Lemma | Exact statement type | Why routine |
|---|---|---|
| `origin_local_facts` | `EnvironmentTasksV1.OriginFactsClaim` | Unfold existing C', δ, α and memoryExpansionCost only; no execution proof. |
| `gasprice_local_facts` | `EnvironmentTasksV1.GasPriceFactsClaim` | Same finite base-cost/arity/no-expansion equations; no execution proof. |
| `chainid_local_facts` | `EnvironmentTasksV1.ChainIdFactsClaim` | Same finite existing opcode equations, no new environment/profile parameter. |
| `source_refusals` | `EnvironmentTasksV1.SourceRefusalsClaim` | Existing G31 admittedOp and step definitions refuse exactly these opcodes. |

Construct `glueBatch_discharged : EnvironmentTasksV1.PendingGlueBatch` ONLY after all four proofs exist; never take PendingGlueBatch or desired execution as a hidden premise. Retain original actual gas/stack/fuel order and full State/X observations. No new Scalar/environment slice, source key, pin/fork, maxHeartbeats, recursion or test budget.

Automation first under H14: use lean_multi_attempt with simp only/rfl/decide/omega and applicable repo tactics before manual steps. Record actual tool availability; never present CLI checks as MCP. Use the shared toolkit when present. No Solidity.lean edits; any eventual registrations/freezes must be generated.

Only after Sol supplies the producer proofs, add controls in NEW module `SolidityBridge.RoadmapV15.P10.EnvironmentObservationBatchControls`: populated origin19/source11/owner7 and nonzero account/memory/calldata/return buffers; gasPrice37 versus initial gas9/remaining7; actual pin chainId; complete ordered code/stack; inherited-static and writable cases; input1023 push success/1024 overflow; gas/fuel refusal order; source-profile refusal. Print actual axiom sets for headlines and controls. Preserve every original observation/profile refusal.

NOT TERRA: proving OriginClaim/GasPriceClaim/ChainIdClaim or their fetched/X agreement producers (these are statement-only Sol tasks), SIGNEXTEND word/Scalar producer (now proved below), compiler/source lowering, ABI, physical allocation/PaddingCorrect, Osaka approval, account/world/call/transaction/resource/trace producer proofs. These stay with Sol/original owners. No local or parent completion follows from this packet. All150 full opcode rows remain OPEN.

## Sol follow-up (not Terra)

After the universal facts are proved, Sol will instantiate `origin_at`, `gasprice_at`,
and `chainid_at` with the corresponding per-site fact to discharge the three
frozen producer claims. The existing finite witnesses are not proofs for all
sites. Sol retains these producer results and their semantic review. QH14AUTO
is resolved by the authorized bounded scratch-file automation fallback; use
one example per candidate, retain failures, and keep successful automation.

## Sol numeric progress

The positive SIGNEXTEND case is now proved in
`Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionPositive.lean`, with minimal
nonzero and strict-domain witnesses in
`Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionPositiveWitness.lean`.
General negative/truncating Scalar/reference primitive agreement is now proved below; source/compiler/Osaka origin work stays with Sol. This does not
change or complete the delegated environment fact/control tasks.

## Further Sol numeric progress

The existing positive module now additionally proves arbitrary high-bit
truncation when the selected low-width residue has a clear sign bit. See
`signextend_nonnegative_residue_word` and
`signextend_nonnegative_residue_agreement`; concrete clients are in
`Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionResidueWitness.lean`.
Negative low-residue and all-index Scalar/reference extension are now proved below; source/compiler/Osaka work remains with Sol. This does not discharge or
change the delegated environment facts or unconditional frozen claims.

## Completed Sol primitive: all-index SIGNEXTEND

`signextend_negative_residue_word`, `signextend_width_word`,
`signextend_all_word`, `signextend_scalar_result` and
`signextend_all_agreement` now prove the actual pinned reference/Scalar
primitive for every index/value word, without a sign or residue premise.
Unified clients and negative controls are in
`Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionAllWitness.lean`.
This does not complete any full opcode row or the compiler/source/Osaka/resource
composition, and does not change the environment work delegated above.

## Storage-isolation control continuation

Two Sol producer laws are checked in
`Bridge/SolidityBridge/RoadmapV15/P10/StorageWarmTransport.lean`:
`storage_keys_compare_eq` and `sload_distinct_cost`. Their numeric pair inequality
is not a hash injectivity or symbolic-path premise.

Module `SolidityBridge.RoadmapV15.P10.StorageIsolationControls` now has four
checked and registered clients: `cold_distinct_client`, `warm_distinct_client`,
`same_pair_counterexample` and `complete_ordered_observations`. Their original
proof bodies were accepted unchanged after the published-base rebase. This
routine continuation is complete; do not duplicate it. The original delegated
environment packet remains unchanged and pending.

## Invocation control continuation (source-only)

The three charged fetched producers in `Bridge/SolidityBridge/RoadmapV15/P10/InvocationEnvironment.lean`
are checked. Seven routine control bodies in the sibling `InvocationEnvironmentControls.lean`
are proposals only: corrected record layout has not passed the guarded kernel check.
Do not treat them as proved or register them before actual passing diagnostics.

| Module | Lemmas | Why routine |
|---|---|---|
| `SolidityBridge.RoadmapV15.P10.InvocationEnvironmentControls` | `address_client`, `caller_client`, `callvalue_client` | Instantiate checked producers in independent full expected records. |
| same module | `legal_capacity`, `resource_order` | Existing finite native checks at legal stack boundaries, exact gas and fuel. |
| same module | `distinct_identities`, `complete_ordered_observation` | Concrete nonzero identity/order distinctions and complete populated observations. |

Keep every statement and expected value; do not weaken resource or identity distinctions.
Monitor refusal is not a passing Lean check. The earlier EnvironmentObservationBatch
packet remains independent and pending; these proposals do not replace it.
# Preserved task lists after published adoption

## Existing owned list

# Routine proof queue — current G21 follow-up

Earlier superseded V2/P10 notes remain preserved in refs/checkpoints/v13-before-c467-rebase and the previous sealed exports. They are not silently re-adopted here.

## G21 readback compatibility glue (H14 cascade; not a discharged proof)

| Module/lemma | Why routine and exact prerequisites |
|---|---|
| Original V13 Solidity.Backend.AbiWorld.ReturnedBytes.memory_call_pushes_zero (source at main85d13e5c7db386fd832391be5f7d04970ad31f22) | Existing theorem statement is unchanged; add/refine the three newly published Compiler.Compilation cases memoryCopy/fixedMemory/copyConstruction. Each has isMemoryCalls=false and contradicts hc. Do not weaken hc or any representation/cost bound, edit producer semantics or increase budgets. This is owned compatibility glue for Terra, not work completed by this checkpoint. |
| Future G21 canonical Error packet entry/body composition | Apply existing BytesReadback.roundtrip after source_error codec equality, retaining size<=lim, free+allocationBytes<=lim and original2<=f. BLOCKED until the owned constructor glue above and V12 FrameLaws Binders/RetBinders interface repair are available. No desired verdict premise or new admission policy is allowed. No proof claimed or continuation scheduled. |

## Storage ABI finite success control (unchanged proof budgets)

Module: Solidity.Lowering.V08.LiteralFailureStorageDecodeControls.
Lemma: decode_true (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) frame 35 decoder).run
  (.cons (.storRef rfl path) caller,canonical) =
 (.ok (.val (.bool true)),(.cons (.storRef rfl path) caller,canonical)).
Why routine: closed finite existing evaluator, actual storage word of31zero
bytes and final1; split byte recursion into short blocks or reuse an exact
read-loop equation, then normalize the existing bool decoder. Single rfl
exceeds maxRecDepth; no budget increase permitted. Validated generic
load_bytes/load_memory/bytes_ok/arm/local_ok proofs stay with Sol. The host
#eval outcome is testing only, not this kernel proof. Raw failed attempts and
deferred statement are sealed with this checkpoint. Do not edit Source or
replace any read/decoder result by an assumption. No sorry/axiom placeholder
is added to Lean sources.

### Resolved: storage ABI finite success control

The deferred decode_true statement above is now proved, without budget changes,
as LiteralFailureStorageSuccessControls.decode_true in commit
364b2a8d319fa133e49f860faeba175f28fa4d2e. copied_observed is actual kernel
computation (decide +kernel), copied_full combines it with stored_bytes state
preservation through an abstract run_from_observation lemma, and word_decoder
isolates actual Source bool decoding before the final evaluator rewrite.
No Terra work remains for this item. Original failed attempts/seal remain
immutable; generic and all-profile/runtime obligations are unchanged.


## Published list

# Routine handoff status

## NJ1 — completed for the fixed fixture

The exact original decoder equality, packet and compilation/source/model
endpoints are now kernel-proved in the actual module
`SolidityBridge.Yul.StructuredSwitchJsonKernelAttachment`, namespace
`SolidityBridge.Yul.StructuredSwitchJson.KernelControls`:

- `raw_nested_parsed`: `blockAux 20 ast = .ok tree`, with no parser premise.
- `raw_nested_packet`: the original `Packet [] 20 16 (Controls.fixture "1")`.
- `raw_nested_compiles`: exact `checkCompile` equality returning that packet.
- `raw_nested_source`: actual closed-word execution at horizon16.
- `raw_nested_low_fuel`: exact compiler horizon2 refusal for the same fixture.
- `raw_nested_model`: arbitrary mathematical machine/caller, with the real
  represented-stack premise retained.

Bounds20/16, dirty literal, fixture and expected prefix21/999/42/17 are unchanged.
Earlier failed attempts are preserved as evidence. No NJ1 proof remains pending;
this closes only the fixed-fixture obligation, not generic JSON correctness,
Solidity admission, Source/G24/native adequacy or the full original lane.
No earlier excluded Terra tasks or completed work are restored here.


# Current integration status (2026-11-03)

The helper branch is rebased onto published8eec153a. Scalar now comes from
published Solidity.Lowering.V07.Scalar (exact original0ca869 blob), with NO
active private Scalar/P1 lookup. Older private-stage notes below are history.
IntegerReadBoundaryWitness now discharges the populated [255,256] soundness
witness: real selected uint8 success and eager Source-phase revert[], with
complete original state preserved. Its word geometry and decoder equations
are kernel proved. This specific item is DONE; other listed routines and
controls remain OPEN. Root registrations are generated for BoolArrayDelete,
IntegerArrays and IntegerReadBoundaryWitness. Full/import closure, whole-lane
and general lazy-selected-read lowering are not discharged.

# H14 cascade — G18.05 local bool-array deletion

Producer module: `Solidity.Backend.Aggregates.BoolArrayDelete`.
`default_heap`, `run_var`, `delete_related`, and `delete_preserves_related` are proved; the following are NOT proved claims.
Do not add axioms, `sorry`, higher budgets, or an assumed lowering simulation.
Use the actual `TRun.deleteMem`, Source `deleteLocal_array_run`, and existing
`BoolArrays.Related`; Source ids and intrinsic heap ids remain independent.
Registration must be generated, not hand-edited.

## Routine statements for Terra

In the producer namespace, define
```lean
def result {C : Contract} {Γ : Ctx} (s : State C Γ)
    (i : Idx Γ (.mem BoolArrays.boolR)) : State C Γ :=
  (s.alloc (empty s.H)).1.setLocal i (some (s.alloc (empty s.H)).2)
```

1. `result_contents` (module BoolArrayDelete):
```lean
∀ {C : Contract} {Γ : Ctx} (s : State C Γ)
  (i : Idx Γ (.mem BoolArrays.boolR)),
  MObj.elems ArrTy.dyn ((result s i).heap.get (s.alloc (empty s.H)).2) = []
```
Routine: published `Heap.get_alloc_self` and empty-object weakening.

2. `result_keeps` (same module):
```lean
∀ {C : Contract} {Γ : Ctx} (s : State C Γ)
  (i : Idx Γ (.mem BoolArrays.boolR)),
  Heap.Keeps (List.prefix_append s.H [BoolArrays.boolR]) s.heap (result s i).heap
```
Routine: `Heap.keeps_alloc`; setLocal changes no heap.

3. `result_local` (same module):
```lean
∀ {C : Contract} {Γ : Ctx} (s : State C Γ)
  (i : Idx Γ (.mem BoolArrays.boolR)),
  TEnv.get i (result s i).env = some (s.alloc (empty s.H)).2
```
Routine: typed environment get/set law; no runtime/frame premise.

4. New `BoolArrayDeleteControls` module: use `BoolArrayControls.lowered`,
push a second alias of its newest bool-array reference, delete `.here` via
actual `TRun.deleteMem`. Prove exact full result; top points to fresh empty
object, `.there .here` retains populated `[true,false]`, original bytes
objects retained. Prove wrong-alias-rebound and old-object-cleared negatives.
Routine: instantiate producer plus get/set/weakening and existing controls.
Try automation first; retain strict scoped axiom outputs.

## Soundness work retained by Sol

`delete_related` now derives the actual post-deletion `BoolArrays.Related`
for independent fresh references at Source budget n+2. Old heap contents are now protected by `delete_preserves_related`, deriving
Source freshness from actual occupancy. Caller-local/alias-binding preservation
and populated joint controls remain unfinished. Cover Source budgets 0/1
as timeout with original full state; logical target success does not imply
Source fuel sufficiency. Do not count the new-content relation as general
frame/history preservation. General Source/frame lowering,
physical execution/gas, general recursive copy/delete and G18.05 remain OPEN.

## Additional routine consequence

5. `delete_preserves_related_any_budget` in BoolArrayDelete: same parameters
and `before : Related source.2.heap address target.heap reference` as
`delete_preserves_related`, but replace `(n+2)` with arbitrary `(budget : Nat)`
in the Source operation and retain its exact target postheap and weakened
old reference. Routine: cases budget 0/1 versus n+2 using actual
Source.deleteLocal_array_run; exhausted branches keep the original Source
heap while intrinsic allocation keeps old target objects. This would observe
only old contents, NOT synchronize Source timeouts with logical target success.
Do not infer matching verdicts or general frame simulation from it.


# H14 cascade — generic integer-array consumer (private V07 prerequisite)

Module `Solidity.Backend.Aggregates.IntegerArrays` now proves value_related,
capacity and copy_related. It imports exact peer Scalar5d45c086, not yet
integrated into this helper branch. Use only the recorded private stage until
combined integration; no substitute scalar implementation or proof oracle.

Routine lemmas to add after producer validation:

- `IntegerArrays.target_old_heap`: for `target,t,values,room`,
  `Heap.Keeps (List.prefix_append target.H [runtimeTy t]) target.heap
    (lower target t values room).heap`.
  Reason: existing Heap.keeps_alloc; no new copy arithmetic.
- `IntegerArrays.target_old_local`: for any actual typed local index i,
  `TEnv.get (.there i) (lower target t values room).env =
    LTy.TDenote.wk (List.prefix_append target.H [runtimeTy t]) _
      (TEnv.get i target.env)`.
  Reason: existing TEnv.get_wk; actual frame extension already in lower.
- `IntegerArrays.target_new_local`: for `target,t,values,room`,
  `TEnv.get .here (lower target t values room).env =
    some (target.alloc (object target.H t values room)).2`.
  Reason: actual State.allocPush/push equation; connects the new binding to
  the allocated reference. Added following independent finder review.
- `IntegerArrayControls`: inhabited actual ABI copies for unsigned8 values
  [255,0] and signed8 values [-1,-128] using canonical 256-bit encoded words;
  prove copy_related instances and exact numeric/order observations through
  V07.integer_observe. Preserve populated bytes/caller aliases. Add dirty
  unsigned8 word256 and signed8 non-sign-extended word255 rejection controls,
  empty input and swapped-order negatives. These are UNPROVED requested
  controls, not asserted outputs; inspect actual decodeWord before choosing
  fixtures and retain source-specific failure bytes and unchanged original
  state on validation failure. Do not alter
  expected verdicts. No source dispatch/fetched-EVM claim.

`lowerCopy` and `error_iff_copy_error` now execute all actual word validation
branches and reflect exact Source errors/unchanged full original state on validation failure over certified ABI
entry. `sourceCopy_run` and `entry_error_iff_source_error` now compose actual
Source argument header/decode/conversion without an entry-success premise.
Sol retains general Source declaration/expression/frame/compiler admission;
this client is not a general lowering certificate. Independent typed Source/frame admission,
recursive shapes/location copies and physical runtime realization remain open.
Registration for new modules must be generated under H14.


Routine integer validation equations for Terra:
- `lowerCopy_success`: with the same arguments as copy_related and actual
  `validation = .ok values`, prove `lowerCopy target t frame selector data ...
  entry = .ok (lower target t values (capacity t frame selector data ... entry
  validation))`. Reason: split the actual dependent validator match.
- `lowerCopy_failure`: with actual `validation = .error halt`, prove the
  corresponding `lowerCopy ... = .error halt`. Reason: same actual match.
These are not hypothetical simulation premises; exact definitions and
error_iff_copy_error already constrain them. Controls remain unproved.


Routine integer entry consequences for Terra:
- `lowerEntry_of_ok`: with actual `entry : Source.cdTail data index 32 =
  .ok (offset,length)`, `lowerEntry ... index = lowerCopy ... entry`.
- `lowerEntry_of_error`: with actual `entry : Source.cdTail data index 32 =
  .error halt`, `lowerEntry ... index = .error halt`.
  Reason for both: split the real dependent match, no new validation or
  simulation law. Keep Source.Halt and input/frame equations exact.
- `successful_import`: same actual entry/validation arguments as copy_related,
  but replace Source.cdToMem in the conclusion by sourceCopy and include
  lowerEntry success plus actual Source result/fresh address/full grown state.
  Reason: instantiate sourceCopy_run, lowerCopy_success and copy_related.
  The existing lowerCopy_success TODO must first be proved. Preserve actual
  ordered values and independent Source/target IDs, not balance-only or
  erased frame observations. This is routine composition, not final compiler
  or machine correctness; inhabited controls remain required.


# H14 cascade — integer typed expression and scoped client

Within `IntegerArrays.Expression`, conversion_allowed derives the actual
Source implicit judgment for every Source.IntTy; expr uses that proof.
eval_expr_run and scopedCopy_run are proved at the existing Source budget
n+2. This is not physical execution or general frontend/profile lowering.

Routine lemmas for Terra:
- `eval_expr_zero` / `eval_expr_one`: for any actual extended
  `before : Source.EMState E (argumentTy t :: caller)`, actual
  `(Source.evalE G frame 0 (expr t)).run before` and budget1 respectively
  equal `(.error .timeout,before)`. Reason: actual evalE budget equations.
- `scopedCopy_low_run`: for budget≤1 and arbitrary complete caller source,
  actual scopedCopy.run equals `match Source.cdTail data index 32 with
  | .error halt => (.error halt,source)
  | .ok _ => (.error .timeout,source)`.
  Reason: real header law plus zero/one expression equations and EM.sub;
  no word validation or allocation before timeout after a successful header.
- `scoped_error_iff`: at budget n+2, `lowerEntry ... = .error halt ↔
  (Expression.scopedCopy t G frame (n+2) data index).run source =
  (.error halt,source)` under the SAME frame/selector equations as the
  existing native entry_error_iff_source_error. Reason: scopedCopy_run.
- Instantiate successful-import and populated signed8/unsigned8/empty/dirty/
  truncated-header controls for the real scoped expression. Preserve old
  aliases/objects/full caller locals, exact signed numeric order and errors.
  Add a phase-success versus expression-budget0-timeout negative to prevent
  counting Source.Halt phase reflection as fuel/gas/machine adequacy.
All remain unproved TODO statements; no whole profile or completed checkpoint
follows. Sol retains general source/frame/compiler adequacy beyond this client.


# H14 cascade — integer copy/index consumers

copy_read_related and copy_first_out are proved. The former consumes actual
Source copied-element reads and actual intrinsic Heap.readAddr, including
exact numeric observation via V07. The latter covers first invalid index
length, with real Source index-panic bytes and grown heap.next, versus actual
intrinsic readAddr=none. Index representability follows from real ABI extent;
no desired read or bounds oracle was introduced.

Routine extraction `target_contents`: for target,t,values,room, prove
`MObj.elems ArrTy.dyn ((lower target t values room).heap.get
  (target.alloc (object target.H t values room)).2) = values.map (value t)`.
Reason: published allocPush_get and primitive weakening. Identical local
facts in both proved consumers are available to extract; no broad refactor
or budget increase. Keep the exact source-keyed private producer unchanged.

Routine controls in IntegerArrayControls remain UNPROVED:
- Actual signed8 and unsigned8 canonical two-word ABI copies, then actual
  Source second-element read and intrinsic second-element Heap.readAddr;
  prove exact [-1,-128] and [255,0] numeric/order observations respectively.
- At index2, prove exact Source index-panic bytes/full grown state and target
  none. Prove heap.next grew once, rejecting rollback to original heap or a
  fabricated successful read. Include empty extent/index0.
- Dirty validation followed by an invalid read must fail at validation and
  retain the original full state, unlike successful copy then bad index.
- Preserve populated caller aliases/old objects; reject swapped order,
  signed truncation, wrong source address or wrong target reference.
These instantiate actual existing definitions; inspect decoder canonicality
before fixtures. They are not external EVM or general frame/compiler tests.


# H14 cascade — selected calldata read and eager-import boundary

CalldataRead.eval_read_run derives the actual typed index expression result
from the selected decoder, with unchanged full Source state. imported_read
compares it to the validated imported snapshot and derives Source uint256
index bounds. Whole-array validation is an EXPLICIT conditional snapshot
premise, never inferred from selected-read success or counted as general
calldata lowering. selected_success_import_error proves the semantic boundary
from actual selected-word and traversal equations; no machine halt is asserted.

Routine controls for Terra (UNPROVED):
- Build uint8 calldata array data with ABI head32, length2, first word255,
  second word256. The latter MUST be `List.replicate 30 0 ++ [1,0]`:
  existing NestedCalldataControls.word stores only UInt8.ofNat n and word256
  would incorrectly wrap to zero. Prove actual word observations first.
- With existing populated caller fixtures and actual G, prove Source typed
  selected index0 at budget2 returns uint8 255 with full unchanged caller;
  eager lowerEntry fails with actual Source.revert[] due to second word.
  Prove real entry and decoder equations, instantiate boundary theorem;
  reject treating eager validation as a total selected-read compiler.
- For fully canonical signed8/unsigned8 arrays instantiate imported_read;
  prove exact source/numeric order, preserved caller objects and target handle.
- Instantiate first selected-index OOB using published eval_cdIndex_out_run
  together with copy_first_out. Direct calldata read leaves original Source
  heap unchanged, whereas copy-then-bad-read preserves the grown copied heap.
  Do NOT identify those states or intrinsic none with machine panic.

Routine index-bound extraction: same local arithmetic used in imported_read
and selected_success_import_error may be factored into a proved helper; no
new caller-provided typing or representability premise, larger budget or
source scalar implementation. General selected-element target lowering must
respect lazy selected-word validation; a blanket eager-validation premise
cannot close the admitted Source profile. No semantic choice is requested.


# V14 constructor argument routines (H14)

No unproved Lean declarations or axioms are introduced by this list.

- ConstructorLocalArguments: derive identity STy.implicit admission for arbitrary
  integer types from the existing definition (routine Boolean/reflexivity law).
  The current explicit ha/hb inputs are not a new whole-profile restriction.
- ConstructorArgumentControls: state and prove exact fuel=1 and fuel=2 timeouts
  with the same complete before state (routine reduction of the published runner).
  Do not increase fuel or weaken error observations.
- ConstructorArgumentControls: factor the existing conjunctive inhabited control
  into separately named order/old-object/alias lemmas if needed by clients
  (routine projections; do not replace the complete execution statements).

Hard work retained by V14: general n-ary/effectful argument lowering, constructor
selection/body/inheritance binding, source/frame/world and failure correspondence,
G43 and final executable closure. No P8a coverage or P1 profile provenance inferred.

## Inherited argument routines (H14)

- ConstructorBaseArguments.old_acc_prefix: after bound, the original CtorLocals
  list is a prefix of the returned accumulator; routine List.prefix_append.
- ConstructorBaseArguments.new_frame_keys: project the two appended/retrieved
  integer keys in constructor-frame order; routine bound/lookup projections.
- ConstructorBaseArguments.fresh_zero_timeout: for any RBaseArg and absent base,
  giveArgs at zero returns exact timeout with original state; routine reduction
  of the existing evaluator. Keep priority for an already-given base separate.

Hard work remains with V14: general effectful/n-ary argument transport, actual
constructor/body/initializer lowering and admitted Program provenance; the
current manually supplied fixture is not an elaborator certificate.

## Constructor failure routine projections (H14)

- ConstructorArgumentFailure.inner_aliases: project old reference locals through
  the existing setter-based innerAfter; routine Locals.get/set reduction.
- ConstructorArgumentFailure.wrong_panic: derive the actual giveArgs failure
  cannot return divZero bytes from giveArgs_failed and constructor_controls;
  routine Except.error injectivity, preserving exact Source.Halt.

General state-effectful arguments, multiple bases/initializers, canonical Program
provenance, source/body compilation and G43 remain substantive V14 work.

## Storage-failure routine projections (H14)

- ConstructorStorageFailure.old_aliases: project caller memory aliases and the
  retained old heap object through before/written; routine definitions/equality.
- ConstructorStorageFailure.not_old_state: specialize giveArgs_failed with
  state_distinct to exclude an arithmetic halt paired with before; routine pair
  and Except injectivity, preserving the full returned state.

G44.02/.03 and balance-independent G43/P14 remain next substantive work. H19
balance representation facts must stay explicit typed producer premises.

## Published ArgumentEntry consumer (pending bounded dependency validation)

Draft: `/workspace/v14-master-rebase-artifacts/published-059eb83d-adoption/draft/ConstructorFrameSelection.lean`.
Intended owned module: `Solidity/Backend/Executable/ConstructorFrameSelection.lean`.
Do not treat these statements as assumptions or completed theorems. Import closure
currently times out under unchanged180s; wait for verified source-keyed cache or
an independently demonstrated repair before checking. No proof-budget increase.

- `arguments`: `args.evalT caller = .ok (PrimTy.ofLit .uint 9 rfl, (PrimTy.ofLit .uint 1 rfl, ()))`. Routine local reads from the existing reached caller; keeps actual innermost parameter order.
- `selection`: `(Calls.compile 1 F program).isSome = true`. Routine actual compiler reduction; no hypothetical Program certificate.
- `cost_zero`: after deriving `checked` from selection, `checked.cost caller = 0`. Derive nonallocation and use existing zeroCost law.
- `room`: `1 + checked.need ≤ 16`. Derive real selected need; do not assume available capacity.

Sol retains source/native constructor composition, physical endpoint consumption,
full caller/heap/stack observations and negative controls. These remain OPEN.
