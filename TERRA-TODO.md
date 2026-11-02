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
  fixtures and retain source-specific failure bytes/rollback. Do not alter
  expected verdicts. No source dispatch/fetched-EVM claim.

Sol retains total actual Source error/target adapter composition beyond the
successful validation theorem. Independent typed Source/frame admission,
recursive shapes/location copies and physical runtime realization remain open.
Registration for new modules must be generated under H14.
