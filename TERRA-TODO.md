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
`default_heap`, `run_var`, and `delete_related` are proved; the following are NOT proved claims.
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
for independent fresh references at Source budget n+2. Caller/alias preservation
and populated joint controls remain unfinished. Cover Source budgets 0/1
as timeout with original full state; logical target success does not imply
Source fuel sufficiency. Do not count the new-content relation as general
frame/history preservation. General Source/frame lowering,
physical execution/gas, general recursive copy/delete and G18.05 remain OPEN.
