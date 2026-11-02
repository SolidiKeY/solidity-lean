import Solidity.Backend.Passes.LoopScopeApplication

/-! Complete loop/source observations and exact finite target witnesses below
use only existing intrinsic states and EVM loop iteration semantics. -/
namespace Solidity.Backend.Passes.LoopScopeObservations
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C A initial base machine)
open LoopScopeControls

private def arrayAt {H : HTy} (hp : Heap H) (id i : Nat) : Option Int := do
  if h : H[id]? = some A then
    let value ← hp.index (⟨id,h⟩ : HRef H A) .dyn (indexValue (wmod i))
    pure value.val
  else none
private def lengthAt {H : HTy} (hp : Heap H) (id : Nat) : Option Int :=
  if h : H[id]? = some A then some (hp.len (⟨id,h⟩ : HRef H A) .dyn) else none

private def beforeVector (σ : State C LoopScopeControls.Γ) : Option (List Int) := do
  let old ← TEnv.get (.there (.there .here) : Idx LoopScopeControls.Γ (.mem A)) σ.env
  let live ← TEnv.get (.here : Idx LoopScopeControls.Γ (.mem A)) σ.env
  let flag := TEnv.get (.there .here : Idx LoopScopeControls.Γ (.val .uint)) σ.env
  let len ← lengthAt σ.heap 0
  let value ← arrayAt σ.heap 0 0
  pure [σ.H.length,old.id,live.id,flag.val,len,value]

private def loopVector (σ : State C LoopScopeControls.Γ) : Option (List Int) := do
  let old ← beforeVector σ
  let len ← lengthAt σ.heap 1
  let first ← arrayAt σ.heap 1 0
  let second ← arrayAt σ.heap 1 1
  pure (old ++ [len,first,second])

private def finalVector (σ : State C LoopScopeControls.Ω) : Option (List Int) := do
  let old ← TEnv.get (.there (.there (.there .here)) : Idx LoopScopeControls.Ω (.mem A)) σ.env
  let live ← TEnv.get (.there .here : Idx LoopScopeControls.Ω (.mem A)) σ.env
  let flag := TEnv.get (.there (.there .here) : Idx LoopScopeControls.Ω (.val .uint)) σ.env
  let observed := TEnv.get (.here : Idx LoopScopeControls.Ω (.val .uint)) σ.env
  let oldLen ← lengthAt σ.heap 0
  let oldValue ← arrayAt σ.heap 0 0
  let len ← lengthAt σ.heap 1
  let first ← arrayAt σ.heap 1 0
  let second ← arrayAt σ.heap 1 1
  pure [σ.H.length,old.id,live.id,flag.val,observed.val,oldLen,oldValue,len,first,second]

theorem before_source_vector : beforeVector prepared.st = some [1,0,0,42,1,7] := by decide +kernel
theorem loop_source_vector : loopVector loopOut.st = some [2,0,1,0,1,7,2,0,0] := by decide +kernel
theorem final_source_vector : finalVector final.st = some [2,0,1,0,0,1,8,2,9,0] := by decide +kernel

theorem skipped_effect : beforeVector prepared.st ≠ beforeVector loopOut.st := by
  decide +kernel

def fullCursor (m : Machine) : Machine := {m with mem := upd m.mem 0 (.val wMax)}

/-- Measuring this reached loop by the legacy0 would falsely accept capacity.
The actual successful Cost3 is a reached demand of the original scope Room. -/
theorem wrong_cost_refused (selected : Nat → Fin W) (m : Machine) :
    AllocationInput 1 128 0 prepared.st selected (fullCursor m) ∧
    ¬ LoopScopes.Room enclosed.cert 128 prepared.st selected (fullCursor m) := by
  refine ⟨.inl rfl,?_⟩
  intro room
  have capacity := scope_cost_allocation_input room actual_cost
  rcases capacity with impossible | ⟨hb,cursor,repr,fit⟩
  · cases impossible
  · have cell : wMax = cursor := Word.val.inj repr.arrays.free.cell
    subst cursor
    change W - 1 + 3 < W at fit
    have positive := W_pos
    omega

end Solidity.Backend.Passes.LoopScopeObservations
