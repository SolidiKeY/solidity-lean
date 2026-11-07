import Solidity.Backend.Passes.MemoryCallScopeControls
import Solidity.Backend.Passes.MemoryCallObservations

namespace Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations
open Evm Evm.Memory MemoryCallControls
open MemoryCallScopeBoundary.Controls

private def arrayAt {H : HTy} (hp : Heap H) (id i : Nat) : Option Int := do
  if h : H[id]? = some A then
    let value ← hp.index (⟨id,h⟩ : HRef H A) .dyn (indexValue (wmod i))
    pure value.val
  else none
private def lengthAt {H : HTy} (hp : Heap H) (id : Nat) : Option Int :=
  if h : H[id]? = some A then some (hp.len (⟨id,h⟩ : HRef H A) .dyn) else none

def sourceVector (state : State C Before) : Option (List Int) := do
  let old ← TEnv.get (.there .here : Idx Before (.mem A)) state.env
  let marker := TEnv.get (.here : Idx Before (.val .uint)) state.env
  let oldLength ← lengthAt state.heap 0
  let oldValue ← arrayAt state.heap 0 0
  let defaultLength ← lengthAt state.heap 1
  let ownedLength ← lengthAt state.heap 2
  let left ← arrayAt state.heap 2 0
  let right ← arrayAt state.heap 2 1
  let reboundLength ← lengthAt state.heap 3
  let reboundValue ← arrayAt state.heap 3 0
  pure [state.H.length,old.id,marker.val,oldLength,oldValue,defaultLength,
    ownedLength,left,right,reboundLength,reboundValue]

theorem scope_source_vector : sourceVector post = some [4,0,42,1,7,0,2,33,34,1,44] := by
  decide +kernel

theorem final_source_vector : sourceVector Controls.final.st = some [4,0,42,1,8,0,2,33,34,1,44] := by
  decide +kernel

private def targetWords (out : Evm.Out) (addresses : List Nat) : Option (List Nat) := do
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w => match w with
    | .val v => some v.val
    | .slot _ => none
  | _ => none

abbrev addresses := MemoryCallObservations.addresses
def code : List Instr := allocation.code ++ (scopeProducer.code ++ Controls.right.code)

theorem scoped_target_vector : targetWords (run (allocation.code ++ scopeProducer.code)
    {machine with stack := [w[77],w[88]]}) addresses =
    some [77,88,264,99,256,42,256,259,259,259,1,7,0,2,33,34,1,44] := by
  decide +kernel

theorem final_target_vector : targetWords (run code {machine with stack := [w[77],w[88]]}) addresses =
    some [77,88,264,99,256,42,256,259,259,259,1,8,0,2,33,34,1,44] := by
  decide +kernel

/-- The old consumer has a different typed context. Its raw emitted code still
reads the stale returned pointer and mutates the object dropped from locals. -/
def wrongCode : List Instr := allocation.code ++ (scopeProducer.code ++ MemoryCallControls.consumer.code)
theorem wrong_context_vector : targetWords (run wrongCode {machine with stack := [w[77],w[88]]}) addresses =
    some [77,88,264,99,256,42,256,259,259,259,1,8,0,2,42,34,1,44] := by
  decide +kernel

theorem wrong_context_differs :
    targetWords (run code {machine with stack := [w[77],w[88]]}) addresses ≠
      targetWords (run wrongCode {machine with stack := [w[77],w[88]]}) addresses := by
  rw [final_target_vector,wrong_context_vector]
  decide

theorem skipped_suffix_differs :
    targetWords (run (allocation.code ++ scopeProducer.code) {machine with stack := [w[77],w[88]]}) addresses ≠
      targetWords (run code {machine with stack := [w[77],w[88]]}) addresses := by
  rw [scoped_target_vector,final_target_vector]
  decide

theorem corrupted_tail_refused : targetWords (run code {machine with stack := [w[77],w[88]]}) addresses ≠
    some [78,88,264,99,256,42,256,259,259,259,1,8,0,2,33,34,1,44] := by
  rw [final_target_vector]
  decide

theorem saved_tail_not_erased : (w[77] :: w[88] :: ([] : List Word)) ≠ [] := by decide

end Solidity.Backend.Passes.MemoryCallScopeBoundary.Observations
