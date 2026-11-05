import Solidity.Backend.Passes.FixedBooleanSequence

/-! Complete observations and negative controls for the fixed runtime receiver.
No observation here claims ABI bytes or frontend-to-intrinsic correspondence. -/
namespace Solidity.Backend.Passes.FixedBooleanSequence
open Evm Evm.Memory Evm.Compiler
open Controls.Fixture
open ReferenceControls (Γb state branchThenRead wrongOrder)

private noncomputable def sourceVector (b : Bool) : Option (List Int) := do
  let st := (final b).st
  let dest ← TEnv.get (.there (.there (.there (.there .here)))) st.env
  let saved ← TEnv.get (.there (.there (.there (.there (.there .here))))) st.env
  let independent ← TEnv.get (.there (.there (.there (.there (.there (.there .here)))))) st.env
  let observed := TEnv.get (.here : Idx Final (.val .uint)) st.env
  let captured := TEnv.get (.there .here : Idx Final (.val .uint)) st.env
  let flag := TEnv.get (.there (.there .here) : Idx Final (.val .bool)) st.env
  let read := TEnv.get (.there (.there (.there .here)) : Idx Final (.val .uint)) st.env
  let a ← st.heap.index saved .dyn (indexValue (wmod 0))
  let z ← st.heap.index saved .dyn (indexValue (wmod 1))
  let c ← st.heap.index independent .dyn (indexValue (wmod 0))
  pure [st.H.length,observed.val,captured.val,flag.toNat,read.val,
    dest.id,saved.id,independent.id,st.heap.len saved .dyn,a.val,z.val,
    st.heap.len independent .dyn,c.val]

theorem both_complete_source_vectors :
    sourceVector true = some [2,5,4,1,4,1,0,1,2,7,9,1,5] ∧
    sourceVector false = some [2,8,7,0,7,0,0,1,2,8,9,1,4] := by
  exact ⟨by decide +kernel,by decide +kernel⟩

private def vector (out : Evm.Out) : Option (List Nat) :=
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w =>
      match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem allocated_prefix_vectors :
    vector (.ok {(runtimeInput true) with stack := [w[77],w[88]]} 0) =
      some [77,88,261,99,259,256,256,0,1,0,0,2,7,9,1,4] ∧
    vector (.ok {(runtimeInput false) with stack := [w[77],w[88]]} 0) =
      some [77,88,261,99,259,256,256,0,0,0,0,2,7,9,1,4] := by
  exact ⟨by decide +kernel,by decide +kernel⟩

theorem receiver_prefix_vectors :
    vector (run receiver.code {(runtimeInput true) with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,259,4,1,0,0,2,7,9,1,4] ∧
    vector (run receiver.code {(runtimeInput false) with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,256,7,0,0,0,2,7,9,1,4] := by
  exact ⟨by decide +kernel,by decide +kernel⟩

def wrongReceiver : Memory.CompiledProg 1 BF wrongOrder :=
  (Memory.compileProg 1 BF wrongOrder).get (by decide +kernel)
def wrongConsumer : Memory.CompiledProg 1 wrongReceiver.frag suffix :=
  (Memory.compileProg 1 _ suffix).get (by decide +kernel)

theorem wrong_order_complete_vector :
    vector (run (wrongReceiver.code ++ wrongConsumer.code)
      {(runtimeInput true) with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,259,7,1,4,5,2,7,9,1,5] := by decide +kernel

theorem wrong_order_discriminated :
    vector (run (wrongReceiver.code ++ wrongConsumer.code)
      {(runtimeInput true) with stack := [w[77],w[88]]}) ≠
      some [77,88,261,99,259,256,259,4,1,4,5,2,7,9,1,5] := by decide +kernel

theorem wrong_value_discriminated :
    vector (run fixedCode {(runtimeInput false) with stack := [w[77],w[88]]}) ≠
      some [77,88,261,99,259,256,259,4,1,4,5,2,7,9,1,5] := by decide +kernel

theorem tail_corruption_discriminated :
    vector (run fixedCode {(runtimeInput true) with stack := [w[88],w[77]]}) ≠
      some [77,88,261,99,259,256,259,4,1,4,5,2,7,9,1,5] := by decide +kernel

theorem skipped_capture_discriminated :
    vector (run receiver.code {(runtimeInput true) with stack := [w[77],w[88]]}) ≠
      some [77,88,261,99,259,256,259,4,1,4,5,2,7,9,1,5] := by decide +kernel

theorem insufficient_frame {base : Nat → Fin W} {st : State C Γb} {m : Machine} :
    ¬ (Compilation.memory consumer).Input 1 7 base st m := by
  intro h
  have capacity := h.2.1
  change 1 + 7 ≤ 7 at capacity
  omega

end Solidity.Backend.Passes.FixedBooleanSequence
