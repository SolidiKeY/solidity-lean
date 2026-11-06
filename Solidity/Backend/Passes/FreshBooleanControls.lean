import Solidity.Backend.Passes.FreshBooleanFailure

/-! Complete ordered fresh-prefix observations. Internal revert has no
post-failure machine: order/tail negatives observe the reached prefix. -/
namespace Solidity.Backend.Passes.FreshBooleanControls
open Evm Evm.Memory Evm.Compiler
open Controls.Fixture FixedBooleanSequence FreshBooleanPrefix FreshBooleanFailure
open ReferenceControls (Γb state initializeBool branchThenRead wrongOrder)

private def words (out : Evm.Out) : Option (List Nat) :=
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w =>
      match w with | .val v => some v.val | .slot _ => none
  | _ => none

private def throughInitialization (b : Bool) : List Instr := population.code ++ (initializer b).code
private def throughReceiver (b : Bool) : List Instr := throughInitialization b ++ receiver.code

/-- Every cell in the existing ordered vector is retained at each prefix:
cursor/sentinel, all locals/aliases, both old elements and independent object. -/
theorem ordered_initial_to_capture :
    words (.ok {initialMachine with stack := [w[77],w[88]]} 0) =
      some [77,88,256,99,0,0,0,0,0,0,0,0,0,0,0,0] ∧
    words (run population.code {initialMachine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,256,0,0,0,0,2,7,9,1,4] ∧
    words (run (throughInitialization true) {initialMachine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,256,0,1,0,0,2,7,9,1,4] ∧
    words (run (throughReceiver true) {initialMachine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,259,4,1,0,0,2,7,9,1,4] ∧
    words (run (prefixCode true) {initialMachine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,259,4,1,4,0,2,7,9,1,5] ∧
    run (wholeCode true) {initialMachine with stack := [w[77],w[88]]} = .revert := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,?_⟩
  exact (fresh_revert [w[77],w[88]]).2.1

theorem ordered_opposite_prefix_and_terminal :
    words (run (throughInitialization false) {initialMachine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,256,0,0,0,0,2,7,9,1,4] ∧
    words (run (throughReceiver false) {initialMachine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,256,7,0,0,0,2,7,9,1,4] ∧
    words (run (prefixCode false) {initialMachine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,256,7,0,7,0,2,8,9,1,4] ∧
    words (run (wholeCode false) {initialMachine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,256,7,0,7,9,2,8,9,1,4] := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

private noncomputable def allocatedVector : Option (List Int) := do
  let dest ← TEnv.get (.there .here : Idx Γ (.mem (.array (.prim .uint)))) σ.env
  let saved ← TEnv.get (.there (.there .here) : Idx Γ (.mem (.array (.prim .uint)))) σ.env
  let independent ← TEnv.get (.there (.there (.there .here)) : Idx Γ (.mem (.array (.prim .uint)))) σ.env
  let a ← σ.heap.index saved .dyn (indexValue (wmod 0))
  let z ← σ.heap.index saved .dyn (indexValue (wmod 1))
  let c ← σ.heap.index independent .dyn (indexValue (wmod 0))
  pure [σ.H.length,(TEnv.get (.here : Idx Γ (.val .uint)) σ.env).val,dest.id,saved.id,independent.id,
    σ.heap.len saved .dyn,a.val,z.val,σ.heap.len independent .dyn,c.val]

private noncomputable def selectedVector (st : State C Γb) : Option (List Int) := do
  let dest ← TEnv.get (.there (.there .here)) st.env
  let saved ← TEnv.get (.there (.there (.there .here))) st.env
  let independent ← TEnv.get (.there (.there (.there (.there .here)))) st.env
  let a ← st.heap.index saved .dyn (indexValue (wmod 0))
  let z ← st.heap.index saved .dyn (indexValue (wmod 1))
  let c ← st.heap.index independent .dyn (indexValue (wmod 0))
  pure [st.H.length,(TEnv.get (.here : Idx Γb (.val .bool)) st.env).toNat,
    (TEnv.get (.there .here : Idx Γb (.val .uint)) st.env).val,dest.id,saved.id,independent.id,
    st.heap.len saved .dyn,a.val,z.val,st.heap.len independent .dyn,c.val]

private noncomputable def capturedVector (b : Bool) : Option (List Int) := do
  let st := (afterCapture b).st
  let dest ← TEnv.get (.there (.there (.there .here))) st.env
  let saved ← TEnv.get (.there (.there (.there (.there .here)))) st.env
  let independent ← TEnv.get (.there (.there (.there (.there (.there .here))))) st.env
  let a ← st.heap.index saved .dyn (indexValue (wmod 0))
  let z ← st.heap.index saved .dyn (indexValue (wmod 1))
  let c ← st.heap.index independent .dyn (indexValue (wmod 0))
  pure [st.H.length,(TEnv.get (.here : Idx Captured (.val .uint)) st.env).val,
    (TEnv.get (.there .here : Idx Captured (.val .bool)) st.env).toNat,
    (TEnv.get (.there (.there .here) : Idx Captured (.val .uint)) st.env).val,
    dest.id,saved.id,independent.id,st.heap.len saved .dyn,a.val,z.val,st.heap.len independent .dyn,c.val]

private noncomputable def oppositeVector : Option (List Int) := do
  let st := oppositeResult.st
  let dest ← TEnv.get (.there (.there (.there (.there .here)))) st.env
  let saved ← TEnv.get (.there (.there (.there (.there (.there .here))))) st.env
  let independent ← TEnv.get (.there (.there (.there (.there (.there (.there .here)))))) st.env
  let a ← st.heap.index saved .dyn (indexValue (wmod 0))
  let z ← st.heap.index saved .dyn (indexValue (wmod 1))
  let c ← st.heap.index independent .dyn (indexValue (wmod 0))
  pure [st.H.length,(TEnv.get (.here : Idx Final (.val .uint)) st.env).val,
    (TEnv.get (.there .here : Idx Final (.val .uint)) st.env).val,
    (TEnv.get (.there (.there .here) : Idx Final (.val .bool)) st.env).toNat,
    (TEnv.get (.there (.there (.there .here)) : Idx Final (.val .uint)) st.env).val,
    dest.id,saved.id,independent.id,st.heap.len saved .dyn,a.val,z.val,st.heap.len independent .dyn,c.val]

theorem ordered_source_prefixes :
    initial.H = [] ∧ allocatedVector = some [2,0,0,0,1,2,7,9,1,4] ∧
    selectedVector (state true) = some [2,1,0,0,0,1,2,7,9,1,4] ∧
    selectedVector (middle true).st = some [2,1,4,1,0,1,2,7,9,1,4] ∧
    selectedVector (state false) = some [2,0,0,0,0,1,2,7,9,1,4] ∧
    selectedVector (middle false).st = some [2,0,7,0,0,1,2,7,9,1,4] ∧
    capturedVector true = some [2,4,1,4,1,0,1,2,7,9,1,5] ∧
    capturedVector false = some [2,7,0,7,0,0,1,2,8,9,1,4] ∧
    oppositeVector = some [2,9,7,0,7,0,0,1,2,8,9,1,4] := by
  exact ⟨rfl,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

def wrongCapture : Memory.CompiledProg 1 wrongReceiver.frag capturePrefix :=
  (Memory.compileProg 1 _ capturePrefix).get (by decide +kernel)
private def wrongPrefix : List Instr :=
  population.code ++ ((initializer true).code ++ (wrongReceiver.code ++ wrongCapture.code))

theorem wrong_order_complete_prefix :
    words (run wrongPrefix {initialMachine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,259,7,1,4,0,2,7,9,1,5] ∧
    words (run wrongPrefix {initialMachine with stack := [w[77],w[88]]}) ≠
      some [77,88,261,99,259,256,259,4,1,4,0,2,7,9,1,5] := by
  exact ⟨by decide +kernel,by decide +kernel⟩

theorem skipped_capture_prefix :
    words (run (throughReceiver true) {initialMachine with stack := [w[77],w[88]]}) ≠
      some [77,88,261,99,259,256,259,4,1,4,0,2,7,9,1,5] := by decide +kernel

theorem corrupted_tail_prefix :
    words (run (prefixCode true) {initialMachine with stack := [w[88],w[77]]}) ≠
      some [77,88,261,99,259,256,259,4,1,4,0,2,7,9,1,5] := by decide +kernel

/-- Coarse revert itself exposes NO saved stack. Tail discrimination above
is deliberately before failure, not an invented post-failure machine. -/
theorem corrupted_tail_still_reverts :
    run (wholeCode true) {initialMachine with stack := [w[88],w[77]]} = .revert :=
  (fresh_revert [w[88],w[77]]).2.1

theorem insufficient_observer_frame {base : Nat → Fin W} {st : State C Captured} {m : Machine} :
    ¬ (Compilation.memory badStage).Input 1 7 base st m := by
  intro h
  have cap := h.2.1
  change 1 + 7 ≤ 7 at cap
  omega

theorem stale_initial_map (m : Machine) :
    ¬ (Compilation.memory badStage).Input 1 128 initialBase (afterCapture true).st m := by
  intro h
  let old := CompileExamples.r0.wk ((middle true).ext.trans (afterCapture true).ext)
  have bound := h.1.heap.above old
  change 128 ≤ 0 at bound
  omega

theorem ordinary_failure_not_panic_or_divergence :
    (wholeProgram true).run initial ≠ .error .panic ∧
    (wholeProgram true).run initial ≠ .error .diverge := by
  rw [source_revert]
  constructor <;> intro h <;> cases h

theorem reached_failure_not_target_fault (tail : List Word) :
    run (wholeCode true) {initialMachine with stack := tail} ≠ .fault := by
  rw [(fresh_revert tail).2.1]
  intro h
  cases h

end Solidity.Backend.Passes.FreshBooleanControls
