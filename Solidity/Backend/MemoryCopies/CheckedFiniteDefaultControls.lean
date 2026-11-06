import Solidity.Backend.MemoryCopies.CheckedFiniteDefault
import Solidity.Evm.MemoryStructDefaultExamples

/-! Actual existing plans with nonzero parent offsets, declaration binding,
retained old objects and fully represented saturated input controls. -/
namespace Solidity.Backend.MemoryCopies.CheckedFiniteDefaultControls
open Evm Evm.Memory

private structure Input where
  C : Contract
  state : State C []
  base : Nat → Fin W
  machine : Machine
  represented : StateRepr 1 1 64 (Frag.init []) state base machine
  allocator : StructAllocatorRepr state.heap base 64 (wmod 128) machine
private def input : Input :=
  ⟨_, _, _, _, StructDefaultExamples.initial_repr.1, StructDefaultExamples.initial_repr.2⟩
private def basket : DefaultPlan (.struct "Basket") :=
  (defaultPlan? (.struct "Basket")).get (by decide +kernel)
private def person : DefaultPlan (.struct "Person") :=
  (defaultPlan? (.struct "Person")).get (by decide +kernel)
private def array : DefaultPlan (.array (.prim .uint)) := DefaultPlan.array .uint
private def observe : Evm.Out → Option (Nat × Nat × Nat)
  | .ok machine _ => match machine.stack, machine.mem 0, machine.mem 63 with
    | .val root :: _, .val cursor, .val old => some (root.val, cursor.val, old.val)
    | _, _, _ => none
  | _ => none
private def reached : Evm.Out → Option Machine
  | .ok machine _ => some machine
  | _ => none
private def binding : Evm.Out → Option (Nat × Nat × List Word)
  | .ok machine _ => match machine.mem 1, machine.mem 0 with
    | .val root, .val cursor => some (root.val, cursor.val, machine.stack)
    | _, _ => none
  | _ => none
private def sourceObserve {R : RefTy}
    (result : TRes (Solidity.Out input.C input.state.H [.mem R])) : Option (Nat × Nat × Nat) := do
  let out ← result.toOption
  let reference ← TEnv.get .here out.st.env
  pure (reference.id, heapWords out.st.heap, out.st.H.length)

theorem certificate_inhabited : CheckedFiniteDefaultCertificate := checkedFiniteDefault

theorem root_offsets : basket.root = 1 ∧ basket.cost = 2 ∧ person.root = 3 ∧ person.cost = 5 := by
  decide +kernel

theorem body_observations :
    observe (run (checkedFiniteDefaultCode basket []) input.machine) = some (129, 130, 99) ∧
    observe (run (checkedFiniteDefaultCode person []) input.machine) = some (131, 133, 99) ∧
    observe (run (checkedFiniteDefaultCode array []) input.machine) = some (128, 129, 99) := by
  decide +kernel

theorem declaration_observations :
    binding (run (checkedFiniteDefaultCode basket [.mstore (cell 1)]) input.machine) = some (129, 130, [w[77]]) ∧
    binding (run (checkedFiniteDefaultCode person [.mstore (cell 1)]) input.machine) = some (131, 133, [w[77]]) := by
  decide +kernel

theorem source_declarations :
    sourceObserve (TRun.declMem (.struct "Basket") none rfl input.state) = some (1, 2, 2) ∧
    sourceObserve (TRun.declMem (.struct "Person") none rfl input.state) = some (2, 5, 3) := by
  decide +kernel

theorem actual_body_contract :
    (∃ fits, FiniteDefaultSuccess (L := 1) (b := 1) (frame := 64) (F := Frag.init [])
      person input.state input.base (wmod 128) input.machine rfl fits) ∨
    (¬ (wmod 128).val + person.cost < W ∧
      run (checkedFiniteDefaultCode person []) input.machine = .revert) :=
  checked_finite_default person input.state input.base (wmod 128) input.machine rfl
    input.represented input.allocator (by decide)

theorem actual_declaration_contract :
    GrowingResult 1 1 64 person.cost ((Frag.init []).push (.mem (.struct "Person")) .ok)
      input.state input.base input.machine (TRun.declMem (.struct "Person") none rfl input.state)
      (run (checkedFiniteDefaultCode person [.mstore (cell 1)]) input.machine) ∨
    (¬ (wmod 128).val + person.cost < W ∧
      run (checkedFiniteDefaultCode person [.mstore (cell 1)]) input.machine = .revert) :=
  checked_finite_declaration person input.state input.base (wmod 128) input.machine rfl
    input.represented input.allocator (by decide) (by decide)

/-- A second plan allocation leaves the first child's header and parent pointer. -/
theorem old_children_retained :
    (do let first ← reached (run (checkedFiniteDefaultCode basket []) input.machine)
        let second ← reached (run (checkedFiniteDefaultCode person []) first)
        pure (second.mem 128, second.mem 129, second.mem 0, second.stack)) =
      some (w[0], w[128], w[135], [w[133], w[129], w[77]]) := by decide +kernel

private def saturated : Machine := writeMachine input.machine 0 (.val wMax)
private theorem noRef {R : RefTy} (reference : HRef input.state.H R) : False := by
  cases reference.get?

private theorem saturated_represented :
    StateRepr 1 1 64 (Frag.init []) input.state input.base saturated := by
  refine ⟨input.represented.core.congrMem ?_, ?_, ?_, input.represented.locals, ?_,
    input.represented.separated, ?_⟩
  · intro slot lower upper
    change slot < 1 at upper
    omega
  · exact ⟨fun reference => (noRef reference).elim, fun reference => (noRef reference).elim,
      fun reference => (noRef reference).elim⟩
  · intro R index; nomatch index
  · exact ⟨fun reference => (noRef reference).elim, fun reference => (noRef reference).elim,
      fun reference => (noRef reference).elim⟩
  · intro s field R reference found
    exact (noRef reference).elim

private theorem saturated_allocator :
    StructAllocatorRepr input.state.heap input.base 64 wMax saturated := by
  refine ⟨⟨?_, ?_, fun reference => (noRef reference).elim⟩, ?_, input.allocator.separated,
    fun reference => (noRef reference).elim⟩
  · exact ⟨fun reference => (noRef reference).elim, fun reference => (noRef reference).elim,
      fun reference => (noRef reference).elim⟩
  · refine ⟨by decide, by decide +kernel, ?_, ?_⟩
    · change upd input.machine.mem 0 (.val wMax) 0 = .val wMax
      exact upd_same _ _ _
    · intro address above
      have positive : 0 < wMax.val := by decide +kernel
      have old : (wmod 128).val ≤ address := by
        have bound : (wmod 128).val ≤ wMax.val := by decide +kernel
        omega
      exact (upd_other _ _ (by omega : address ≠ 0)).trans (input.allocator.arrays.free.zero address old)
  · exact ⟨fun reference => (noRef reference).elim, fun reference => (noRef reference).elim,
      fun reference => (noRef reference).elim⟩

theorem saturated_inputs_inhabited :
    StateRepr 1 1 64 (Frag.init []) input.state input.base saturated ∧
    StructAllocatorRepr input.state.heap input.base 64 wMax saturated :=
  ⟨saturated_represented, saturated_allocator⟩

theorem saturated_refusals : run (checkedFiniteDefaultCode basket []) saturated = .revert ∧
    run (checkedFiniteDefaultCode person []) saturated = .revert ∧
    run (checkedFiniteDefaultCode array []) saturated = .revert ∧
    run (checkedFiniteDefaultCode person [.mstore (cell 1)]) saturated = .revert := by
  have refusing : ∀ {R : RefTy} (plan : DefaultPlan R) (suffix : List Instr),
      run (checkedFiniteDefaultCode plan suffix) saturated = .revert := by
    intro R plan suffix
    rw [checked_finite_run plan suffix saturated wMax saturated_allocator.arrays.free.cell]
    apply if_neg
    have positive : 0 < plan.cost := finite_default_positive plan
    change ¬ (W - 1 + plan.cost < W)
    have bound : 0 < W := W_pos
    omega
  exact ⟨refusing basket [], refusing person [], refusing array [], refusing person _⟩

theorem wrong_parent_address_rejected :
    observe (run (checkedFiniteDefaultCode basket []) input.machine) ≠ some (128, 130, 99) := by
  rw [body_observations.1]
  decide

theorem empty_code_rejected : checkedFiniteDefaultCode person [] ≠ [] := by
  intro empty
  have correct : observe (run (checkedFiniteDefaultCode person []) input.machine) = some (131, 133, 99) :=
    body_observations.2.1
  rw [empty] at correct
  have initial : observe (run [] input.machine) = some (77, 128, 99) := rfl
  rw [initial] at correct
  cases correct

#print axioms certificate_inhabited
#print axioms root_offsets
#print axioms body_observations
#print axioms declaration_observations
#print axioms source_declarations
#print axioms actual_body_contract
#print axioms actual_declaration_contract
#print axioms old_children_retained
#print axioms saturated_inputs_inhabited
#print axioms saturated_refusals
#print axioms wrong_parent_address_rejected
#print axioms empty_code_rejected
end Solidity.Backend.MemoryCopies.CheckedFiniteDefaultControls
