import Solidity.Backend.MemoryCopies.CheckedReference
import Solidity.Evm.MemoryObjectArrayExamples

/-! Populated nested runtime defaults, oversized children, and exact division
bounds use actual guarded execution, never a desired target-run premise. -/
namespace Solidity.Backend.MemoryCopies.CheckedReferenceControls
open Evm Evm.Memory
private def element : Ty := .ref (.array (.prim .uint))
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_,_,_,_,ObjectArrayExamples.initial_allocator⟩
private def chosen (dimensions : List Nat) :
    SelectedCheckedDefault (nestedArrayType element dimensions) (nested_mapFree element dimensions) :=
  checkedNestedDefault element dimensions (nested_mapFree element dimensions)
private def observe : Evm.Out → Option (Nat × Nat × Nat)
  | .ok machine _ => match machine.stack,machine.mem 0,machine.mem 17 with
    | .val root :: _,.val cursor,.val old => some (root.val,cursor.val,old.val)
    | _,_,_ => none
  | _ => none

theorem certificate_inhabited : CheckedReferenceCertificate := checkedReference

theorem runtime_observation (dimensions : List Nat) (size : Fin W)
    (fits : 40 + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions))) < W) :
    observe (run (checkedReferenceCode (chosen dimensions)) (input.machine.push (.val size))) =
      some (40,40 + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions))),7) := by
  obtain ⟨base,target,ran,allocated,_,_,_,below,_⟩ :=
    checked_reference_success (chosen dimensions) input.heap size input.base 8 (wmod 40) input.machine input.allocator fits
  rw [ran]
  simp only [observe,Machine.push]
  rw [allocated.free.cell,below 17 (by decide) (by decide)]
  rfl

theorem empty_parent : observe (run (checkedReferenceCode (chosen [2,3])) (input.machine.push (.val (wmod 0)))) = some (40,41,7) :=
  runtime_observation [2,3] (wmod 0) (by decide)

theorem two_nested_children : observe (run (checkedReferenceCode (chosen [2,3])) (input.machine.push (.val (wmod 2)))) = some (40,71,7) :=
  runtime_observation [2,3] (wmod 2) (by decide)

theorem long_parent : observe (run (checkedReferenceCode (chosen [2,3])) (input.machine.push (.val (wmod 64)))) = some (40,1001,7) :=
  runtime_observation [2,3] (wmod 64) (by decide)

theorem empty_any_child (dimensions : List Nat) :
    observe (run (checkedReferenceCode (chosen dimensions)) (input.machine.push (.val (wmod 0)))) = some (40,41,7) := by
  have fits : 40 + ((wmod 0).val + 1 + (wmod 0).val * ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions))) < W := by
    simp only [show (wmod 0).val = 0 from rfl,Nat.zero_add,Nat.zero_mul,Nat.add_zero]
    decide
  simpa only [show (wmod 0).val = 0 from rfl,Nat.zero_add,Nat.zero_mul,Nat.add_zero] using runtime_observation dimensions (wmod 0) fits

theorem empty_oversized_child :
    observe (run (checkedReferenceCode (chosen [W])) (input.machine.push (.val (wmod 0)))) = some (40,41,7) :=
  empty_any_child [W]

theorem oversized_child_refusal :
    run (checkedReferenceCode (chosen [W])) (input.machine.push (.val (wmod 1))) = .revert := by
  rw [checked_reference_run (chosen [W]) input.heap (wmod 1) input.base 8 (wmod 40) input.machine input.allocator]
  apply if_neg
  change ¬ (40 + (1 + 1 + 1 * (max 1 W + W * 1)) < W)
  omega

theorem maximal_parent_refusal :
    run (checkedReferenceCode (chosen [2,3])) (input.machine.push (.val wMax)) = .revert := by
  rw [checked_reference_run (chosen [2,3]) input.heap wMax input.base 8 (wmod 40) input.machine input.allocator]
  apply if_neg
  change ¬ (40 + (W - 1 + 1 + (W - 1) * 14) < W)
  have positive : 0 < W := W_pos
  omega

private def moved (cursor : Fin W) : Machine := writeMachine input.machine 0 (.val cursor)
private theorem moved_allocator (cursor : Fin W) (above : 40 ≤ cursor.val) :
    Objects.AllocatorRepr input.heap input.base 8 cursor (moved cursor) := by
  refine ⟨input.allocator.heap.localWrite 0 (by decide) (.val cursor),⟨by decide,by omega,?_,?_⟩,?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (input.allocator.free.zero address (by change 40 ≤ address; omega))
  · intro Q reference
    have oldLive : (input.base reference.id).val + Objects.cells input.heap reference ≤ 40 := input.allocator.live reference
    omega

private theorem last_cursor : (wmod (W - 32)).val = W - 32 := Nat.mod_eq_of_lt (by
  have large : 32 ≤ W := by decide
  omega)
private theorem last_above : 40 ≤ (wmod (W - 32)).val := by
  rw [last_cursor]
  have large : 128 < W := by decide
  omega

theorem last_fitting_pair : ∃ fits,
    CheckedReferenceResult (chosen [2,3]) input.heap (wmod 2) input.base 8 (wmod (W - 32)) (moved (wmod (W - 32))) fits := by
  have fits : (wmod (W - 32)).val + ((wmod 2).val + 1 + (wmod 2).val * ReferenceDefaults.defaultCells (.ref (nestedArrayType element [2,3]))) < W := by
    rw [last_cursor]
    change W - 32 + (2 + 1 + 2 * 14) < W
    have large : 32 ≤ W := by decide
    omega
  exact ⟨fits,checked_reference_success (chosen [2,3]) input.heap (wmod 2) input.base 8 (wmod (W - 32))
    (moved (wmod (W - 32))) (moved_allocator _ last_above) fits⟩

theorem next_length_refusal :
    run (checkedReferenceCode (chosen [2,3])) ((moved (wmod (W - 32))).push (.val (wmod 3))) = .revert := by
  rw [checked_reference_run (chosen [2,3]) input.heap (wmod 3) input.base 8 (wmod (W - 32))
    (moved (wmod (W - 32))) (moved_allocator _ last_above),last_cursor]
  apply if_neg
  change ¬ (W - 32 + (3 + 1 + 3 * 14) < W)
  have large : 32 ≤ W := by decide
  omega

theorem wrong_cursor_rejected :
    observe (run (checkedReferenceCode (chosen [2,3])) (input.machine.push (.val (wmod 2)))) ≠ some (40,70,7) := by
  rw [two_nested_children]
  decide

#print axioms certificate_inhabited
#print axioms runtime_observation
#print axioms empty_parent
#print axioms two_nested_children
#print axioms long_parent
#print axioms empty_any_child
#print axioms empty_oversized_child
#print axioms oversized_child_refusal
#print axioms maximal_parent_refusal
#print axioms last_fitting_pair
#print axioms next_length_refusal
#print axioms wrong_cursor_rejected
end Solidity.Backend.MemoryCopies.CheckedReferenceControls
