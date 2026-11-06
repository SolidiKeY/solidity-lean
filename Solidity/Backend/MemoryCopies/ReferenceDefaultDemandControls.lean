import Solidity.Backend.MemoryCopies.ReferenceDefaultDemand
import Solidity.Backend.MemoryCopies.HeapContents
import Solidity.Evm.MemoryObjectArrayExamples

/-! Actual populated runtime reference defaults with empty/long parents,
unused huge children, explicit new-child contents and separate real refusals. -/
namespace Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls
open Evm Evm.Memory

private def chosen (dimensions : List Nat) :
    SelectedCheckedDefault (nestedArrayType (.prim .uint) dimensions)
      (nested_mapFree (.prim .uint) dimensions) :=
  checkedNestedDefault (.prim .uint) dimensions (nested_mapFree (.prim .uint) dimensions)
private def token : SelectedCheckedDefault (.struct "Token") rfl :=
  selectedCheckedDefault _ rfl rfl
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_, _, _, _, ObjectArrayExamples.initial_allocator⟩
private def observe : Evm.Out → Option (Nat × Nat × Nat)
  | .ok machine _ => match machine.stack, machine.mem 0, machine.mem 17 with
    | .val root :: _, .val cursor, .val old => some (root.val,cursor.val,old.val)
    | _, _, _ => none
  | _ => none

private theorem observe_cost {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) (size : Fin W)
    (fits : 40 + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < W) :
    observe (run (checkedReferenceCode selected) (input.machine.push (.val size))) =
      some (40,40 + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)),7) := by
  obtain ⟨base,target,ran,allocated,_,_,_,below,_⟩ :=
    checked_reference_success selected input.heap size input.base 8 (wmod 40) input.machine input.allocator fits
  rw [ran]
  simp only [observe, Machine.push]
  rw [allocated.free.cell, below 17 (by decide) (by decide)]
  rfl

theorem certificate_inhabited : ReferenceDefaultDemandCertificate := referenceDefaultDemand

theorem semantic_demands :
    referenceDefaultWords (.array (.prim .uint)) (wmod 0) = 1 ∧
    referenceDefaultWords (.array (.prim .uint)) (wmod 2) = 5 ∧
    referenceDefaultWords (.array (.prim .uint)) (wmod 64) = 129 ∧
    referenceDefaultWords (.struct "Token") (wmod 2) = 5 := by
  rw [reference_default_words (root := .array (.prim .uint)) (chosen []) (wmod 0),
    reference_default_words (root := .array (.prim .uint)) (chosen []) (wmod 2), reference_default_words (root := .array (.prim .uint)) (chosen []) (wmod 64),
    reference_default_words token (wmod 2)]
  decide +kernel

theorem empty_parent :
    observe (run (checkedReferenceCode (chosen [])) (input.machine.push w[0])) = some (40,41,7) :=
  observe_cost (chosen []) (wmod 0) (by decide)

theorem two_children :
    observe (run (checkedReferenceCode (chosen [])) (input.machine.push w[2])) = some (40,45,7) :=
  observe_cost (chosen []) (wmod 2) (by decide)

theorem long_parent :
    observe (run (checkedReferenceCode (chosen [])) (input.machine.push w[64])) = some (40,169,7) :=
  observe_cost (chosen []) (wmod 64) (by decide)

theorem token_children :
    observe (run (checkedReferenceCode token) (input.machine.push w[2])) = some (40,45,7) :=
  observe_cost token (wmod 2) (by decide)

private def emptyChild : SVal (.ref (.array (.prim .uint))) := .array .nil .nil (by decide)
private def expected : SVal (.ref (.array (.ref (.array (.prim .uint))))) :=
  .array (SVec.replicate emptyChild 2) .nil (by decide)

private theorem strip_replicate {T : Ty} (value : SVal T) (count : Nat) :
    (SVec.replicate value count).strip = SVec.replicate value.strip count := by
  induction count with
  | zero => simp only [SVec.replicate, SVec.strip_nil]
  | succ count previous => simp only [SVec.replicate, SVec.strip_cons, previous]

theorem actual_contents :
    ∃ fits : (wmod 40).val + ((wmod 2).val + 1 + (wmod 2).val *
        ReferenceDefaults.defaultCells (.ref (.array (.prim .uint)))) < W,
      CheckedReferenceResult (chosen []) input.heap (wmod 2) input.base 8 (wmod 40) input.machine fits ∧
      let grown := Objects.referenceArrayCopy input.heap (.array (.prim .uint)) rfl (wmod 2)
      MVal.copyMToSt grown.heap grown.val = expected := by
  refine ⟨by decide, checked_reference_success (chosen []) input.heap (wmod 2) input.base 8
    (wmod 40) input.machine input.allocator (by decide), ?_⟩
  rw [← reference_default_copy input.heap (.array (.prim .uint)) rfl (wmod 2)]
  exact ((storageHeapContents (referenceDefaultValue (.array (.prim .uint)) (wmod 2)) rfl).contents
    input.heap).trans (by
      simp only [referenceDefaultValue, SVal.strip_array, strip_replicate, SVal.dflt_array,
        SVec.strip_nil, expected, emptyChild]
      rfl)


theorem unused_huge_child :
    observe (run (checkedReferenceCode (chosen [W])) (input.machine.push w[0])) = some (40,41,7) :=
  observe_cost (chosen [W]) (wmod 0) (by
    change 40 + (0 + 1 + 0 * (max 1 W + W * 1)) < W
    simp only [Nat.zero_add, Nat.zero_mul, Nat.add_zero]
    decide)

theorem huge_child_refusal : run (checkedReferenceCode (chosen [W])) (input.machine.push w[1]) = .revert := by
  change run (checkedReferenceCode (chosen [W])) (input.machine.push (.val (wmod 1))) = .revert
  rw [checked_reference_run (chosen [W]) input.heap (wmod 1) input.base 8 (wmod 40)
    input.machine input.allocator]
  apply if_neg
  change ¬ 40 + (1 + 1 + 1 * (max 1 W + W * 1)) < W
  have lower : W ≤ max 1 W := Nat.le_max_right _ _
  omega

theorem huge_parent_refusal : run (checkedReferenceCode (chosen [])) (input.machine.push (.val wMax)) = .revert := by
  rw [checked_reference_run (chosen []) input.heap wMax input.base 8 (wmod 40)
    input.machine input.allocator]
  apply if_neg
  change ¬ 40 + (W - 1 + 1 + (W - 1) * 1) < W
  have positive : 0 < W := W_pos
  omega

theorem unselected_account :
    ReferenceDefaults.compileDefault (.struct "Account") rfl = none ∧
    referenceDefaultWords (.struct "Account") (wmod 1) = 5 ∧
    (wmod 1).val + 1 + (wmod 1).val * ReferenceDefaults.defaultCells (.ref (.struct "Account")) = 4 := by
  refine ⟨rfl, ?_, rfl⟩
  decide +kernel

theorem wrong_cursor_rejected :
    observe (run (checkedReferenceCode (chosen [])) (input.machine.push w[2])) ≠ some (40,44,7) := by
  rw [two_children]
  decide

/--
info: 'Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls.certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls.semantic_demands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms semantic_demands
/--
info: 'Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls.empty_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_parent
/--
info: 'Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls.two_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms two_children
/--
info: 'Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls.long_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms long_parent
/--
info: 'Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls.token_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms token_children
/--
info: 'Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls.actual_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_contents
/--
info: 'Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls.unused_huge_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms unused_huge_child
/--
info: 'Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls.huge_child_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms huge_child_refusal
/--
info: 'Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls.huge_parent_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms huge_parent_refusal
/--
info: 'Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls.unselected_account' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms unselected_account
/--
info: 'Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls.wrong_cursor_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_cursor_rejected
end Solidity.Backend.MemoryCopies.ReferenceDefaultDemandControls
