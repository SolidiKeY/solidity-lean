import Solidity.Backend.MemoryCopies.BudgetedReference
import Solidity.Backend.MemoryCopies.HeapContents
import Solidity.Evm.MemoryObjectArrayExamples

/-! Actual populated runtime reference defaults with empty/long parents,
unused huge children, explicit new-child contents and separate real refusals. -/
namespace Solidity.Backend.MemoryCopies.BudgetedReferenceControls
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
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory) (size : Fin W)
    (fits : (wmod 40).val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < limit.val) :
    observe (run (budgetedReferenceCode limit selected) (input.machine.push (.val size))) =
      some (40,40 + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)),7) := by
  obtain ⟨base,target,ran,allocated,_,_,_,below,_⟩ :=
    Objects.referenceArray_correct selected.builder input.heap size input.base 8 input.machine (wmod 40)
      input.allocator (Nat.lt_of_lt_of_le fits (Nat.le_of_lt_succ limit.isLt))
  rw [budgeted_reference_run limit selected input.heap size input.base 8 (wmod 40) input.machine input.allocator,if_pos fits,ran]
  simp only [observe, Machine.push]
  rw [allocated.free.cell, below 17 (by decide) (by decide)]
  rfl

theorem certificate_inhabited : BudgetedReferenceCertificate := budgetedReference

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
    observe (run (budgetedReferenceCode ⟨46,by decide⟩ (chosen [])) (input.machine.push w[0])) = some (40,41,7) :=
  observe_cost ⟨46,by decide⟩ (chosen []) (wmod 0) (by decide)

theorem two_children :
    observe (run (budgetedReferenceCode ⟨46,by decide⟩ (chosen [])) (input.machine.push w[2])) = some (40,45,7) :=
  observe_cost ⟨46,by decide⟩ (chosen []) (wmod 2) (by decide)

theorem long_parent :
    observe (run (budgetedReferenceCode ⟨170,by decide⟩ (chosen [])) (input.machine.push w[64])) = some (40,169,7) :=
  observe_cost ⟨170,by decide⟩ (chosen []) (wmod 64) (by decide)

theorem token_children :
    observe (run (budgetedReferenceCode ⟨46,by decide⟩ token) (input.machine.push w[2])) = some (40,45,7) :=
  observe_cost ⟨46,by decide⟩ token (wmod 2) (by decide)

private def emptyChild : SVal (.ref (.array (.prim .uint))) := .array .nil .nil (by decide)
private def expected : SVal (.ref (.array (.ref (.array (.prim .uint))))) :=
  .array (SVec.replicate emptyChild 2) .nil (by decide)

private theorem strip_replicate {T : Ty} (value : SVal T) (count : Nat) :
    (SVec.replicate value count).strip = SVec.replicate value.strip count := by
  induction count with
  | zero => simp only [SVec.replicate, SVec.strip_nil]
  | succ count previous => simp only [SVec.replicate, SVec.strip_cons, previous]

theorem actual_contents :
    ∃ fits : (wmod 40).val + referenceDefaultWords (.array (.prim .uint)) (wmod 2) < 46,
      BudgetedReferenceResult ⟨46,by decide⟩ (chosen []) input.heap (wmod 2) input.base 8 (wmod 40) input.machine fits ∧
      let grown := Objects.referenceArrayCopy input.heap (.array (.prim .uint)) rfl (wmod 2)
      MVal.copyMToSt grown.heap grown.val = expected := by
  refine ⟨by
      change (wmod 40).val + referenceDefaultWords (.array (.prim .uint)) (wmod 2) < 46
      rw [reference_default_words (root := .array (.prim .uint)) (chosen [])]
      decide, budgeted_reference_success ⟨46,by decide⟩ (chosen []) input.heap (wmod 2) input.base 8
    (wmod 40) input.machine input.allocator (by
      change (wmod 40).val + referenceDefaultWords (.array (.prim .uint)) (wmod 2) < 46
      rw [reference_default_words (root := .array (.prim .uint)) (chosen [])]
      decide), ?_⟩
  rw [← reference_default_copy input.heap (.array (.prim .uint)) rfl (wmod 2)]
  exact ((storageHeapContents (referenceDefaultValue (.array (.prim .uint)) (wmod 2)) rfl).contents
    input.heap).trans (by
      simp only [referenceDefaultValue, SVal.strip_array, strip_replicate, SVal.dflt_array,
        SVec.strip_nil, expected, emptyChild]
      rfl)


theorem unused_huge_child :
    observe (run (budgetedReferenceCode ⟨42,by decide⟩ (chosen [W])) (input.machine.push w[0])) = some (40,41,7) :=
  observe_cost ⟨42,by decide⟩ (chosen [W]) (wmod 0) (by
    change 40 + (0 + 1 + 0 * (max 1 W + W * 1)) < 42
    simp only [Nat.zero_add, Nat.zero_mul, Nat.add_zero]
    decide)

theorem huge_child_refusal : run (budgetedReferenceCode ⟨42,by decide⟩ (chosen [W])) (input.machine.push w[1]) = .revert := by
  change run (budgetedReferenceCode ⟨42,by decide⟩ (chosen [W])) (input.machine.push (.val (wmod 1))) = .revert
  rw [budgeted_reference_run ⟨42,by decide⟩ (chosen [W]) input.heap (wmod 1) input.base 8 (wmod 40)
    input.machine input.allocator]
  apply if_neg
  change ¬ 40 + (1 + 1 + 1 * (max 1 W + W * 1)) < 42
  have lower : W ≤ max 1 W := Nat.le_max_right _ _
  omega

theorem huge_parent_refusal : run (budgetedReferenceCode ⟨46,by decide⟩ (chosen [])) (input.machine.push (.val wMax)) = .revert := by
  rw [budgeted_reference_run ⟨46,by decide⟩ (chosen []) input.heap wMax input.base 8 (wmod 40)
    input.machine input.allocator]
  apply if_neg
  change ¬ 40 + (W - 1 + 1 + (W - 1) * 1) < 46
  have large : 46 < W := by decide
  omega

theorem unselected_account :
    ReferenceDefaults.compileDefault (.struct "Account") rfl = none ∧
    referenceDefaultWords (.struct "Account") (wmod 1) = 5 ∧
    (wmod 1).val + 1 + (wmod 1).val * ReferenceDefaults.defaultCells (.ref (.struct "Account")) = 4 := by
  refine ⟨rfl, ?_, rfl⟩
  decide +kernel

theorem wrong_cursor_rejected :
    observe (run (budgetedReferenceCode ⟨46,by decide⟩ (chosen [])) (input.machine.push w[2])) ≠ some (40,44,7) := by
  rw [two_children]
  decide

theorem strict_boundary_refusal :
    run (budgetedReferenceCode ⟨45,by decide⟩ (chosen [])) (input.machine.push w[2]) = .revert := by
  rw [budgeted_reference_run _ _ _ _ _ _ _ _ input.allocator]
  rw [if_neg (by decide)]

theorem zero_budget_refusal :
    run (budgetedReferenceCode ⟨0,by decide⟩ (chosen [])) (input.machine.push w[0]) = .revert := by
  rw [budgeted_reference_run _ _ _ _ _ _ _ _ input.allocator]
  rw [if_neg (by decide)]

theorem full_budget_code {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) :
    budgetedReferenceCode ⟨W,Nat.lt_succ_self W⟩ selected = checkedReferenceCode selected := by
  simp only [budgetedReferenceCode,referenceBudgetGuard,budgetDefaultGuard,Nat.sub_self,Nat.zero_add,
    referenceBudgetTail,checkedReferenceCode,referenceCapacityGuard,referenceCapacityTail]

/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.semantic_demands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms semantic_demands
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.empty_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_parent
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.two_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms two_children
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.long_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms long_parent
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.token_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms token_children
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.actual_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_contents
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.unused_huge_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms unused_huge_child
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.huge_child_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms huge_child_refusal
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.huge_parent_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms huge_parent_refusal
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.unselected_account' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms unselected_account
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.wrong_cursor_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_cursor_rejected
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.strict_boundary_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms strict_boundary_refusal
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.zero_budget_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms zero_budget_refusal
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedReferenceControls.full_budget_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms full_budget_code
end Solidity.Backend.MemoryCopies.BudgetedReferenceControls
