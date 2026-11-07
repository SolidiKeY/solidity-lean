import Solidity.Backend.MemoryCopies.BudgetedDefault
import Solidity.Evm.MemoryObjectArrayExamples
import Solidity.Backend.MemoryCopies.HeapContents

/-! Actual represented allocations distinguish strict budget refusal from
successful empty and nested defaults. Address bounds do not assert byte execution. -/
namespace Solidity.Backend.MemoryCopies.BudgetedDefaultControls
open Evm Evm.Memory

private def element : Ty := .ref (.array (.prim .uint))
private def chosen (dimensions : List Nat) :
    SelectedCheckedDefault (nestedArrayType element dimensions) (nested_mapFree element dimensions) :=
  checkedNestedDefault element dimensions (nested_mapFree element dimensions)
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_, _, _, _, ObjectArrayExamples.initial_allocator⟩
private def observe : Evm.Out → Option (Nat × Nat × Nat)
  | .ok machine _ => match machine.stack, machine.mem 0, machine.mem 17 with
    | .val root :: _, .val cursor, .val old => some (root.val, cursor.val, old.val)
    | _, _, _ => none
  | _ => none

theorem certificate_inhabited : BudgetedDefaultCertificate := budgetedDefault

theorem full_budget_code {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) :
    budgetedDefaultCode ⟨W, Nat.lt_succ_self W⟩ selected = selected.code := by
  simp only [budgetedDefaultCode, budgetDefaultGuard, Nat.sub_self, Nat.zero_add,
    SelectedCheckedDefault.code]

private theorem actual_success (limit : Fin (W + 1)) (dimensions : List Nat)
    (fits : (wmod 40).val + ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions)) < limit.val) :
    observe (run (budgetedDefaultCode limit (chosen dimensions)) input.machine) =
      some (40, 40 + ReferenceDefaults.defaultCells (.ref (nestedArrayType element dimensions)), 7) := by
  obtain ⟨base, target, ran, allocated, _, _, _, below, _⟩ :=
    budgeted_default_success limit (chosen dimensions) input.heap input.base 8 (wmod 40)
      input.machine input.allocator fits
  rw [ran]
  simp only [observe, Machine.push]
  rw [allocated.free.cell, below 17 (by decide) (by decide)]
  rfl

theorem empty_success :
    observe (run (budgetedDefaultCode ⟨42,by decide⟩ (chosen [])) input.machine) = some (40,41,7) :=
  actual_success ⟨42,by decide⟩ [] (by decide)

theorem nested_success :
    observe (run (budgetedDefaultCode ⟨55,by decide⟩ (chosen [2,3])) input.machine) = some (40,54,7) :=
  actual_success ⟨55,by decide⟩ [2,3] (by decide)

theorem nested_refusal :
    run (budgetedDefaultCode ⟨54,by decide⟩ (chosen [2,3])) input.machine = .revert := by
  rw [budgeted_default_run _ _ _ _ _ _ _ input.allocator]
  rw [if_neg (by decide)]

theorem zero_budget_refusal :
    run (budgetedDefaultCode ⟨0,by decide⟩ (chosen [])) input.machine = .revert := by
  rw [budgeted_default_run _ _ _ _ _ _ _ input.allocator]
  rw [if_neg (by decide)]

theorem wrong_cursor_rejected :
    observe (run (budgetedDefaultCode ⟨55,by decide⟩ (chosen [2,3])) input.machine) ≠ some (40,55,7) := by
  rw [nested_success]
  decide

private def emptyChild : SVal (.ref (.array element)) := .array .nil .nil (by decide)
private def expectedChildren : SVal (.ref (nestedArrayType element [2,3])) :=
  .fixed (SVec.replicate (.fixed (SVec.replicate emptyChild 3)) 2)

theorem nested_actual_contents :
    ∃ fits : (wmod 40).val + ReferenceDefaults.defaultCells (.ref (nestedArrayType element [2,3])) < 55,
      BudgetedDefaultSuccess ⟨55,by decide⟩ (chosen [2,3]) input.heap input.base 8
        (wmod 40) input.machine fits ∧
      let grown := input.heap.allocDefault (nestedArrayType element [2,3]) (nested_mapFree element [2,3])
      MVal.copyMToSt grown.heap grown.val = expectedChildren := by
  refine ⟨by decide, budgeted_default_success _ _ _ _ _ _ _ input.allocator (by decide), ?_⟩
  exact ((storageHeapContents (SVal.dflt (.ref (nestedArrayType element [2,3])))
    (nested_mapFree element [2,3])).contents input.heap).trans (by
      simp only [nestedArrayType, SVal.dflt_fixed, SVal.dflt_array, SVal.strip_fixed,
        SVal.strip_array, SVec.strip_cons, SVec.strip_nil, SVec.replicate, expectedChildren, emptyChild])

theorem nested_actual_spans :
    let grown := input.heap.allocDefault (nestedArrayType element [2,3]) (nested_mapFree element [2,3])
    ∃ (base : Nat → Fin W) (target : Machine),
      run (budgetedDefaultCode ⟨55,by decide⟩ (chosen [2,3])) input.machine =
        .ok (target.push (.val (wmod 40))) 0 ∧
      Objects.AllocatorRepr grown.heap base 8 (wmod 54) target ∧
      ∀ {R : RefTy} (reference : HRef grown.H' R) (offset : Nat),
        offset < Objects.cells grown.heap reference →
        32 * ((base reference.id).val + offset) + 32 ≤ W := by
  obtain ⟨base,target,ran,allocated,_,_,_,_,_⟩ :=
    budgeted_default_success ⟨55,by decide⟩ (chosen [2,3]) input.heap input.base 8 (wmod 40)
      input.machine input.allocator (by decide)
  refine ⟨base,target,ran,allocated,?_⟩
  exact physical_default_live_spans _ _ _ _ _ allocated (by decide)

theorem last_complete_cell_fits :
    W / 32 - 1 + 1 < physicalDefaultBudget.val ∧ 32 * (W / 32 - 1) + 32 = W := by
  change W / 32 - 1 + 1 < W / 32 + 1 ∧ 32 * (W / 32 - 1) + 32 = W
  decide +kernel

theorem next_cell_refused : ¬ W / 32 + 1 < physicalDefaultBudget.val := by
  change ¬ W / 32 + 1 < W / 32 + 1
  omega

/--
info: 'Solidity.Backend.MemoryCopies.BudgetedDefaultControls.certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedDefaultControls.full_budget_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms full_budget_code
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedDefaultControls.empty_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_success
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedDefaultControls.nested_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nested_success
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedDefaultControls.nested_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nested_refusal
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedDefaultControls.zero_budget_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms zero_budget_refusal
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedDefaultControls.wrong_cursor_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_cursor_rejected
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedDefaultControls.nested_actual_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nested_actual_contents
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedDefaultControls.nested_actual_spans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nested_actual_spans
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedDefaultControls.last_complete_cell_fits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms last_complete_cell_fits
/--
info: 'Solidity.Backend.MemoryCopies.BudgetedDefaultControls.next_cell_refused' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms next_cell_refused
end Solidity.Backend.MemoryCopies.BudgetedDefaultControls
