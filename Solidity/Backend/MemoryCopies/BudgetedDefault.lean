import Solidity.Backend.MemoryCopies.BudgetedDefaultInterface

/-! Existing guards implement arbitrary target word budgets through a bias;
actual builders retain their unmodified cost and full allocator contract. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem budget_default_guard_run (limit : Fin (W + 1)) (cost : Nat) (positive : 0 < cost)
    (machine : Machine) (cursor : Fin W) (cell : machine.mem 0 = .val cursor) :
    run (budgetDefaultGuard limit cost) machine =
      if cursor.val + cost < limit.val then .ok machine 0 else .revert := by
  have bounded : limit.val ≤ W := Nat.le_of_lt_succ limit.isLt
  have biasedPositive : 0 < W - limit.val + cost := by omega
  rw [budgetDefaultGuard, default_capacity_guard_run _ biasedPositive machine cursor cell]
  by_cases fits : cursor.val + cost < limit.val
  · have wordFits : cursor.val + (W - limit.val + cost) < W := by omega
    rw [if_pos wordFits, if_pos fits]
  · have wordRefusal : ¬ cursor.val + (W - limit.val + cost) < W := by omega
    rw [if_neg wordRefusal, if_neg fits]

theorem budgeted_default_run {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory)
    {H : HTy} (heap : Heap H) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    run (budgetedDefaultCode limit selected) machine =
      if cursor.val + ReferenceDefaults.defaultCells (.ref root) < limit.val
      then run selected.builder.code machine else .revert := by
  have guard : run (budgetDefaultGuard limit (ReferenceDefaults.defaultCells (.ref root))) machine =
      if cursor.val + ReferenceDefaults.defaultCells (.ref root) < limit.val then .ok machine 0 else .revert :=
    budget_default_guard_run limit _ selected.builder.positive machine cursor allocator.free.cell
  rw [budgetedDefaultCode]
  by_cases fits : cursor.val + ReferenceDefaults.defaultCells (.ref root) < limit.val
  · rw [if_pos fits] at guard
    rw [run_append_ok guard, if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard, if_neg fits]

theorem budgeted_default_success {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory)
    {H : HTy} (heap : Heap H) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + ReferenceDefaults.defaultCells (.ref root) < limit.val) :
    BudgetedDefaultSuccess limit selected heap base frame cursor machine fits := by
  have wordFits : cursor.val + ReferenceDefaults.defaultCells (.ref root) < W :=
    Nat.lt_of_lt_of_le fits (Nat.le_of_lt_succ limit.isLt)
  obtain ⟨base',target,ran,allocated,rootAt,extension,shape,below,gaps⟩ :=
    selected.builder.correct heap base frame cursor machine allocator wordFits
  refine ⟨base',target,?_,allocated,rootAt,extension,shape,below,gaps⟩
  rw [budgeted_default_run limit selected heap base frame cursor machine allocator, if_pos fits]
  exact ran

theorem budgeted_default_correct {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory)
    {H : HTy} (heap : Heap H) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    (∃ fits, BudgetedDefaultSuccess limit selected heap base frame cursor machine fits) ∨
    (¬ cursor.val + ReferenceDefaults.defaultCells (.ref root) < limit.val ∧
      run (budgetedDefaultCode limit selected) machine = .revert) := by
  by_cases fits : cursor.val + ReferenceDefaults.defaultCells (.ref root) < limit.val
  · exact .inl ⟨fits,budgeted_default_success limit selected heap base frame cursor machine allocator fits⟩
  · refine .inr ⟨fits,?_⟩
    rw [budgeted_default_run limit selected heap base frame cursor machine allocator, if_neg fits]

theorem physical_default_live_spans {H : HTy} (heap : Heap H) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (bounded : cursor.val < physicalDefaultBudget.val) {R : RefTy}
    (reference : HRef H R) (offset : Nat) (inside : offset < Objects.cells heap reference) :
    32 * ((base reference.id).val + offset) + 32 ≤ W := by
  have live : (base reference.id).val + Objects.cells heap reference ≤ cursor.val := allocator.live reference
  change cursor.val < W / 32 + 1 at bounded
  omega

def budgetedDefault : BudgetedDefaultCertificate :=
  ⟨budget_default_guard_run,budgeted_default_correct,physical_default_live_spans⟩

/--
info: 'Solidity.Backend.MemoryCopies.budget_default_guard_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budget_default_guard_run
/--
info: 'Solidity.Backend.MemoryCopies.budgeted_default_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgeted_default_run
/--
info: 'Solidity.Backend.MemoryCopies.budgeted_default_success' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgeted_default_success
/--
info: 'Solidity.Backend.MemoryCopies.budgeted_default_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgeted_default_correct
/--
info: 'Solidity.Backend.MemoryCopies.physical_default_live_spans' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms physical_default_live_spans
/--
info: 'Solidity.Backend.MemoryCopies.budgetedDefault' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgetedDefault
end Solidity.Backend.MemoryCopies
