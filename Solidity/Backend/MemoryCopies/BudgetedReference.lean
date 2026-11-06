import Solidity.Backend.MemoryCopies.BudgetedReferenceInterface

/-! Division checks runtime natural demand before the unchanged reference-array
constructor; strict configurable limits include empty unused-child behavior. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem reference_budget_remaining (limit : Fin (W + 1)) (cursor : Fin W) (room : cursor.val + 1 < limit.val) :
    (limit.val - 2 + (W - cursor.val)) % W = limit.val - 2 - cursor.val := by
  have large : 2 ≤ limit.val := by omega
  have equation : limit.val - 2 + (W - cursor.val) = W + (limit.val - 2 - cursor.val) := by omega
  have limitBound : limit.val ≤ W := Nat.le_of_lt_succ limit.isLt
  have bounded : limit.val - 2 - cursor.val < W := by omega
  simp only [equation,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_eq_of_lt bounded]

theorem reference_budget_iff (limit : Fin (W + 1)) (childCost : Nat) (cursor size : Fin W) (room : cursor.val + 1 < limit.val) :
    size.val ≤ (limit.val - 2 - cursor.val) / (childCost + 1) ↔
      cursor.val + (size.val + 1 + size.val * childCost) < limit.val := by
  rw [Nat.le_div_iff_mul_le (by omega : 0 < childCost + 1)]
  simp only [Nat.mul_add,Nat.mul_one]
  have large : 2 ≤ limit.val := by omega
  omega

theorem reference_budget_large (limit : Fin (W + 1)) (childCost : Nat) (cursor size : Fin W) (room : cursor.val + 1 < limit.val)
    (large : limit.val ≤ childCost + 1) :
    cursor.val + (size.val + 1 + size.val * childCost) < limit.val ↔ size.val = 0 := by
  constructor
  · intro fits
    by_cases zero : size.val = 0
    · exact zero
    have one : 1 ≤ size.val := by omega
    have product : 1 * (childCost + 1) ≤ size.val * (childCost + 1) := Nat.mul_le_mul_right _ one
    simp only [Nat.one_mul,Nat.mul_add,Nat.mul_one] at product
    omega
  · intro zero
    rw [zero,Nat.zero_add,Nat.zero_mul,Nat.add_zero]
    exact room

theorem reference_budget_tail_run (limit : Fin (W + 1)) (childCost : Nat) (machine : Machine) (cursor size : Fin W)
    (cell : machine.mem 0 = .val cursor) (room : cursor.val + 1 < limit.val) :
    run (referenceBudgetTail limit childCost) (machine.push (.val size)) =
      if cursor.val + (size.val + 1 + size.val * childCost) < limit.val
      then .ok (machine.push (.val size)) 0 else .revert := by
  by_cases bounded : childCost + 1 < limit.val
  · have limitBound : limit.val ≤ W := Nat.le_of_lt_succ limit.isLt
    have boundedWord : childCost + 1 < W := Nat.lt_of_lt_of_le bounded limitBound
    have largest : limit.val - 2 < W := by
      have large : 2 ≤ limit.val := by omega
      omega
    have remainder : (limit.val - 2 + (W - cursor.val)) % W = limit.val - 2 - cursor.val := reference_budget_remaining limit cursor room
    have nonzero : childCost + 1 ≠ 0 := by omega
    by_cases fits : cursor.val + (size.val + 1 + size.val * childCost) < limit.val
    · have comparison : ¬ (limit.val - 2 - cursor.val) / (childCost + 1) < size.val := by
        have limit : size.val ≤ (limit.val - 2 - cursor.val) / (childCost + 1) := (reference_budget_iff limit childCost cursor size room).mpr fits
        omega
      simp only [referenceBudgetTail,if_pos bounded,assertTop,List.cons_append,List.nil_append,run,exec_cons_zero,
        Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,Nat.reduceSub,List.getElem?_cons_zero,
        List.set_cons_zero,cell,wmod_def,Nat.mod_eq_of_lt largest,Nat.mod_eq_of_lt boundedWord,remainder,
        nonzero,comparison,decide_false,decide_true,bword,
        Bool.false_eq_true,↓reduceIte,Nat.succ_ne_self,exec_cons_succ,if_pos fits]
    · have comparison : (limit.val - 2 - cursor.val) / (childCost + 1) < size.val := by
        have limit : ¬ size.val ≤ (limit.val - 2 - cursor.val) / (childCost + 1) :=
          fun accepted => fits ((reference_budget_iff limit childCost cursor size room).mp accepted)
        omega
      simp only [referenceBudgetTail,if_pos bounded,assertTop,List.cons_append,List.nil_append,run,exec_cons_zero,
        Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,Nat.reduceSub,List.getElem?_cons_zero,
        List.set_cons_zero,cell,wmod_def,Nat.mod_eq_of_lt largest,Nat.mod_eq_of_lt boundedWord,remainder,
        nonzero,comparison,decide_false,decide_true,bword,
        Bool.false_eq_true,↓reduceIte,Nat.succ_ne_self,if_neg fits,Out.revert_bind]
  · have equivalence : cursor.val + (size.val + 1 + size.val * childCost) < limit.val ↔ size.val = 0 :=
      reference_budget_large limit childCost cursor size room (by omega)
    by_cases zero : size.val = 0
    · have fits : cursor.val + (size.val + 1 + size.val * childCost) < limit.val := equivalence.mpr zero
      rw [if_pos fits]
      simp only [referenceBudgetTail,if_neg bounded,assertTop,List.cons_append,List.nil_append,run,exec_cons_zero,
        Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,Nat.reduceSub,List.getElem?_cons_zero,
        zero,decide_true,bword,↓reduceIte,Nat.succ_ne_self,exec_cons_succ]
    · have fits : ¬ cursor.val + (size.val + 1 + size.val * childCost) < limit.val := fun accepted => zero (equivalence.mp accepted)
      simp only [referenceBudgetTail,if_neg bounded,assertTop,List.cons_append,List.nil_append,run,exec_cons_zero,
        Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,Nat.reduceSub,List.getElem?_cons_zero,
        zero,decide_false,bword,Bool.false_eq_true,↓reduceIte,if_neg fits,Out.revert_bind]

theorem reference_budget_guard_run (limit : Fin (W + 1)) (childCost : Nat) (machine : Machine) (cursor size : Fin W)
    (cell : machine.mem 0 = .val cursor) :
    run (referenceBudgetGuard limit childCost) (machine.push (.val size)) =
      if cursor.val + (size.val + 1 + size.val * childCost) < limit.val
      then .ok (machine.push (.val size)) 0 else .revert := by
  have first : run (budgetDefaultGuard limit 1) (machine.push (.val size)) =
      if cursor.val + 1 < limit.val then .ok (machine.push (.val size)) 0 else .revert :=
    budget_default_guard_run limit 1 (by decide) (machine.push (.val size)) cursor cell
  rw [referenceBudgetGuard]
  by_cases room : cursor.val + 1 < limit.val
  · rw [if_pos room] at first
    rw [run_append_ok first]
    exact reference_budget_tail_run limit childCost machine cursor size cell room
  · rw [if_neg room] at first
    rw [run_append_revert first,if_neg (by omega)]

theorem budgeted_reference_run {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H) (size : Fin W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    run (budgetedReferenceCode limit selected) (machine.push (.val size)) =
      if cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < limit.val
      then run (Objects.referenceArrayCode selected.builder.code) (machine.push (.val size)) else .revert := by
  have guard : run (referenceBudgetGuard limit (ReferenceDefaults.defaultCells (.ref root))) (machine.push (.val size)) =
      if cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < limit.val
      then .ok (machine.push (.val size)) 0 else .revert :=
    reference_budget_guard_run limit _ machine cursor size allocator.free.cell
  rw [budgetedReferenceCode]
  by_cases fits : cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < limit.val
  · rw [if_pos fits] at guard
    rw [run_append_ok guard,if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard,if_neg fits]

theorem budgeted_reference_success {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory) {H : HTy}
    (heap : Heap H) (size : Fin W) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + referenceDefaultWords root size < limit.val) :
    BudgetedReferenceResult limit selected heap size base frame cursor machine fits := by
  have actualFits : cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < limit.val := by
    rw [← reference_default_words selected size]
    exact fits
  have wordFits : cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < W :=
    Nat.lt_of_lt_of_le actualFits (Nat.le_of_lt_succ limit.isLt)
  obtain ⟨base',target,ran,allocated,rootAt,extension,shape,below,gaps⟩ :=
    Objects.referenceArray_correct selected.builder heap size base frame machine cursor allocator wordFits
  unfold BudgetedReferenceResult
  simp only [reference_default_words selected size]
  refine ⟨base',target,?_,allocated,rootAt,extension,shape,below,gaps⟩
  rw [budgeted_reference_run limit selected heap size base frame cursor machine allocator,if_pos actualFits]
  exact ran

theorem budgeted_reference_correct {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory) {H : HTy}
    (heap : Heap H) (size : Fin W) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    (∃ fits, BudgetedReferenceResult limit selected heap size base frame cursor machine fits) ∨
    (¬ cursor.val + referenceDefaultWords root size < limit.val ∧
      run (budgetedReferenceCode limit selected) (machine.push (.val size)) = .revert) := by
  by_cases fits : cursor.val + referenceDefaultWords root size < limit.val
  · exact .inl ⟨fits,budgeted_reference_success limit selected heap size base frame cursor machine allocator fits⟩
  · refine .inr ⟨fits,?_⟩
    rw [reference_default_words selected size] at fits
    rw [budgeted_reference_run limit selected heap size base frame cursor machine allocator,if_neg fits]

def budgetedReference : BudgetedReferenceCertificate :=
  ⟨reference_budget_guard_run,budgeted_reference_correct⟩

/--
info: 'Solidity.Backend.MemoryCopies.reference_budget_remaining' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms reference_budget_remaining
/--
info: 'Solidity.Backend.MemoryCopies.reference_budget_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reference_budget_iff
/--
info: 'Solidity.Backend.MemoryCopies.reference_budget_large' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms reference_budget_large
/--
info: 'Solidity.Backend.MemoryCopies.reference_budget_tail_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reference_budget_tail_run
/--
info: 'Solidity.Backend.MemoryCopies.reference_budget_guard_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reference_budget_guard_run
/--
info: 'Solidity.Backend.MemoryCopies.budgeted_reference_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgeted_reference_run
/--
info: 'Solidity.Backend.MemoryCopies.budgeted_reference_success' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgeted_reference_success
/--
info: 'Solidity.Backend.MemoryCopies.budgeted_reference_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgeted_reference_correct
/--
info: 'Solidity.Backend.MemoryCopies.budgetedReference' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgetedReference
end Solidity.Backend.MemoryCopies
