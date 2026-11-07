import Solidity.Backend.MemoryCopies.BudgetedFiniteInterface

/-! Guard existing finite-plan code with a configurable bound. The original
complete plan result and declaration simulation are preserved unchanged. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem budgeted_finite_run {R : RefTy} (limit : Fin (W + 1)) (plan : DefaultPlan R)
    (suffix : List Instr) (machine : Machine) (cursor : Fin W) (cell : machine.mem 0 = .val cursor) :
    run (budgetedFiniteCode limit plan suffix) machine =
      if cursor.val + plan.cost < limit.val then run (plan.code ++ suffix) machine else .revert := by
  have guard : run (budgetDefaultGuard limit plan.cost) machine =
      if cursor.val + plan.cost < limit.val then .ok machine 0 else .revert :=
    budget_default_guard_run limit plan.cost (finite_default_positive plan) machine cursor cell
  rw [budgetedFiniteCode]
  by_cases fits : cursor.val + plan.cost < limit.val
  · rw [if_pos fits] at guard
    rw [run_append_ok guard,if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard,if_neg fits]

theorem budgeted_finite_success {C : Contract} {Γ : Ctx} {R : RefTy}
    (limit : Fin (W + 1)) (plan : DefaultPlan R) {L b frame : Nat} {F : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (memory : (Ty.ref R).mapFree = true) (represented : StateRepr L b frame F state base machine)
    (allocator : StructAllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (fits : cursor.val + plan.cost < limit.val) :
    BudgetedFiniteSuccess (L := L) (b := b) (frame := frame) (F := F)
      limit plan state base cursor machine memory fits := by
  have wordFits : cursor.val + plan.cost < W := Nat.lt_of_lt_of_le fits (Nat.le_of_lt_succ limit.isLt)
  refine ⟨checked_finite_success plan state base cursor machine memory represented allocator positive wordFits,?_⟩
  rw [budgeted_finite_run limit plan [] machine cursor allocator.arrays.free.cell,if_pos fits,
    checked_finite_run plan [] machine cursor allocator.arrays.free.cell,if_pos wordFits]

theorem budgeted_finite_correct {C : Contract} {Γ : Ctx} {R : RefTy}
    (limit : Fin (W + 1)) (plan : DefaultPlan R) {L b frame : Nat} {F : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (memory : (Ty.ref R).mapFree = true) (represented : StateRepr L b frame F state base machine)
    (allocator : StructAllocatorRepr state.heap base frame cursor machine) (positive : 0 < b) :
    (∃ fits, BudgetedFiniteSuccess (L := L) (b := b) (frame := frame) (F := F)
      limit plan state base cursor machine memory fits) ∨
    (¬ cursor.val + plan.cost < limit.val ∧ run (budgetedFiniteCode limit plan []) machine = .revert) := by
  by_cases fits : cursor.val + plan.cost < limit.val
  · exact .inl ⟨fits,budgeted_finite_success limit plan state base cursor machine memory represented allocator positive fits⟩
  · refine .inr ⟨fits,?_⟩
    rw [budgeted_finite_run limit plan [] machine cursor allocator.arrays.free.cell,if_neg fits]

theorem budgeted_finite_declaration {C : Contract} {Γ : Ctx} {R : RefTy}
    (limit : Fin (W + 1)) (plan : DefaultPlan R) {L b frame : Nat} {F : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (memory : (Ty.ref R).mapFree = true) (represented : StateRepr L b frame F state base machine)
    (allocator : StructAllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (locals : b + (Γ.length + 1) ≤ frame) :
    GrowingResult L b frame plan.cost (F.push (.mem R) .ok) state base machine
      (TRun.declMem R none memory state)
      (run (budgetedFiniteCode limit plan [.mstore (cell (b + Γ.length))]) machine) ∨
    (¬ cursor.val + plan.cost < limit.val ∧
      run (budgetedFiniteCode limit plan [.mstore (cell (b + Γ.length))]) machine = .revert) := by
  by_cases fits : cursor.val + plan.cost < limit.val
  · have wordFits : cursor.val + plan.cost < W := Nat.lt_of_lt_of_le fits (Nat.le_of_lt_succ limit.isLt)
    apply Or.inl
    rw [budgeted_finite_run limit plan _ machine cursor allocator.arrays.free.cell,if_pos fits]
    exact plan.declare_correct represented positive memory locals (.inr ⟨positive,cursor,allocator,wordFits⟩)
  · refine .inr ⟨fits,?_⟩
    rw [budgeted_finite_run limit plan _ machine cursor allocator.arrays.free.cell,if_neg fits]

def budgetedFinite : BudgetedFiniteCertificate := ⟨budgeted_finite_correct,budgeted_finite_declaration⟩

/--
info: 'Solidity.Backend.MemoryCopies.budgeted_finite_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgeted_finite_run
/--
info: 'Solidity.Backend.MemoryCopies.budgeted_finite_success' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgeted_finite_success
/--
info: 'Solidity.Backend.MemoryCopies.budgeted_finite_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgeted_finite_correct
/--
info: 'Solidity.Backend.MemoryCopies.budgeted_finite_declaration' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgeted_finite_declaration
/--
info: 'Solidity.Backend.MemoryCopies.budgetedFinite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms budgetedFinite
end Solidity.Backend.MemoryCopies
