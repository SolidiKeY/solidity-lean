import Solidity.Backend.MemoryCopies.CheckedFiniteDefaultInterface

/-! Guard existing finite-plan code, retaining all previous success guarantees.
Capacity refusal is a word-machine result, not an asserted Source panic. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem finite_default_positive {R : RefTy} (plan : DefaultPlan R) : 0 < plan.cost := by
  have root : plan.root < plan.cost := plan.root_lt
  omega

theorem checked_finite_run {R : RefTy} (plan : DefaultPlan R) (suffix : List Instr)
    (machine : Machine) (cursor : Fin W) (cell : machine.mem 0 = .val cursor) :
    run (checkedFiniteDefaultCode plan suffix) machine =
      if cursor.val + plan.cost < W then run (plan.code ++ suffix) machine else .revert := by
  have guard : run (defaultCapacityGuard plan.cost) machine =
      if cursor.val + plan.cost < W then .ok machine 0 else .revert :=
    default_capacity_guard_run plan.cost (finite_default_positive plan) machine cursor cell
  rw [checkedFiniteDefaultCode]
  by_cases fits : cursor.val + plan.cost < W
  · rw [if_pos fits] at guard
    rw [run_append_ok guard, if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard, if_neg fits]

theorem checked_finite_success {C : Contract} {Γ : Ctx} {R : RefTy} (plan : DefaultPlan R)
    {L b frame : Nat} {F : Frag Γ} (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (memory : (Ty.ref R).mapFree = true)
    (represented : StateRepr L b frame F state base machine)
    (allocator : StructAllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (fits : cursor.val + plan.cost < W) :
    FiniteDefaultSuccess (L := L) (b := b) (frame := frame) (F := F)
      plan state base cursor machine memory fits := by
  obtain ⟨base', mem, stateRepr, heapRepr, extension, root, execution⟩ :=
    plan.sound state base cursor machine memory represented allocator positive fits
  refine ⟨base', mem, stateRepr, heapRepr, extension, root, ?_, default_plan_words plan state.heap memory⟩
  rw [checked_finite_run plan [] machine cursor allocator.arrays.free.cell, if_pos fits, List.append_nil]
  exact execution

theorem checked_finite_default {C : Contract} {Γ : Ctx} {R : RefTy} (plan : DefaultPlan R)
    {L b frame : Nat} {F : Frag Γ} (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (memory : (Ty.ref R).mapFree = true)
    (represented : StateRepr L b frame F state base machine)
    (allocator : StructAllocatorRepr state.heap base frame cursor machine) (positive : 0 < b) :
    (∃ fits, FiniteDefaultSuccess (L := L) (b := b) (frame := frame) (F := F)
      plan state base cursor machine memory fits) ∨
    (¬ cursor.val + plan.cost < W ∧ run (checkedFiniteDefaultCode plan []) machine = .revert) := by
  by_cases fits : cursor.val + plan.cost < W
  · exact .inl ⟨fits, checked_finite_success plan state base cursor machine memory represented allocator positive fits⟩
  · refine .inr ⟨fits, ?_⟩
    rw [checked_finite_run plan [] machine cursor allocator.arrays.free.cell, if_neg fits]

theorem checked_finite_declaration {C : Contract} {Γ : Ctx} {R : RefTy} (plan : DefaultPlan R)
    {L b frame : Nat} {F : Frag Γ} (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (memory : (Ty.ref R).mapFree = true)
    (represented : StateRepr L b frame F state base machine)
    (allocator : StructAllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (locals : b + (Γ.length + 1) ≤ frame) :
    GrowingResult L b frame plan.cost (F.push (.mem R) .ok) state base machine
      (TRun.declMem R none memory state)
      (run (checkedFiniteDefaultCode plan [.mstore (cell (b + Γ.length))]) machine) ∨
    (¬ cursor.val + plan.cost < W ∧
      run (checkedFiniteDefaultCode plan [.mstore (cell (b + Γ.length))]) machine = .revert) := by
  by_cases fits : cursor.val + plan.cost < W
  · apply Or.inl
    rw [checked_finite_run plan _ machine cursor allocator.arrays.free.cell, if_pos fits]
    exact plan.declare_correct represented positive memory locals (.inr ⟨positive, cursor, allocator, fits⟩)
  · refine .inr ⟨fits, ?_⟩
    rw [checked_finite_run plan _ machine cursor allocator.arrays.free.cell, if_neg fits]

def checkedFiniteDefault : CheckedFiniteDefaultCertificate :=
  ⟨checked_finite_default, checked_finite_declaration⟩

#print axioms finite_default_positive
#print axioms checked_finite_run
#print axioms checked_finite_success
#print axioms checked_finite_default
#print axioms checked_finite_declaration
#print axioms checkedFiniteDefault
end Solidity.Backend.MemoryCopies
