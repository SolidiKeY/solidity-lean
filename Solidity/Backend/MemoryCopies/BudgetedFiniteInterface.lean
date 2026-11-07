import Solidity.Backend.MemoryCopies.BudgetedDefault
import Solidity.Backend.MemoryCopies.CheckedFiniteDefault

/-! Configurable guards for existing finite struct plans, including nonzero
parent offsets and actual declaration StateRepr/allocator growth. This adds no
planner branch, Source admission, panic or physical execution theorem. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def budgetedFiniteCode {R : RefTy} (limit : Fin (W + 1))
    (plan : DefaultPlan R) (suffix : List Instr) : List Instr :=
  budgetDefaultGuard limit plan.cost ++ (plan.code ++ suffix)

/-- Retain the complete existing finite-plan contract and identify the actual
budgeted run with its checked execution. The caller supplies no capacity. -/
def BudgetedFiniteSuccess {C : Contract} {Γ : Ctx} {R : RefTy}
    (limit : Fin (W + 1)) (plan : DefaultPlan R) {L b frame : Nat} {F : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (memory : (Ty.ref R).mapFree = true) (fits : cursor.val + plan.cost < limit.val) : Prop :=
  FiniteDefaultSuccess (L := L) (b := b) (frame := frame) (F := F)
    plan state base cursor machine memory (Nat.lt_of_lt_of_le fits (Nat.le_of_lt_succ limit.isLt)) ∧
  run (budgetedFiniteCode limit plan []) machine = run (checkedFiniteDefaultCode plan []) machine

structure BudgetedFiniteCertificate : Prop where
  execute : ∀ {C : Contract} {Γ : Ctx} {R : RefTy}
    (limit : Fin (W + 1)) (plan : DefaultPlan R) {L b frame : Nat} {F : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (memory : (Ty.ref R).mapFree = true),
    StateRepr L b frame F state base machine →
    StructAllocatorRepr state.heap base frame cursor machine → 0 < b →
    (∃ fits, BudgetedFiniteSuccess (L := L) (b := b) (frame := frame) (F := F)
      limit plan state base cursor machine memory fits) ∨
    (¬ cursor.val + plan.cost < limit.val ∧ run (budgetedFiniteCode limit plan []) machine = .revert)
  declaration : ∀ {C : Contract} {Γ : Ctx} {R : RefTy}
    (limit : Fin (W + 1)) (plan : DefaultPlan R) {L b frame : Nat} {F : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (memory : (Ty.ref R).mapFree = true),
    StateRepr L b frame F state base machine →
    StructAllocatorRepr state.heap base frame cursor machine → 0 < b →
    b + (Γ.length + 1) ≤ frame →
    GrowingResult L b frame plan.cost (F.push (.mem R) .ok) state base machine
      (TRun.declMem R none memory state)
      (run (budgetedFiniteCode limit plan [.mstore (cell (b + Γ.length))]) machine) ∨
    (¬ cursor.val + plan.cost < limit.val ∧
      run (budgetedFiniteCode limit plan [.mstore (cell (b + Γ.length))]) machine = .revert)

end Solidity.Backend.MemoryCopies
