import Solidity.Backend.MemoryCopies.SelectedDefaultDemand

/-! Configurable target word budgets reuse the existing capacity guard and
selected builder. The physical budget admits the last complete 32-byte cell;
address-fit is not bytecode execution, gas or Source panic correspondence. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def budgetDefaultGuard (limit : Fin (W + 1)) (cost : Nat) : List Instr :=
  defaultCapacityGuard (W - limit.val + cost)

def budgetedDefaultCode {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory) : List Instr :=
  budgetDefaultGuard limit (ReferenceDefaults.defaultCells (.ref root)) ++ selected.builder.code

def physicalDefaultBudget : Fin (W + 1) := ⟨W / 32 + 1, by
  have positive : 0 < W := W_pos
  omega⟩

def BudgetedDefaultSuccess {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory)
    {H : HTy} (heap : Heap H) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (fits : cursor.val + ReferenceDefaults.defaultCells (.ref root) < limit.val) : Prop :=
  Objects.DefaultBuildResult heap root memory (budgetedDefaultCode limit selected)
    (ReferenceDefaults.defaultCells (.ref root)) base frame cursor machine
    (Nat.lt_of_lt_of_le fits (Nat.le_of_lt_succ limit.isLt))

structure BudgetedDefaultCertificate : Prop where
  guard : ∀ (limit : Fin (W + 1)) (cost : Nat) (positive : 0 < cost)
    (machine : Machine) (cursor : Fin W), machine.mem 0 = .val cursor →
    run (budgetDefaultGuard limit cost) machine =
      if cursor.val + cost < limit.val then .ok machine 0 else .revert
  execute : ∀ {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory)
    {H : HTy} (heap : Heap H) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr heap base frame cursor machine →
    (∃ fits, BudgetedDefaultSuccess limit selected heap base frame cursor machine fits) ∨
    (¬ cursor.val + ReferenceDefaults.defaultCells (.ref root) < limit.val ∧
      run (budgetedDefaultCode limit selected) machine = .revert)
  live_spans : ∀ {H : HTy} (heap : Heap H) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr heap base frame cursor machine → cursor.val < physicalDefaultBudget.val →
    ∀ {R : RefTy} (reference : HRef H R) (offset : Nat), offset < Objects.cells heap reference →
      32 * ((base reference.id).val + offset) + 32 ≤ W

end Solidity.Backend.MemoryCopies
