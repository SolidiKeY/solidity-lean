import Solidity.Backend.MemoryCopies.BudgetedDefault
import Solidity.Backend.MemoryCopies.ReferenceDefaultDemand

/-! Configurable runtime reference-array budgets extend the existing guard and
constructor. Division checks full natural demand before target allocation;
Source panic, compiler coverage, gas and physical execution remain separate. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def referenceBudgetTail (limit : Fin (W + 1)) (childCost : Nat) : List Instr :=
  if childCost + 1 < limit.val then
    [.dup 1,.mload 0,.push (.val (wmod (limit.val - 2))),.sub,.push (.val (wmod (childCost + 1))),
      .swap 1,.div,.lt,.iszero] ++ assertTop
  else [.dup 1,.iszero] ++ assertTop

def referenceBudgetGuard (limit : Fin (W + 1)) (childCost : Nat) : List Instr :=
  budgetDefaultGuard limit 1 ++ referenceBudgetTail limit childCost

def budgetedReferenceCode {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory) : List Instr :=
  referenceBudgetGuard limit (ReferenceDefaults.defaultCells (.ref root)) ++
    Objects.referenceArrayCode selected.builder.code

def BudgetedReferenceResult {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory) {H : HTy}
    (heap : Heap H) (size : Fin W) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (fits : cursor.val + referenceDefaultWords root size < limit.val) : Prop :=
  let grown := Objects.referenceArrayCopy heap root memory size
  ∃ base' target, run (budgetedReferenceCode limit selected) (machine.push (.val size)) =
      .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + referenceDefaultWords root size,
        Nat.lt_of_lt_of_le fits (Nat.le_of_lt_succ limit.isLt)⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi)

structure BudgetedReferenceCertificate : Prop where
  guard : ∀ (limit : Fin (W + 1)) (childCost : Nat) (machine : Machine) (cursor size : Fin W),
    machine.mem 0 = .val cursor →
    run (referenceBudgetGuard limit childCost) (machine.push (.val size)) =
      if cursor.val + (size.val + 1 + size.val * childCost) < limit.val
      then .ok (machine.push (.val size)) 0 else .revert
  execute : ∀ {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (limit : Fin (W + 1)) (selected : SelectedCheckedDefault root memory) {H : HTy}
    (heap : Heap H) (size : Fin W) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr heap base frame cursor machine →
    (∃ fits, BudgetedReferenceResult limit selected heap size base frame cursor machine fits) ∨
    (¬ cursor.val + referenceDefaultWords root size < limit.val ∧
      run (budgetedReferenceCode limit selected) (machine.push (.val size)) = .revert)

end Solidity.Backend.MemoryCopies
