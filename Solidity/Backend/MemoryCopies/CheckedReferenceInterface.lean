import Solidity.Backend.MemoryCopies.CheckedDefault

/-! Runtime reference-array defaults check complete demand before allocating.
Oversized unused child demand does not exclude the empty-parent execution. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def referenceCapacityTail (childCost : Nat) : List Instr :=
  if childCost + 1 < W then
    [.dup 1,.mload 0,.push (.val (wmod (W - 2))),.sub,.push (.val (wmod (childCost + 1))),
      .swap 1,.div,.lt,.iszero] ++ assertTop
  else [.dup 1,.iszero] ++ assertTop

def referenceCapacityGuard (childCost : Nat) : List Instr :=
  defaultCapacityGuard 1 ++ referenceCapacityTail childCost

def checkedReferenceCode {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) : List Instr :=
  referenceCapacityGuard (ReferenceDefaults.defaultCells (.ref root)) ++ Objects.referenceArrayCode selected.builder.code

def CheckedReferenceResult {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H) (size : Fin W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (fits : cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < W) : Prop :=
  let grown := Objects.referenceArrayCopy heap root memory size
  ∃ base' target, run (checkedReferenceCode selected) (machine.push (.val size)) = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)),fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi)

structure CheckedReferenceCertificate : Prop where
  execute : ∀ {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H) (size : Fin W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr heap base frame cursor machine →
    (∃ fits, CheckedReferenceResult selected heap size base frame cursor machine fits) ∨
    (¬ cursor.val + (size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)) < W ∧
      run (checkedReferenceCode selected) (machine.push (.val size)) = .revert)
end Solidity.Backend.MemoryCopies
