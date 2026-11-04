import Solidity.Backend.MemoryCopies.NestedDefaults

/-! Checked production defaults retain their exact intrinsic demand. Capacity
refusal is a word-machine outcome, separate from Source panic and gas. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def defaultCapacityGuard (cost : Nat) : List Instr :=
  if cost < W then [.push (.val (wmod (W - cost))),.mload 0,.lt] ++ assertTop else [.revert]

structure SelectedCheckedDefault (root : RefTy) (memory : (Ty.ref root).mapFree = true) where
  builder : Objects.DefaultBuilder root memory (ReferenceDefaults.defaultCells (.ref root))
  selected : ReferenceDefaults.compileDefault root memory = some builder

def SelectedCheckedDefault.code {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) : List Instr :=
  defaultCapacityGuard (ReferenceDefaults.defaultCells (.ref root)) ++ selected.builder.code

structure CheckedDefaultCertificate : Prop where
  execute : ∀ {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr heap base frame cursor machine →
    (∃ fits, Objects.DefaultBuildResult heap root memory selected.code
      (ReferenceDefaults.defaultCells (.ref root)) base frame cursor machine fits) ∨
    (¬ cursor.val + ReferenceDefaults.defaultCells (.ref root) < W ∧ run selected.code machine = .revert)
end Solidity.Backend.MemoryCopies
