import Solidity.Backend.MemoryCopies.FixedReferenceStorageTurn
import Solidity.Backend.MemoryCopies.NestedStorageLoop

/-! Headerless fixed-parent traversal through actual checked storage children.
The existing typed row vector/copy fold and runtime demand are reused. Parent
reservation/adoption, source selection and physical/gas adequacy stay separate. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedReferenceStorageLoopCode : List Instr :=
  [.loop Objects.childrenCondition fixedReferenceStorageTurnCode]

def FixedReferenceStorageLoopResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (parent total index : Fin W)
    (fits : cursor.val + nestedStorageDemand rows < W) : Prop :=
  let grown := (nestedStorageValues primitive rows).copyStToM heap rfl
  ∃ base' target,
    loopIterN (run Objects.childrenCondition) (run fixedReferenceStorageTurnCode) (rows.length + 1)
      (nestedStorageControl machine source parent total index) =
      .inr (.ok (nestedStorageControl target source parent total total) 0) ∧
    run fixedReferenceStorageLoopCode (nestedStorageControl machine source parent total index) =
      .ok (nestedStorageControl target source parent total total) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + nestedStorageDemand rows, fits⟩ target ∧
    BaseExtends H base base' ∧ Objects.Gap grown.heap base' parent.val (parent.val + max 1 total.val) ∧
    (∀ offset reference, grown.val.1[offset]? = some reference →
      target.mem (parent.val + index.val + offset) = .val (base' reference.id)) ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val →
      (address < parent.val + index.val ∨ parent.val + total.val ≤ address) →
      target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap

structure FixedReferenceStorageLoopCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (parent total index : Fin W) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    Objects.Gap heap base parent.val (parent.val + max 1 total.val) →
    frame ≤ parent.val → parent.val + max 1 total.val ≤ cursor.val →
    index.val + rows.length = total.val → NestedStorageRowsRepr primitive rows machine source index.val L →
    (∃ fits, FixedReferenceStorageLoopResult heap primitive rows base frame cursor machine source parent total index fits) ∨
    (¬ cursor.val + nestedStorageDemand rows < W ∧
      loopIterN (run Objects.childrenCondition) (run fixedReferenceStorageTurnCode) (rows.length + 1)
        (nestedStorageControl machine source parent total index) = .inr .revert ∧
      run fixedReferenceStorageLoopCode (nestedStorageControl machine source parent total index) = .revert)

end Solidity.Backend.MemoryCopies
