import Solidity.Backend.MemoryCopies.NestedStorageTurn

/-! Complete traversal of represented dynamic primitive children in an existing
parent reservation. Source rows use the existing intrinsic vector and copy;
parent adoption, outer-header selection and Source/physical adequacy stay open. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

abbrev PrimitiveStorageRow (primitive : PrimTy) := {values : List primitive.Denote // values.length < W}

def nestedStorageValues (primitive : PrimTy) :
    (rows : List (PrimitiveStorageRow primitive)) → SVec (.ref (.array (.prim primitive))) rows.length
  | [] => .nil
  | row :: rows => .cons (primitiveArrayValue primitive row.val row.property) (nestedStorageValues primitive rows)

def nestedStorageDemand {primitive : PrimTy} : List (PrimitiveStorageRow primitive) → Nat
  | [] => 0
  | row :: rows => row.val.length + 1 + nestedStorageDemand rows

def nestedStorageLoopCode : List Instr := [.loop Objects.childrenCondition nestedStorageTurnCode]

def NestedStorageRowsRepr (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive))
    (machine : Machine) (source : Slot) (index L : Nat) : Prop :=
  ∀ offset row, rows[offset]? = some row →
    ReprAt machine.store L (.ref (.array (.prim primitive))) (source.add (index + offset))
      (primitiveArrayValue primitive row.val row.property)

def NestedStorageLoopResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (parent total index : Fin W)
    (fits : cursor.val + nestedStorageDemand rows < W) : Prop :=
  let grown := (nestedStorageValues primitive rows).copyStToM heap rfl
  ∃ base' target,
    loopIterN (run Objects.childrenCondition) (run nestedStorageTurnCode) (rows.length + 1)
      (nestedStorageControl machine source parent total index) =
      .inr (.ok (nestedStorageControl target source parent total total) 0) ∧
    run nestedStorageLoopCode (nestedStorageControl machine source parent total index) =
      .ok (nestedStorageControl target source parent total total) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + nestedStorageDemand rows, fits⟩ target ∧
    BaseExtends H base base' ∧ Objects.Gap grown.heap base' parent.val (parent.val + 1 + total.val) ∧
    (∀ offset reference, grown.val.1[offset]? = some reference →
      target.mem (parent.val + 1 + index.val + offset) = .val (base' reference.id)) ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val →
      (address < parent.val + 1 + index.val ∨ parent.val + 1 + total.val ≤ address) →
      target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap

structure NestedStorageLoopCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (parent total index : Fin W) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    Objects.Gap heap base parent.val (parent.val + 1 + total.val) →
    frame ≤ parent.val → parent.val + 1 + total.val ≤ cursor.val →
    index.val + rows.length = total.val → NestedStorageRowsRepr primitive rows machine source index.val L →
    (∃ fits, NestedStorageLoopResult heap primitive rows base frame cursor machine source parent total index fits) ∨
    (¬ cursor.val + nestedStorageDemand rows < W ∧
      loopIterN (run Objects.childrenCondition) (run nestedStorageTurnCode) (rows.length + 1)
        (nestedStorageControl machine source parent total index) = .inr .revert ∧
      run nestedStorageLoopCode (nestedStorageControl machine source parent total index) = .revert)

end Solidity.Backend.MemoryCopies
