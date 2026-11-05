import Solidity.Backend.MemoryCopies.CheckedStorageArray
import Solidity.Evm.MemoryDefaultChildren

/-! One actual storage-child copy into a reserved parent. The child slot is
represented explicitly; outer traversal, physical slot hashing and typed parent
adoption are separate obligations. Capacity refusal is target-only. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def nestedChildSlotCode : List Instr := [.dup 4, .dup 2, .add]

def nestedStorageTurnCode : List Instr :=
  nestedChildSlotCode ++ (checkedStorageArrayCode ++ Objects.defaultStoreStep 1)

def nestedStorageControl (machine : Machine) (source : Slot) (parent total index : Fin W) : Machine :=
  Objects.control (machine.push (.slot source)) parent total index

def NestedStorageTurnResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (parent total index : Fin W)
    (fits : cursor.val + (values.length + 1) < W) : Prop :=
  let grown := (primitiveArrayValue primitive values bounded).copyStToM heap rfl
  ∃ base' target,
    run nestedStorageTurnCode (nestedStorageControl machine source parent total index) =
      .ok (nestedStorageControl target source parent total (wmod (index.val + 1))) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (values.length + 1), fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
    Objects.Gap grown.heap base' parent.val (parent.val + 1 + total.val) ∧
    target.mem (parent.val + 1 + index.val) = .val cursor ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ parent.val + 1 + index.val →
      target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ grown.val.id = H.length ∧
    grown.heap.len grown.val .dyn = values.length

structure NestedStorageTurnCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (parent total index : Fin W) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    Objects.Gap heap base parent.val (parent.val + 1 + total.val) →
    frame ≤ parent.val → parent.val + 1 + total.val ≤ cursor.val → index.val < total.val →
    ReprAt machine.store L (.ref (.array (.prim primitive))) (source.add index.val)
      (primitiveArrayValue primitive values bounded) →
    (∃ fits, NestedStorageTurnResult heap primitive values bounded base frame cursor machine source parent total index fits) ∨
    (¬ cursor.val + (values.length + 1) < W ∧
      run nestedStorageTurnCode (nestedStorageControl machine source parent total index) = .revert)

end Solidity.Backend.MemoryCopies
