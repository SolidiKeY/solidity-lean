import Solidity.Backend.MemoryCopies.NestedStorageTurn
import Solidity.Evm.MemoryDefaultArraySource

/-! One checked dynamic-child copy into a headerless fixed-parent reservation.
Pointers are stored at parent+index, with no fictitious header cell or gap.
Full traversal/adoption, Source and physical adequacy remain separate. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedReferenceStorageTurnCode : List Instr :=
  nestedChildSlotCode ++ (checkedStorageArrayCode ++ Objects.defaultStoreStep 0)

def FixedReferenceStorageTurnResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (parent total index : Fin W)
    (fits : cursor.val + (values.length + 1) < W) : Prop :=
  let grown := (primitiveArrayValue primitive values bounded).copyStToM heap rfl
  ∃ base' target,
    run fixedReferenceStorageTurnCode (nestedStorageControl machine source parent total index) =
      .ok (nestedStorageControl target source parent total (wmod (index.val + 1))) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (values.length + 1), fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
    Objects.Gap grown.heap base' parent.val (parent.val + max 1 total.val) ∧
    target.mem (parent.val + index.val) = .val cursor ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ parent.val + index.val →
      target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ grown.val.id = H.length ∧
    grown.heap.len grown.val .dyn = values.length

structure FixedReferenceStorageTurnCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (parent total index : Fin W) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    Objects.Gap heap base parent.val (parent.val + max 1 total.val) →
    frame ≤ parent.val → parent.val + max 1 total.val ≤ cursor.val → index.val < total.val →
    ReprAt machine.store L (.ref (.array (.prim primitive))) (source.add index.val)
      (primitiveArrayValue primitive values bounded) →
    (∃ fits, FixedReferenceStorageTurnResult heap primitive values bounded base frame cursor machine source parent total index fits) ∨
    (¬ cursor.val + (values.length + 1) < W ∧
      run fixedReferenceStorageTurnCode (nestedStorageControl machine source parent total index) = .revert)

end Solidity.Backend.MemoryCopies
