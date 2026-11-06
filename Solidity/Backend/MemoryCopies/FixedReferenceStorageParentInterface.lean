import Solidity.Backend.MemoryCopies.FixedReferenceStorageLoop
import Solidity.Backend.MemoryCopies.NestedStorageParent
import Solidity.Backend.MemoryCopies.TraversalWords
import Solidity.Evm.MemoryDefaultFixedBuilder

/-! Signature-only contract for checked fixed parents with dynamic primitive
children. This module supplies no inhabitant. FixedReferenceStorageParent and
its Controls companion prove/check the reservation, traversal and typed-adoption
composition. Source inputs are actual ReprAt values; physical/gas and general
compiler coverage remain separate. Static counts are natural numbers. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedReferenceStorageValue (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive)) :
    SVal (.ref (.fixed (.ref (.array (.prim primitive))) rows.length)) :=
  .fixed (nestedStorageValues primitive rows)

def fixedReferenceStorageParentDemand {primitive : PrimTy} (rows : List (PrimitiveStorageRow primitive)) : Nat :=
  max 1 rows.length + nestedStorageDemand rows

def fixedReferenceStorageParentCode (count : Nat) : List Instr :=
  defaultCapacityGuard (max 1 count) ++
    (Objects.fixedDefaultPrefix count ++ (fixedReferenceStorageLoopCode ++ nestedStorageParentExit))

def FixedReferenceStorageParentResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (source : Slot)
    (fits : cursor.val + fixedReferenceStorageParentDemand rows < W) : Prop :=
  let value := fixedReferenceStorageValue primitive rows
  let grown := value.copyStToM heap rfl
  ∃ base' target,
    run (fixedReferenceStorageParentCode rows.length) (machine.push (.slot source)) =
      .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + fixedReferenceStorageParentDemand rows,fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ H.length ≤ grown.val.id ∧
    grown.heap.len grown.val .fixed = rows.length ∧
    MVal.copyMToSt grown.heap grown.val = value.strip ∧
    heapWords grown.heap = heapWords heap + fixedReferenceStorageParentDemand rows

structure FixedReferenceStorageParentCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store L (.ref (.fixed (.ref (.array (.prim primitive))) rows.length)) source
      (fixedReferenceStorageValue primitive rows) →
    (∃ fits, FixedReferenceStorageParentResult heap primitive rows base frame cursor machine source fits) ∨
    (¬ cursor.val + fixedReferenceStorageParentDemand rows < W ∧
      run (fixedReferenceStorageParentCode rows.length) (machine.push (.slot source)) = .revert)
  demand : ∀ (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive)),
    liveWordCount (fixedReferenceStorageValue primitive rows) = fixedReferenceStorageParentDemand rows
  growth : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive)),
    heapWords ((fixedReferenceStorageValue primitive rows).copyStToM heap rfl).heap =
      heapWords heap + fixedReferenceStorageParentDemand rows

end Solidity.Backend.MemoryCopies
