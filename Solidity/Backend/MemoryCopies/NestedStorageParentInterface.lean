import Solidity.Backend.MemoryCopies.NestedStorageLoop
import Solidity.Backend.MemoryCopies.CheckedReference
import Solidity.Backend.MemoryCopies.HeapContents
import Solidity.Evm.MemoryDefaultParent
import Solidity.Evm.MemoryObjectNested

/-! Checked reservation, actual child traversal and typed parent adoption for
explicit count/source-base operands. Loading the outer storage header and
Source/physical adequacy are separate obligations. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def nestedStorageParentValue (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive))
    (bounded : rows.length < W) : SVal (.ref (.array (.ref (.array (.prim primitive))))) :=
  .array (nestedStorageValues primitive rows) .nil bounded

def nestedStorageParentExit : List Instr := [.pop, .pop, .swap 1, .pop]

def nestedStorageParentCode : List Instr := referenceCapacityGuard 0 ++
  (Objects.nestedPrefix ++ (nestedStorageLoopCode ++ nestedStorageParentExit))

def nestedStorageParentDemand {primitive : PrimTy} (rows : List (PrimitiveStorageRow primitive)) : Nat :=
  rows.length + 1 + nestedStorageDemand rows

def NestedStorageParentResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (size : Fin W) (fits : cursor.val + nestedStorageParentDemand rows < W) : Prop :=
  let value := nestedStorageParentValue primitive rows bounded
  let grown := value.copyStToM heap rfl
  ∃ base' target,
    run nestedStorageParentCode ((machine.push (.slot source)).push (.val size)) =
      .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + nestedStorageParentDemand rows, fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ H.length ≤ grown.val.id ∧
    grown.heap.len grown.val .dyn = rows.length ∧ MVal.copyMToSt grown.heap grown.val = value.strip

structure NestedStorageParentCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (size : Fin W) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine → rows.length = size.val →
    NestedStorageRowsRepr primitive rows machine source 0 L →
    (∃ fits, NestedStorageParentResult heap primitive rows bounded base frame cursor machine source size fits) ∨
    (¬ cursor.val + nestedStorageParentDemand rows < W ∧
      run nestedStorageParentCode ((machine.push (.slot source)).push (.val size)) = .revert)

end Solidity.Backend.MemoryCopies
