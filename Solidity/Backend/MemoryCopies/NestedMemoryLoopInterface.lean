import Solidity.Backend.MemoryCopies.NestedMemoryTurn
import Solidity.Backend.MemoryCopies.NestedStorageLoopInterface
import Solidity.Backend.MemoryCopies.SnapshotTransport
import Solidity.Backend.MemoryCopies.TraversalFresh

/-! Actual primitive child traversal from a canonical control stack. The public
rows/count are computed from the typed source heap, not supplied as premises.
Outer header loading, target parent adoption and Source adequacy remain open. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def memoryChildRows {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) : List (PrimitiveStorageRow primitive) :=
  (MObj.elems (.dyn (E := .ref (.array (.prim primitive)))) (heap.get source)).map
    (fun child : HRef H (.array (.prim primitive)) => ⟨MObj.elems (.dyn (E := .prim primitive)) (heap.get child), heap.len_dyn_lt child⟩)

def memoryChildCount {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) : Fin W :=
  ⟨heap.len source .dyn, heap.len_dyn_lt source⟩

def nestedMemoryLoopCode (primitive : PrimTy) : List Instr := [.loop Objects.childrenCondition (nestedMemoryTurnCode primitive)]

def NestedMemoryRowsRepr {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive)))))
    (rows : List (PrimitiveStorageRow primitive)) (index : Nat) : Prop :=
  ∀ offset row, rows[offset]? = some row → ∃ child,
    heap.index source .dyn (indexValue (wmod (index + offset))) = some child ∧
    heap.len child .dyn = row.val.length ∧
    MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) child = primitiveArrayValue primitive row.val row.property

def NestedMemoryRowsLoopResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive))
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (parent total index : Fin W)
    (fits : cursor.val + nestedStorageDemand rows < W) : Prop :=
  let grown := (nestedStorageValues primitive rows).copyStToM heap rfl
  ∃ base' target,
    loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) (rows.length + 1)
      (nestedMemoryControl machine (base source.id) parent total index) =
      .inr (.ok (nestedMemoryControl target (base source.id) parent total total) 0) ∧
    run (nestedMemoryLoopCode primitive) (nestedMemoryControl machine (base source.id) parent total index) =
      .ok (nestedMemoryControl target (base source.id) parent total total) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + nestedStorageDemand rows, fits⟩ target ∧
    BaseExtends H base base' ∧ Objects.Gap grown.heap base' parent.val (parent.val + 1 + total.val) ∧
    (∀ offset reference, grown.val.1[offset]? = some reference →
      target.mem (parent.val + 1 + index.val + offset) = .val (base' reference.id)) ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val →
      (address < parent.val + 1 + index.val ∨ parent.val + 1 + total.val ≤ address) →
      target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ TraversalFreshCertificate heap (nestedStorageValues primitive rows) rfl ∧
    MVal.copyMToSt grown.heap (T := .ref (.array (.ref (.array (.prim primitive))))) (source.wk grown.ext) =
      MVal.copyMToSt heap (T := .ref (.array (.ref (.array (.prim primitive))))) source

structure NestedMemoryLoopCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (parent : Fin W),
    Objects.AllocatorRepr heap base frame cursor machine →
    Objects.Gap heap base parent.val (parent.val + 1 + heap.len source .dyn) →
    frame ≤ parent.val → parent.val + 1 + heap.len source .dyn ≤ cursor.val →
    let rows := memoryChildRows heap primitive source
    let count := memoryChildCount heap primitive source
    (∃ fits, NestedMemoryRowsLoopResult heap primitive rows source base frame cursor machine parent count (wmod 0) fits) ∨
    (¬ cursor.val + nestedStorageDemand rows < W ∧
      loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) (rows.length + 1)
        (nestedMemoryControl machine (base source.id) parent count (wmod 0)) = .inr .revert ∧
      run (nestedMemoryLoopCode primitive) (nestedMemoryControl machine (base source.id) parent count (wmod 0)) = .revert)
end Solidity.Backend.MemoryCopies
