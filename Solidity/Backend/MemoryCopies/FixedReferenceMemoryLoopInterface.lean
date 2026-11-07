import Solidity.Backend.MemoryCopies.FixedReferenceMemoryTurn
import Solidity.Backend.MemoryCopies.NestedMemoryLoopInterface

/-! Contract for actual fixed-parent memory child traversal. Rows come from the
source heap, including repeated references. The parent reservation is headerless
and stays unadopted here; full adoption/path and Source adequacy remain open. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedMemoryChildRows {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) size)) : List (PrimitiveStorageRow primitive) :=
  (MObj.elems (.fixed (n := size) (E := .ref (.array (.prim primitive)))) (heap.get source)).map
    (fun child : HRef H (.array (.prim primitive)) => ⟨MObj.elems (.dyn (E := .prim primitive)) (heap.get child), heap.len_dyn_lt child⟩)

def fixedReferenceMemoryLoopCode (primitive : PrimTy) (size : Nat) : List Instr := [.loop Objects.childrenCondition (fixedReferenceMemoryTurnCode primitive size)]

def FixedReferenceMemoryRowsRepr {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) size))
    (rows : List (PrimitiveStorageRow primitive)) (index : Nat) : Prop :=
  ∀ offset row, rows[offset]? = some row → ∃ child,
    heap.index source .fixed (indexValue (wmod (index + offset))) = some child ∧
    heap.len child .dyn = row.val.length ∧
    MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) child = primitiveArrayValue primitive row.val row.property

def FixedReferenceMemoryRowsLoopResult {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (rows : List (PrimitiveStorageRow primitive))
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) size)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (parent total index : Fin W)
    (fits : cursor.val + nestedStorageDemand rows < W) : Prop :=
  let grown := (nestedStorageValues primitive rows).copyStToM heap rfl
  ∃ base' target,
    loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) (rows.length + 1)
      (nestedMemoryControl machine (base source.id) parent total index) =
      .inr (.ok (nestedMemoryControl target (base source.id) parent total total) 0) ∧
    run (fixedReferenceMemoryLoopCode primitive size) (nestedMemoryControl machine (base source.id) parent total index) =
      .ok (nestedMemoryControl target (base source.id) parent total total) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + nestedStorageDemand rows, fits⟩ target ∧
    BaseExtends H base base' ∧ Objects.Gap grown.heap base' parent.val (parent.val + max 1 total.val) ∧
    (∀ offset reference, grown.val.1[offset]? = some reference →
      target.mem (parent.val + index.val + offset) = .val (base' reference.id)) ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val →
      (address < parent.val + index.val ∨ parent.val + max 1 total.val ≤ address) →
      target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ TraversalFreshCertificate heap (nestedStorageValues primitive rows) rfl ∧
    MVal.copyMToSt grown.heap (T := .ref (.fixed (.ref (.array (.prim primitive))) size)) (source.wk grown.ext) =
      MVal.copyMToSt heap (T := .ref (.fixed (.ref (.array (.prim primitive))) size)) source

structure FixedReferenceMemoryLoopCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) size)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (parent : Fin W),
    Objects.AllocatorRepr heap base frame cursor machine →
    Objects.Gap heap base parent.val (parent.val + max 1 size) →
    frame ≤ parent.val → parent.val + max 1 size ≤ cursor.val →
    let rows := fixedMemoryChildRows heap primitive size source
    let count := wmod size
    (∃ fits, FixedReferenceMemoryRowsLoopResult heap primitive size rows source base frame cursor machine parent count (wmod 0) fits) ∨
    (¬ cursor.val + nestedStorageDemand rows < W ∧
      loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) (rows.length + 1)
        (nestedMemoryControl machine (base source.id) parent count (wmod 0)) = .inr .revert ∧
      run (fixedReferenceMemoryLoopCode primitive size) (nestedMemoryControl machine (base source.id) parent count (wmod 0)) = .revert)
end Solidity.Backend.MemoryCopies
