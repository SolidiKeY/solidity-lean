import Solidity.Backend.MemoryCopies.CheckedMemoryArray
import Solidity.Backend.MemoryCopies.HeapContents
import Solidity.Evm.MemoryDefaultChildren
import Solidity.Evm.MemoryObjectAccess

/-! One actual checked nested-memory child access, deep copy and reserved-parent
pointer store. Source bounds and allocation refusal are separate; whole graph
traversal, typed parent adoption and Source/physical adequacy remain open. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def nestedMemoryControl (machine : Machine) (source parent total index : Fin W) : Machine :=
  Objects.control (machine.push (.val source)) parent total index

def nestedMemorySelectCode (primitive : PrimTy) : List Instr := [.dup 4, .dup 2] ++ Objects.readCode (.dyn (E := .ref (.array (.prim primitive))))

def nestedMemoryTurnCode (primitive : PrimTy) : List Instr :=
  nestedMemorySelectCode primitive ++ (checkedMemoryArrayCode ++ Objects.defaultStoreStep 1)

def NestedMemoryTurnResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive)))))
    (child : HRef H (.array (.prim primitive)))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (parent total index : Fin W) (fits : cursor.val + (heap.len child .dyn + 1) < W) : Prop :=
  let snapshot := MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) child
  let grown := snapshot.copyStToM heap rfl
  ∃ base' target,
    run (nestedMemoryTurnCode primitive) (nestedMemoryControl machine (base source.id) parent total index) =
      .ok (nestedMemoryControl target (base source.id) parent total (wmod (index.val + 1))) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (heap.len child .dyn + 1), fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
    Objects.Gap grown.heap base' parent.val (parent.val + 1 + total.val) ∧
    target.mem (parent.val + 1 + index.val) = .val cursor ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ parent.val + 1 + index.val →
      target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ child.id < grown.val.id ∧
    MVal.copyMToSt grown.heap grown.val = snapshot.strip

def NestedMemoryTurnFailure {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (index cursor : Fin W) : Prop :=
  heap.index source .dyn (indexValue index) = none ∨
  ∃ child, heap.index source .dyn (indexValue index) = some child ∧ ¬ cursor.val + (heap.len child .dyn + 1) < W

structure NestedMemoryTurnCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive)))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (parent total index : Fin W),
    Objects.AllocatorRepr heap base frame cursor machine →
    Objects.Gap heap base parent.val (parent.val + 1 + total.val) →
    frame ≤ parent.val → parent.val + 1 + total.val ≤ cursor.val → index.val < total.val →
    (∃ child, heap.index source .dyn (indexValue index) = some child ∧ ∃ fits,
      NestedMemoryTurnResult heap primitive source child base frame cursor machine parent total index fits) ∨
    (NestedMemoryTurnFailure heap primitive source index cursor ∧
      run (nestedMemoryTurnCode primitive) (nestedMemoryControl machine (base source.id) parent total index) = .revert)
end Solidity.Backend.MemoryCopies
