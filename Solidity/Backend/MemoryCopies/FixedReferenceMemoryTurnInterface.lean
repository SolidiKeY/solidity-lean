import Solidity.Backend.MemoryCopies.NestedMemoryTurn

/-! Contract for checked access and deep copying of one dynamic primitive child
from a headerless fixed memory parent into a separate parent reservation.
Source access refusal and allocation refusal remain distinct; traversal/adoption
and Source/physical adequacy are separate obligations. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedReferenceMemorySelectCode (primitive : PrimTy) (count : Nat) : List Instr := [.dup 4, .dup 2] ++ Objects.readCode (.fixed (n := count) (E := .ref (.array (.prim primitive))))

def fixedReferenceMemoryTurnCode (primitive : PrimTy) (count : Nat) : List Instr :=
  fixedReferenceMemorySelectCode primitive count ++ (checkedMemoryArrayCode ++ Objects.defaultStoreStep 0)

def FixedReferenceMemoryTurnResult {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) count))
    (child : HRef H (.array (.prim primitive)))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (parent total index : Fin W) (fits : cursor.val + (heap.len child .dyn + 1) < W) : Prop :=
  let snapshot := MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) child
  let grown := snapshot.copyStToM heap rfl
  ∃ base' target,
    run (fixedReferenceMemoryTurnCode primitive count) (nestedMemoryControl machine (base source.id) parent total index) =
      .ok (nestedMemoryControl target (base source.id) parent total (wmod (index.val + 1))) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (heap.len child .dyn + 1), fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
    Objects.Gap grown.heap base' parent.val (parent.val + max 1 total.val) ∧
    target.mem (parent.val + index.val) = .val cursor ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ parent.val + index.val →
      target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ child.id < grown.val.id ∧
    MVal.copyMToSt grown.heap grown.val = snapshot.strip

def FixedReferenceMemoryTurnFailure {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) count)) (index cursor : Fin W) : Prop :=
  heap.index source .fixed (indexValue index) = none ∨
  ∃ child, heap.index source .fixed (indexValue index) = some child ∧ ¬ cursor.val + (heap.len child .dyn + 1) < W

structure FixedReferenceMemoryTurnCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) count))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (parent total index : Fin W),
    Objects.AllocatorRepr heap base frame cursor machine →
    Objects.Gap heap base parent.val (parent.val + max 1 total.val) →
    frame ≤ parent.val → parent.val + max 1 total.val ≤ cursor.val → index.val < total.val →
    (∃ child, heap.index source .fixed (indexValue index) = some child ∧ ∃ fits,
      FixedReferenceMemoryTurnResult heap primitive count source child base frame cursor machine parent total index fits) ∨
    (FixedReferenceMemoryTurnFailure heap primitive count source index cursor ∧
      run (fixedReferenceMemoryTurnCode primitive count) (nestedMemoryControl machine (base source.id) parent total index) = .revert)
end Solidity.Backend.MemoryCopies
