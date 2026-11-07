import Solidity.Backend.MemoryCopies.FixedReferenceMemoryTurnInterface

/-! Derive a headerless fixed-parent child pointer from its represented memory,
then execute the existing checked deep child copy and header0 pointer store.
Old represented objects and reserved-parent gaps survive each successful step. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem fixed_reference_memory_select {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) count))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    RefOut base (TRes.ofOpt (heap.index source .fixed (indexValue index)))
      (run (fixedReferenceMemorySelectCode primitive count) (nestedMemoryControl machine (base source.id) parent total index))
      (nestedMemoryControl machine (base source.id) parent total index) := by
  let controlled := nestedMemoryControl machine (base source.id) parent total index
  have represented : Objects.AllocatorRepr heap base frame cursor controlled := allocator.stack _
  rw [fixedReferenceMemorySelectCode, run_append_ok (nested_memory_operands machine (base source.id) parent total index)]
  exact ((represented.heap.arrays .fixed source).read index).reference

theorem fixed_reference_memory_turn_success {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) count)) (child : HRef H (.array (.prim primitive)))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + max 1 total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + max 1 total.val ≤ cursor.val)
    (inBounds : index.val < total.val)
    (selected : heap.index source .fixed (indexValue index) = some child)
    (fits : cursor.val + (heap.len child .dyn + 1) < W) :
    FixedReferenceMemoryTurnResult heap primitive count source child base frame cursor machine parent total index fits := by
  let snapshot := MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) child
  let grown := snapshot.copyStToM heap rfl
  let controlled := nestedMemoryControl machine (base source.id) parent total index
  have selectedRun : run (fixedReferenceMemorySelectCode primitive count) controlled = .ok (controlled.push (.val (base child.id))) 0 := by
    rcases fixed_reference_memory_select heap primitive count source base frame cursor machine parent total index allocator with
      ⟨actual, found, ran⟩ | ⟨failed, _⟩
    · rw [selected] at found
      cases Except.ok.inj found
      exact ran
    · rw [selected] at failed
      cases failed
  have inputAllocator : Objects.AllocatorRepr heap base frame cursor controlled := allocator.stack _
  obtain ⟨base', copied, ran, allocated, root, extension, shape, below, gaps, keeps, fresh⟩ :=
    checked_memory_array_success heap primitive child base frame cursor controlled inputAllocator fits
  let childMachine : Machine := {machine with mem := copied.mem}
  have controlShape : copied = nestedMemoryControl childMachine (base source.id) parent total index := shape
  have childAllocator : Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + (heap.len child .dyn + 1), fits⟩ childMachine := allocated.mem_eq rfl
  have childGap : Objects.Gap grown.heap base' parent.val (parent.val + max 1 total.val) :=
    gaps _ _ gap beforeCursor
  have addressBound : parent.val + index.val < W := by omega
  have parentPositive : 0 < parent.val := Nat.lt_of_lt_of_le allocator.free.reserved afterFrame
  have addressPositive : 0 < parent.val + index.val := by omega
  let target := Objects.defaultStoreMachine childMachine parent index cursor 0
  have targetEq : target = writeMachine childMachine (parent.val + index.val) (.val cursor) :=
    Objects.defaultStoreMachine_eq _ _ _ _ _ addressBound
  have targetAllocator : Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + (heap.len child .dyn + 1), fits⟩ target := by
    rw [targetEq]
    exact childAllocator.writeGap childGap (by omega) (by omega) addressPositive (by
      change parent.val + max 1 total.val ≤ cursor.val + (heap.len child .dyn + 1)
      omega) _
  have stored : target.mem (parent.val + index.val) = .val cursor := by
    rw [targetEq]
    exact upd_same _ _ _
  have oldCells : ∀ address, 0 < address → address < cursor.val → address ≠ parent.val + index.val →
      target.mem address = machine.mem address := by
    intro address positive lower different
    rw [targetEq]
    exact (upd_other _ _ different).trans (below address positive lower)
  have targetShape : target = {machine with mem := target.mem} := by
    rw [targetEq]
    rfl
  have bodyRun : run (fixedReferenceMemoryTurnCode primitive count) controlled =
      .ok (nestedMemoryControl target (base source.id) parent total (wmod (index.val + 1))) 0 := by
    rw [fixedReferenceMemoryTurnCode, run_append_ok selectedRun,
      run_append_ok ran, controlShape]
    exact Objects.defaultStoreStep_run (childMachine.push (.val (base source.id))) parent total index cursor 0
  exact ⟨base', target, bodyRun, targetAllocator, root, extension, childGap, stored,
    targetShape, oldCells, gaps, keeps, fresh, (storageHeapContents snapshot rfl).contents heap⟩

theorem fixed_reference_memory_turn_correct {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) count))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + max 1 total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + max 1 total.val ≤ cursor.val)
    (inBounds : index.val < total.val) :
    (∃ child, heap.index source .fixed (indexValue index) = some child ∧ ∃ fits,
      FixedReferenceMemoryTurnResult heap primitive count source child base frame cursor machine parent total index fits) ∨
    (FixedReferenceMemoryTurnFailure heap primitive count source index cursor ∧
      run (fixedReferenceMemoryTurnCode primitive count) (nestedMemoryControl machine (base source.id) parent total index) = .revert) := by
  let controlled := nestedMemoryControl machine (base source.id) parent total index
  rcases fixed_reference_memory_select heap primitive count source base frame cursor machine parent total index allocator with
    ⟨child, selected, selectedRun⟩ | ⟨missing, failed⟩
  · have found : heap.index source .fixed (indexValue index) = some child := by
      cases h : heap.index source .fixed (indexValue index) with
      | none => rw [h] at selected; cases selected
      | some value => rw [h] at selected; cases Except.ok.inj selected; rfl
    by_cases fits : cursor.val + (heap.len child .dyn + 1) < W
    · exact .inl ⟨child, found, fits, fixed_reference_memory_turn_success heap primitive count source child base frame cursor machine
        parent total index allocator gap afterFrame beforeCursor inBounds found fits⟩
    · have inputAllocator : Objects.AllocatorRepr heap base frame cursor controlled := allocator.stack _
      have refusal : run checkedMemoryArrayCode (controlled.push (.val (base child.id))) = .revert := by
        rw [checked_memory_array_run heap primitive child base frame cursor controlled inputAllocator, if_neg fits]
      refine .inr ⟨Or.inr ⟨child, found, fits⟩, ?_⟩
      rw [fixedReferenceMemoryTurnCode, run_append_ok selectedRun, run_append_revert refusal]
  · have absent : heap.index source .fixed (indexValue index) = none := by
      cases h : heap.index source .fixed (indexValue index) with
      | none => rfl
      | some value => rw [h] at missing; cases missing
    exact .inr ⟨Or.inl absent, run_append_revert failed⟩

def fixedReferenceMemoryTurn : FixedReferenceMemoryTurnCertificate := ⟨fixed_reference_memory_turn_correct⟩


/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_memory_select' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_memory_select
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_memory_turn_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_memory_turn_success
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_memory_turn_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_memory_turn_correct
/--
info: 'Solidity.Backend.MemoryCopies.fixedReferenceMemoryTurn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixedReferenceMemoryTurn

end Solidity.Backend.MemoryCopies
