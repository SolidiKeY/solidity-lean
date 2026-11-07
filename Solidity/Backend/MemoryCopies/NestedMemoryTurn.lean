import Solidity.Backend.MemoryCopies.NestedMemoryTurnInterface

/-! The existing checked array read derives the actual child pointer; checked
copying and the reserved-parent store preserve all prior represented objects. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem nested_memory_operands (machine : Machine) (source parent total index : Fin W) :
    run [.dup 4, .dup 2] (nestedMemoryControl machine source parent total index) =
      .ok (((nestedMemoryControl machine source parent total index).push (.val source)).push (.val index)) 0 := by
  simp only [nestedMemoryControl, Objects.control, run, Machine.push, exec_cons_zero,
    Instr.step, Machine.next, Out.ok_bind, List.getElem?_cons_succ, List.getElem?_cons_zero, exec_nil, Nat.reduceSub]

theorem nested_memory_select {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive)))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    RefOut base (TRes.ofOpt (heap.index source .dyn (indexValue index)))
      (run (nestedMemorySelectCode primitive) (nestedMemoryControl machine (base source.id) parent total index))
      (nestedMemoryControl machine (base source.id) parent total index) := by
  let controlled := nestedMemoryControl machine (base source.id) parent total index
  have represented : Objects.AllocatorRepr heap base frame cursor controlled := allocator.stack _
  rw [nestedMemorySelectCode, run_append_ok (nested_memory_operands machine (base source.id) parent total index)]
  exact ((represented.heap.arrays .dyn source).read index).reference

theorem nested_memory_turn_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (child : HRef H (.array (.prim primitive)))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + 1 + total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + 1 + total.val ≤ cursor.val)
    (inBounds : index.val < total.val)
    (selected : heap.index source .dyn (indexValue index) = some child)
    (fits : cursor.val + (heap.len child .dyn + 1) < W) :
    NestedMemoryTurnResult heap primitive source child base frame cursor machine parent total index fits := by
  let snapshot := MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) child
  let grown := snapshot.copyStToM heap rfl
  let controlled := nestedMemoryControl machine (base source.id) parent total index
  have selectedRun : run (nestedMemorySelectCode primitive) controlled = .ok (controlled.push (.val (base child.id))) 0 := by
    rcases nested_memory_select heap primitive source base frame cursor machine parent total index allocator with
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
  have childGap : Objects.Gap grown.heap base' parent.val (parent.val + 1 + total.val) :=
    gaps _ _ gap beforeCursor
  have addressBound : parent.val + 1 + index.val < W := by omega
  have parentPositive : 0 < parent.val := Nat.lt_of_lt_of_le allocator.free.reserved afterFrame
  have addressPositive : 0 < parent.val + 1 + index.val := by omega
  let target := Objects.defaultStoreMachine childMachine parent index cursor 1
  have targetEq : target = writeMachine childMachine (parent.val + 1 + index.val) (.val cursor) :=
    Objects.defaultStoreMachine_eq _ _ _ _ _ addressBound
  have targetAllocator : Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + (heap.len child .dyn + 1), fits⟩ target := by
    rw [targetEq]
    exact childAllocator.writeGap childGap (by omega) (by omega) addressPositive (by
      change parent.val + 1 + total.val ≤ cursor.val + (heap.len child .dyn + 1)
      omega) _
  have stored : target.mem (parent.val + 1 + index.val) = .val cursor := by
    rw [targetEq]
    exact upd_same _ _ _
  have oldCells : ∀ address, 0 < address → address < cursor.val → address ≠ parent.val + 1 + index.val →
      target.mem address = machine.mem address := by
    intro address positive lower different
    rw [targetEq]
    exact (upd_other _ _ different).trans (below address positive lower)
  have targetShape : target = {machine with mem := target.mem} := by
    rw [targetEq]
    rfl
  have bodyRun : run (nestedMemoryTurnCode primitive) controlled =
      .ok (nestedMemoryControl target (base source.id) parent total (wmod (index.val + 1))) 0 := by
    rw [nestedMemoryTurnCode, run_append_ok selectedRun,
      run_append_ok ran, controlShape]
    exact Objects.defaultStoreStep_run (childMachine.push (.val (base source.id))) parent total index cursor 1
  exact ⟨base', target, bodyRun, targetAllocator, root, extension, childGap, stored,
    targetShape, oldCells, gaps, keeps, fresh, (storageHeapContents snapshot rfl).contents heap⟩

theorem nested_memory_turn_correct {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive)))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + 1 + total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + 1 + total.val ≤ cursor.val)
    (inBounds : index.val < total.val) :
    (∃ child, heap.index source .dyn (indexValue index) = some child ∧ ∃ fits,
      NestedMemoryTurnResult heap primitive source child base frame cursor machine parent total index fits) ∨
    (NestedMemoryTurnFailure heap primitive source index cursor ∧
      run (nestedMemoryTurnCode primitive) (nestedMemoryControl machine (base source.id) parent total index) = .revert) := by
  let controlled := nestedMemoryControl machine (base source.id) parent total index
  rcases nested_memory_select heap primitive source base frame cursor machine parent total index allocator with
    ⟨child, selected, selectedRun⟩ | ⟨missing, failed⟩
  · have found : heap.index source .dyn (indexValue index) = some child := by
      cases h : heap.index source .dyn (indexValue index) with
      | none => rw [h] at selected; cases selected
      | some value => rw [h] at selected; cases Except.ok.inj selected; rfl
    by_cases fits : cursor.val + (heap.len child .dyn + 1) < W
    · exact .inl ⟨child, found, fits, nested_memory_turn_success heap primitive source child base frame cursor machine
        parent total index allocator gap afterFrame beforeCursor inBounds found fits⟩
    · have inputAllocator : Objects.AllocatorRepr heap base frame cursor controlled := allocator.stack _
      have refusal : run checkedMemoryArrayCode (controlled.push (.val (base child.id))) = .revert := by
        rw [checked_memory_array_run heap primitive child base frame cursor controlled inputAllocator, if_neg fits]
      refine .inr ⟨Or.inr ⟨child, found, fits⟩, ?_⟩
      rw [nestedMemoryTurnCode, run_append_ok selectedRun, run_append_revert refusal]
  · have absent : heap.index source .dyn (indexValue index) = none := by
      cases h : heap.index source .dyn (indexValue index) with
      | none => rfl
      | some value => rw [h] at missing; cases missing
    exact .inr ⟨Or.inl absent, run_append_revert failed⟩

def nestedMemoryTurn : NestedMemoryTurnCertificate := ⟨nested_memory_turn_correct⟩

#print axioms nested_memory_operands
#print axioms nested_memory_select
#print axioms nested_memory_turn_success
#print axioms nested_memory_turn_correct
#print axioms nestedMemoryTurn
end Solidity.Backend.MemoryCopies
