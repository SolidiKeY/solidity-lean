import Solidity.Backend.MemoryCopies.NestedStorageTurnInterface

/-! Actual child payload copying composes with the existing parent pointer
store. The ownership gap remains reserved, without adopting a typed parent. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem nested_child_slot_run (machine : Machine) (source : Slot) (parent total index : Fin W) :
    run nestedChildSlotCode (nestedStorageControl machine source parent total index) =
      .ok ((nestedStorageControl machine source parent total index).push (.slot (source.add index.val))) 0 := by
  simp only [nestedChildSlotCode, nestedStorageControl, Objects.control, run,
    Machine.push, exec_cons_zero, Instr.step, Machine.next, Out.ok_bind,
    List.getElem?_cons_succ, List.getElem?_cons_zero, exec_nil, Nat.reduceSub]

theorem nested_storage_turn_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (parent total index : Fin W) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + 1 + total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + 1 + total.val ≤ cursor.val)
    (inBounds : index.val < total.val)
    (represented : ReprAt machine.store L (.ref (.array (.prim primitive))) (source.add index.val)
      (primitiveArrayValue primitive values bounded))
    (fits : cursor.val + (values.length + 1) < W) :
    NestedStorageTurnResult heap primitive values bounded base frame cursor machine source parent total index fits := by
  let grown := (primitiveArrayValue primitive values bounded).copyStToM heap rfl
  let controlled := nestedStorageControl machine source parent total index
  have inputAllocator : Objects.AllocatorRepr heap base frame cursor controlled := allocator.stack _
  obtain ⟨base', copied, ran, allocated, root, extension, shape, below, gaps⟩ :=
    checked_storage_array_success heap primitive values bounded base frame cursor controlled
      (source.add index.val) L inputAllocator represented fits
  let childMachine : Machine := {machine with mem := copied.mem}
  have controlShape : copied = nestedStorageControl childMachine source parent total index := shape
  have childAllocator : Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + (values.length + 1), fits⟩ childMachine := allocated.mem_eq rfl
  have childGap : Objects.Gap grown.heap base' parent.val (parent.val + 1 + total.val) :=
    gaps _ _ gap beforeCursor
  have addressBound : parent.val + 1 + index.val < W := by omega
  have parentPositive : 0 < parent.val := Nat.lt_of_lt_of_le allocator.free.reserved afterFrame
  have addressPositive : 0 < parent.val + 1 + index.val := by omega
  let target := Objects.defaultStoreMachine childMachine parent index cursor 1
  have targetEq : target = writeMachine childMachine (parent.val + 1 + index.val) (.val cursor) :=
    Objects.defaultStoreMachine_eq _ _ _ _ _ addressBound
  have targetAllocator : Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + (values.length + 1), fits⟩ target := by
    rw [targetEq]
    exact childAllocator.writeGap childGap (by omega) (by omega) addressPositive (by
      change parent.val + 1 + total.val ≤ cursor.val + (values.length + 1)
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
  have bodyRun : run nestedStorageTurnCode controlled =
      .ok (nestedStorageControl target source parent total (wmod (index.val + 1))) 0 := by
    rw [nestedStorageTurnCode, run_append_ok (nested_child_slot_run machine source parent total index),
      run_append_ok ran, controlShape]
    exact Objects.defaultStoreStep_run (childMachine.push (.slot source)) parent total index cursor 1
  have identity : grown.val.id = H.length := by
    dsimp only [grown]
    rw [primitive_array_source]
    rfl
  have length : grown.heap.len grown.val .dyn = values.length := by
    dsimp only [grown]
    rw [primitive_array_source]
    simp only [Grown.alloc, Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk, primitiveArrayObject, List.length_map]
  exact ⟨base', target, bodyRun, targetAllocator, root, extension, childGap, stored,
    targetShape, oldCells, gaps, SVal.keeps_copyStToM _ rfl heap, identity, length⟩

theorem nested_storage_turn_correct {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (parent total index : Fin W) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + 1 + total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + 1 + total.val ≤ cursor.val)
    (inBounds : index.val < total.val)
    (represented : ReprAt machine.store L (.ref (.array (.prim primitive))) (source.add index.val)
      (primitiveArrayValue primitive values bounded)) :
    (∃ fits, NestedStorageTurnResult heap primitive values bounded base frame cursor machine source parent total index fits) ∨
    (¬ cursor.val + (values.length + 1) < W ∧
      run nestedStorageTurnCode (nestedStorageControl machine source parent total index) = .revert) := by
  by_cases fits : cursor.val + (values.length + 1) < W
  · exact .inl ⟨fits, nested_storage_turn_success heap primitive values bounded base frame cursor machine
      source parent total index L allocator gap afterFrame beforeCursor inBounds represented fits⟩
  · refine .inr ⟨fits, ?_⟩
    have inputAllocator : Objects.AllocatorRepr heap base frame cursor
        (nestedStorageControl machine source parent total index) := allocator.stack _
    have refusal : run checkedStorageArrayCode
        ((nestedStorageControl machine source parent total index).push (.slot (source.add index.val))) = .revert := by
      rw [checked_storage_array_run heap primitive values bounded base frame cursor _ _ L inputAllocator represented,
        if_neg fits]
    rw [nestedStorageTurnCode, run_append_ok (nested_child_slot_run machine source parent total index),
      run_append_revert refusal]

def nestedStorageTurn : NestedStorageTurnCertificate := ⟨nested_storage_turn_correct⟩

#print axioms nested_child_slot_run
#print axioms nested_storage_turn_success
#print axioms nested_storage_turn_correct
#print axioms nestedStorageTurn
end Solidity.Backend.MemoryCopies
