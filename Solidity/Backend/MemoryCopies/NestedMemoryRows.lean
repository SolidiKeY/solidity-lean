import Solidity.Backend.MemoryCopies.NestedMemoryLoopInterface

/-! Heap-derived child rows and their transport through actual child-copy
extensions. No row relation is supplied to the public full-source certificate. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem memory_rows_length {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) :
    (memoryChildRows heap primitive source).length = heap.len source .dyn := by
  simp only [memoryChildRows, List.length_map, Heap.len]

theorem memory_rows_repr {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) :
    NestedMemoryRowsRepr heap primitive source (memoryChildRows heap primitive source) 0 := by
  intro offset row chosen
  simp only [memoryChildRows, List.getElem?_map] at chosen
  obtain ⟨child, picked, rfl⟩ := Option.map_eq_some_iff.mp chosen
  have lower : offset < heap.len source .dyn := lt_of_getElem? picked
  have bound : offset < W := Nat.lt_trans lower (heap.len_dyn_lt source)
  refine ⟨child, ?_, rfl, ?_⟩
  · simpa only [Heap.index, indexValue, Int.toNat_natCast, wmod_def, Nat.zero_add, Nat.mod_eq_of_lt bound] using picked
  · rw [primitiveArray_snapshot]
    rfl

theorem memory_rows_kept {H H' : HTy} (extension : H <+: H') (before : Heap H) (after : Heap H')
    (primitive : PrimTy) (source : HRef H (.array (.ref (.array (.prim primitive)))))
    (rows : List (PrimitiveStorageRow primitive)) (index : Nat)
    (kept : Heap.Keeps extension before after) (represented : NestedMemoryRowsRepr before primitive source rows index) :
    NestedMemoryRowsRepr after primitive (source.wk extension) rows index := by
  intro offset row chosen
  obtain ⟨child, selected, length, snapshot⟩ := represented offset row chosen
  refine ⟨child.wk extension, ?_, (kept.len child .dyn).trans length, ?_⟩
  · rw [kept_index extension before after kept source .dyn _, selected]
    rfl
  · exact (kept_snapshot extension before after kept (.ref (.array (.prim primitive))) child).trans snapshot

theorem memory_row_turn_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (row : PrimitiveStorageRow primitive) (source : HRef H (.array (.ref (.array (.prim primitive)))))
    (child : HRef H (.array (.prim primitive))) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + 1 + total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + 1 + total.val ≤ cursor.val)
    (inBounds : index.val < total.val)
    (selected : heap.index source .dyn (indexValue index) = some child)
    (length : heap.len child .dyn = row.val.length)
    (snapshot : MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) child = primitiveArrayValue primitive row.val row.property)
    (fits : cursor.val + (row.val.length + 1) < W) :
    let grown := (primitiveArrayValue primitive row.val row.property).copyStToM heap rfl
    ∃ base' target,
      run (nestedMemoryTurnCode primitive) (nestedMemoryControl machine (base source.id) parent total index) =
        .ok (nestedMemoryControl target (base source.id) parent total (wmod (index.val + 1))) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (row.val.length + 1), fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      Objects.Gap grown.heap base' parent.val (parent.val + 1 + total.val) ∧
      target.mem (parent.val + 1 + index.val) = .val cursor ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → address ≠ parent.val + 1 + index.val →
        target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext heap grown.heap := by
  have realFits : cursor.val + (heap.len child .dyn + 1) < W := by rw [length]; exact fits
  have turn : NestedMemoryTurnResult heap primitive source child base frame cursor machine parent total index realFits :=
    nested_memory_turn_success heap primitive source child base frame cursor machine parent total index
      allocator gap afterFrame beforeCursor inBounds selected realFits
  unfold NestedMemoryTurnResult at turn
  obtain ⟨base', target, ran, allocated, root, extension, childGap, pointer, shape, below, gaps, kept, _, _⟩ := turn
  have cursorEq : (⟨cursor.val + (heap.len child .dyn + 1), realFits⟩ : Fin W) =
      ⟨cursor.val + (row.val.length + 1), fits⟩ := Fin.ext (congrArg (fun n : Nat => cursor.val + (n + 1)) length)
  rw [cursorEq] at allocated
  have grownEq : (MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) child).copyStToM heap rfl =
      (primitiveArrayValue primitive row.val row.property).copyStToM heap rfl :=
    congrArg (fun value : SVal (.ref (.array (.prim primitive))) => value.copyStToM heap rfl) snapshot
  let Result (grown : Grown H (MVal · (.ref (.array (.prim primitive))))) : Prop :=
    ∃ base' target,
      run (nestedMemoryTurnCode primitive) (nestedMemoryControl machine (base source.id) parent total index) =
        .ok (nestedMemoryControl target (base source.id) parent total (wmod (index.val + 1))) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (row.val.length + 1), fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      Objects.Gap grown.heap base' parent.val (parent.val + 1 + total.val) ∧
      target.mem (parent.val + 1 + index.val) = .val cursor ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → address ≠ parent.val + 1 + index.val →
        target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext heap grown.heap
  have result : Result ((MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) child).copyStToM heap rfl) :=
    ⟨base', target, ran, allocated, root, extension, childGap, pointer, shape, below, gaps, kept⟩
  exact (congrArg Result grownEq).mp result

theorem memory_row_turn_refusal {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (row : PrimitiveStorageRow primitive) (source : HRef H (.array (.ref (.array (.prim primitive)))))
    (child : HRef H (.array (.prim primitive))) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (selected : heap.index source .dyn (indexValue index) = some child)
    (length : heap.len child .dyn = row.val.length) (tooLarge : ¬ cursor.val + (row.val.length + 1) < W) :
    run (nestedMemoryTurnCode primitive) (nestedMemoryControl machine (base source.id) parent total index) = .revert := by
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
  have realTooLarge : ¬ cursor.val + (heap.len child .dyn + 1) < W := by rw [length]; exact tooLarge
  have refusal : run checkedMemoryArrayCode (controlled.push (.val (base child.id))) = .revert := by
    rw [checked_memory_array_run heap primitive child base frame cursor controlled inputAllocator, if_neg realTooLarge]
  rw [nestedMemoryTurnCode, run_append_ok selectedRun, run_append_revert refusal]

theorem memory_rows_demand_bound {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    nestedStorageDemand (memoryChildRows heap primitive source) ≤ cursor.val * heap.len source .dyn := by
  have bound : ∀ children : List (HRef H (.array (.prim primitive))),
      nestedStorageDemand (children.map (fun child : HRef H (.array (.prim primitive)) =>
        (⟨MObj.elems .dyn (heap.get child), heap.len_dyn_lt child⟩ : PrimitiveStorageRow primitive))) ≤
        cursor.val * children.length := by
    intro children
    induction children with
    | nil => exact Nat.le_refl 0
    | cons child children ih =>
      have live : (base child.id).val + (1 + heap.len child .dyn) ≤ cursor.val := allocator.live child
      change heap.len child .dyn + 1 + nestedStorageDemand (children.map _) ≤ cursor.val * (children.length + 1)
      rw [Nat.mul_add, Nat.mul_one]
      omega
  exact bound _

#print axioms memory_rows_demand_bound
#print axioms memory_rows_length
#print axioms memory_rows_repr
#print axioms memory_rows_kept
#print axioms memory_row_turn_success
#print axioms memory_row_turn_refusal
end Solidity.Backend.MemoryCopies
