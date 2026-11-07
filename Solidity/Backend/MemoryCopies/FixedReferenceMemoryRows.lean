import Solidity.Backend.MemoryCopies.FixedReferenceMemoryLoopInterface

/-! Actual fixed-source rows and snapshot-preserving transport through the
existing typed deep child-copy extensions. No public caller row oracle. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem fixed_memory_length {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) size)) : heap.len source .fixed = size := by
  change (MObj.elems .fixed (heap.get source)).length = size
  rw [MObj.elems_fixed]
  exact (heap.get source).property

theorem fixed_memory_rows_length {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) size)) :
    (fixedMemoryChildRows heap primitive size source).length = heap.len source .fixed := by
  simp only [fixedMemoryChildRows, List.length_map, Heap.len]

theorem fixed_memory_rows_repr {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) size)) (sizeBound : size < W) :
    FixedReferenceMemoryRowsRepr heap primitive size source (fixedMemoryChildRows heap primitive size source) 0 := by
  intro offset row chosen
  simp only [fixedMemoryChildRows, List.getElem?_map] at chosen
  obtain ⟨child, picked, rfl⟩ := Option.map_eq_some_iff.mp chosen
  have lower : offset < heap.len source .fixed := lt_of_getElem? picked
  have bound : offset < W := by
    rw [fixed_memory_length] at lower
    exact Nat.lt_trans lower sizeBound
  refine ⟨child, ?_, rfl, ?_⟩
  · simpa only [Heap.index, indexValue, Int.toNat_natCast, wmod_def, Nat.zero_add, Nat.mod_eq_of_lt bound] using picked
  · rw [primitiveArray_snapshot]
    rfl

theorem fixed_memory_rows_kept {H H' : HTy} (extension : H <+: H') (before : Heap H) (after : Heap H')
    (primitive : PrimTy) (size : Nat) (source : HRef H (.fixed (.ref (.array (.prim primitive))) size))
    (rows : List (PrimitiveStorageRow primitive)) (index : Nat)
    (kept : Heap.Keeps extension before after) (represented : FixedReferenceMemoryRowsRepr before primitive size source rows index) :
    FixedReferenceMemoryRowsRepr after primitive size (source.wk extension) rows index := by
  intro offset row chosen
  obtain ⟨child, selected, length, snapshot⟩ := represented offset row chosen
  refine ⟨child.wk extension, ?_, (kept.len child .dyn).trans length, ?_⟩
  · rw [kept_index extension before after kept source .fixed _, selected]
    rfl
  · exact (kept_snapshot extension before after kept (.ref (.array (.prim primitive))) child).trans snapshot

theorem fixed_memory_row_turn_success {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (row : PrimitiveStorageRow primitive) (source : HRef H (.fixed (.ref (.array (.prim primitive))) size))
    (child : HRef H (.array (.prim primitive))) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + max 1 total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + max 1 total.val ≤ cursor.val)
    (inBounds : index.val < total.val)
    (selected : heap.index source .fixed (indexValue index) = some child)
    (length : heap.len child .dyn = row.val.length)
    (snapshot : MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) child = primitiveArrayValue primitive row.val row.property)
    (fits : cursor.val + (row.val.length + 1) < W) :
    let grown := (primitiveArrayValue primitive row.val row.property).copyStToM heap rfl
    ∃ base' target,
      run (fixedReferenceMemoryTurnCode primitive size) (nestedMemoryControl machine (base source.id) parent total index) =
        .ok (nestedMemoryControl target (base source.id) parent total (wmod (index.val + 1))) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (row.val.length + 1), fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      Objects.Gap grown.heap base' parent.val (parent.val + max 1 total.val) ∧
      target.mem (parent.val + index.val) = .val cursor ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → address ≠ parent.val + index.val →
        target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext heap grown.heap := by
  have realFits : cursor.val + (heap.len child .dyn + 1) < W := by rw [length]; exact fits
  have turn : FixedReferenceMemoryTurnResult heap primitive size source child base frame cursor machine parent total index realFits :=
    fixed_reference_memory_turn_success heap primitive size source child base frame cursor machine parent total index
      allocator gap afterFrame beforeCursor inBounds selected realFits
  unfold FixedReferenceMemoryTurnResult at turn
  obtain ⟨base', target, ran, allocated, root, extension, childGap, pointer, shape, below, gaps, kept, _, _⟩ := turn
  have cursorEq : (⟨cursor.val + (heap.len child .dyn + 1), realFits⟩ : Fin W) =
      ⟨cursor.val + (row.val.length + 1), fits⟩ := Fin.ext (congrArg (fun n : Nat => cursor.val + (n + 1)) length)
  rw [cursorEq] at allocated
  have grownEq : (MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) child).copyStToM heap rfl =
      (primitiveArrayValue primitive row.val row.property).copyStToM heap rfl :=
    congrArg (fun value : SVal (.ref (.array (.prim primitive))) => value.copyStToM heap rfl) snapshot
  let Result (grown : Grown H (MVal · (.ref (.array (.prim primitive))))) : Prop :=
    ∃ base' target,
      run (fixedReferenceMemoryTurnCode primitive size) (nestedMemoryControl machine (base source.id) parent total index) =
        .ok (nestedMemoryControl target (base source.id) parent total (wmod (index.val + 1))) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (row.val.length + 1), fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      Objects.Gap grown.heap base' parent.val (parent.val + max 1 total.val) ∧
      target.mem (parent.val + index.val) = .val cursor ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → address ≠ parent.val + index.val →
        target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext heap grown.heap
  have result : Result ((MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) child).copyStToM heap rfl) :=
    ⟨base', target, ran, allocated, root, extension, childGap, pointer, shape, below, gaps, kept⟩
  exact (congrArg Result grownEq).mp result

theorem fixed_memory_row_turn_refusal {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (row : PrimitiveStorageRow primitive) (source : HRef H (.fixed (.ref (.array (.prim primitive))) size))
    (child : HRef H (.array (.prim primitive))) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (selected : heap.index source .fixed (indexValue index) = some child)
    (length : heap.len child .dyn = row.val.length) (tooLarge : ¬ cursor.val + (row.val.length + 1) < W) :
    run (fixedReferenceMemoryTurnCode primitive size) (nestedMemoryControl machine (base source.id) parent total index) = .revert := by
  let controlled := nestedMemoryControl machine (base source.id) parent total index
  have selectedRun : run (fixedReferenceMemorySelectCode primitive size) controlled = .ok (controlled.push (.val (base child.id))) 0 := by
    rcases fixed_reference_memory_select heap primitive size source base frame cursor machine parent total index allocator with
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
  rw [fixedReferenceMemoryTurnCode, run_append_ok selectedRun, run_append_revert refusal]

theorem fixed_memory_rows_demand_bound {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) size)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    nestedStorageDemand (fixedMemoryChildRows heap primitive size source) ≤ cursor.val * heap.len source .fixed := by
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


/--
info: 'Solidity.Backend.MemoryCopies.fixed_memory_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms fixed_memory_length
/--
info: 'Solidity.Backend.MemoryCopies.fixed_memory_rows_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms fixed_memory_rows_length
/--
info: 'Solidity.Backend.MemoryCopies.fixed_memory_rows_repr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_memory_rows_repr
/--
info: 'Solidity.Backend.MemoryCopies.fixed_memory_rows_kept' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_memory_rows_kept
/--
info: 'Solidity.Backend.MemoryCopies.fixed_memory_row_turn_success' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_memory_row_turn_success
/--
info: 'Solidity.Backend.MemoryCopies.fixed_memory_row_turn_refusal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_memory_row_turn_refusal
/--
info: 'Solidity.Backend.MemoryCopies.fixed_memory_rows_demand_bound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_memory_rows_demand_bound

end Solidity.Backend.MemoryCopies
