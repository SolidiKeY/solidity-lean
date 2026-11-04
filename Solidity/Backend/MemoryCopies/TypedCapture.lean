import Solidity.Backend.MemoryCopies.TypedCaptureInterface

/-! Actual typed heap capture reuses the published operation. Word bounds are
derived from live ownership; the reached heap and allocator remain represented. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory Semantics

theorem typed_capture_array_same {A : RefTy} {E F : Ty} (a : ArrTy A E) (b : ArrTy A F) :
    E = F ∧ HEq a b := by
  cases a <;> cases b <;> exact ⟨rfl,HEq.rfl⟩

section Capture
variable {H : HTy} {R Q : RefTy} {E : Ty}
variable (heap : Heap H) (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
variable (start stop offset : Nat) (hs : MemoryOps.SliceBounds (heap.len src sa) start stop)
variable (hd : offset + (stop - start) ≤ heap.len dst da)

theorem typed_capture_frame {T : RefTy} (other : HRef H T) (different : dst.id ≠ other.id) :
    (MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd).get other = heap.get other :=
  MemoryOps.overwriteSlice_frame heap dst other da offset (MemoryOps.sliceElems heap src sa start stop) _ different

theorem typed_capture_length {T : RefTy} {F : Ty} (other : HRef H T) (a : ArrTy T F) :
    (MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd).len other a = heap.len other a := by
  by_cases same : dst.id = other.id
  · obtain ⟨type,equal⟩ := HRef.heq_of_id dst other same
    cases type
    cases equal
    obtain ⟨elementType,arrayEqual⟩ := typed_capture_array_same da a
    cases elementType
    cases arrayEqual
    change (MObj.elems da ((MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd).get dst)).length =
      (MObj.elems da (heap.get dst)).length
    rw [MemoryOps.captureOverwrite,MemoryOps.overwriteSlice_elems]
    apply MemoryOps.replaceSlice_length
    rw [MemoryOps.sliceElems_length heap src sa hs]
    exact hd
  · change (MObj.elems a ((MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd).get other)).length = _
    rw [typed_capture_frame heap src sa dst da start stop offset hs hd other same]
    rfl

theorem typed_capture_cells {T : RefTy} (other : HRef H T) :
    Objects.cells (MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd) other = Objects.cells heap other := by
  cases T with
  | array F =>
    change 1 + (MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd).len other .dyn = 1 + heap.len other .dyn
    rw [typed_capture_length heap src sa dst da start stop offset hs hd other .dyn]
  | fixed F n => rfl
  | struct name => rfl
  | mapping key value => rfl

include hs hd in
theorem typed_capture_spans (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    (base src.id).val + Objects.header sa + start + (stop - start) ≤ cursor.val ∧
    (base dst.id).val + Objects.header da + offset + (stop - start) ≤ cursor.val ∧ stop - start < W := by
  have sourceCells : Objects.header sa + heap.len src sa ≤ Objects.cells heap src := Objects.header_len_le_cells heap sa src
  have destCells : Objects.header da + heap.len dst da ≤ Objects.cells heap dst := Objects.header_len_le_cells heap da dst
  have sourceLive : (base src.id).val + Objects.cells heap src ≤ cursor.val := allocator.live src
  have destLive : (base dst.id).val + Objects.cells heap dst ≤ cursor.val := allocator.live dst
  have ordered : start ≤ stop := hs.ordered
  have bounded : stop ≤ heap.len src sa := hs.bounded
  have limit : cursor.val < W := cursor.isLt
  exact ⟨by omega,by omega,by omega⟩

theorem typed_capture_destination (base : Nat → Fin W) (frame : Nat) (machine target : Machine)
    (represented : Objects.HeapRepr heap base frame machine)
    (copied : ∀ index, index < stop - start →
      target.mem ((base dst.id).val + Objects.header da + offset + index) =
        machine.mem ((base src.id).val + Objects.header sa + start + index))
    (outside : ∀ address, address < (base dst.id).val + Objects.header da + offset ∨
      (base dst.id).val + Objects.header da + offset + (stop - start) ≤ address → target.mem address = machine.mem address) :
    Objects.ArrayRepr (MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd) dst da base target := by
  refine ⟨?_,?_,?_⟩
  · rw [typed_capture_cells heap src sa dst da start stop offset hs hd dst]
    exact (represented.arrays da dst).space
  · intro dynamic
    rw [typed_capture_length heap src sa dst da start stop offset hs hd dst da,
      outside (base dst.id).val (.inl (by omega))]
    exact (represented.arrays da dst).length dynamic
  · intro index value selected
    by_cases inside : offset ≤ index ∧ index < offset + (stop - start)
    · have lower : index - offset < stop - start := by omega
      have position : offset + (index - offset) = index := by omega
      have original : (MObj.elems sa (heap.get src))[start + (index - offset)]? = some value := by
        rw [← MemoryOps.captureOverwrite_read heap src sa dst da start stop offset (index - offset) hs hd lower,position]
        exact selected
      change Objects.ValueRepr base E value (target.mem ((base dst.id).val + Objects.header da + index))
      have address : (base dst.id).val + Objects.header da + index =
          (base dst.id).val + Objects.header da + offset + (index - offset) := by omega
      rw [address,copied (index - offset) lower]
      simpa only [Nat.add_assoc] using (represented.arrays sa src).elements (start + (index - offset)) value original
    · have unchanged : (MObj.elems da ((MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd).get dst))[index]? =
          (MObj.elems da (heap.get dst))[index]? :=
        MemoryOps.overwriteSlice_outside heap dst da offset index (MemoryOps.sliceElems heap src sa start stop) _ (by
          rw [MemoryOps.sliceElems_length heap src sa hs]
          omega)
      rw [unchanged] at selected
      change Objects.ValueRepr base E value (target.mem ((base dst.id).val + Objects.header da + index))
      rw [outside _ (by omega)]
      exact (represented.arrays da dst).elements index value selected

theorem typed_capture_heap (base : Nat → Fin W) (frame : Nat) (machine target : Machine)
    (represented : Objects.HeapRepr heap base frame machine)
    (copied : ∀ index, index < stop - start →
      target.mem ((base dst.id).val + Objects.header da + offset + index) =
        machine.mem ((base src.id).val + Objects.header sa + start + index))
    (outside : ∀ address, address < (base dst.id).val + Objects.header da + offset ∨
      (base dst.id).val + Objects.header da + offset + (stop - start) ≤ address → target.mem address = machine.mem address) :
    Objects.HeapRepr (MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd) base frame target := by
  have endBound : (base dst.id).val + Objects.header da + offset + (stop - start) ≤
      (base dst.id).val + Objects.cells heap dst := by
    have cells : Objects.header da + heap.len dst da ≤ Objects.cells heap dst := Objects.header_len_le_cells heap da dst
    omega
  have otherMemory {T : RefTy} (other : HRef H T) (different : dst.id ≠ other.id) (address : Nat)
      (lower : (base other.id).val ≤ address) (upper : address < (base other.id).val + Objects.cells heap other) :
      target.mem address = machine.mem address := by
    apply outside address
    have separate : (base dst.id).val + Objects.cells heap dst ≤ (base other.id).val ∨
        (base other.id).val + Objects.cells heap other ≤ (base dst.id).val := represented.owner.separated dst other different
    rcases separate with before | after <;> omega
  refine ⟨⟨represented.owner.above,?_,?_⟩,?_,?_,?_⟩
  · intro T other
    rw [typed_capture_cells heap src sa dst da start stop offset hs hd other]
    exact represented.owner.space other
  · intro T U left right different
    rw [typed_capture_cells heap src sa dst da start stop offset hs hd left,
      typed_capture_cells heap src sa dst da start stop offset hs hd right]
    exact represented.owner.separated left right different
  · intro A F a other
    by_cases same : dst.id = other.id
    · obtain ⟨type,equal⟩ := HRef.heq_of_id dst other same
      cases type
      cases equal
      obtain ⟨elementType,arrayEqual⟩ := typed_capture_array_same da a
      cases elementType
      cases arrayEqual
      exact typed_capture_destination heap src sa dst da start stop offset hs hd base frame machine target represented copied outside
    · refine ⟨?_,?_,?_⟩
      · rw [typed_capture_cells heap src sa dst da start stop offset hs hd other]
        exact (represented.arrays a other).space
      · intro dynamic
        rw [typed_capture_length heap src sa dst da start stop offset hs hd other a,
          otherMemory other same (base other.id).val (Nat.le_refl _) (by
            have positive : 0 < Objects.cells heap other := Objects.cells_pos heap other
            omega)]
        exact (represented.arrays a other).length dynamic
      · intro index value selected
        rw [typed_capture_frame heap src sa dst da start stop offset hs hd other same] at selected
        have lower : index < heap.len other a := lt_of_getElem? selected
        have span : Objects.header a + heap.len other a ≤ Objects.cells heap other := Objects.header_len_le_cells heap a other
        change Objects.ValueRepr base F value (target.mem ((base other.id).val + Objects.header a + index))
        rw [otherMemory other same _ (by omega) (by omega)]
        exact (represented.arrays a other).elements index value selected
  · intro name other
    have different : dst.id ≠ other.id := by
      intro same
      exact (da.ne_struct name) (HRef.heq_of_id dst other same).1
    refine ⟨(represented.structs other).space,?_⟩
    intro field primitive selected
    simp only [Heap.field,typed_capture_frame heap src sa dst da start stop offset hs hd other different]
    have bound : fieldOffset (structDef name) field < (structDef name).length := fieldOffset_bound selected
    have span : (structDef name).length ≤ Objects.cells heap other := Nat.le_max_right _ _
    rw [otherMemory other different _ (by omega) (by omega)]
    exact (represented.structs other).fields selected
  · intro name field T other selected
    have different : dst.id ≠ other.id := by
      intro same
      exact (da.ne_struct name) (HRef.heq_of_id dst other same).1
    simp only [Heap.field,typed_capture_frame heap src sa dst da start stop offset hs hd other different]
    have bound : fieldOffset (structDef name) field < (structDef name).length := fieldOffset_bound selected
    have span : (structDef name).length ≤ Objects.cells heap other := Nat.le_max_right _ _
    rw [otherMemory other different _ (by omega) (by omega)]
    exact represented.refs other selected

theorem typed_capture_allocator (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine target : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (copied : ∀ index, index < stop - start →
      target.mem ((base dst.id).val + Objects.header da + offset + index) =
        machine.mem ((base src.id).val + Objects.header sa + start + index))
    (outside : ∀ address, address < (base dst.id).val + Objects.header da + offset ∨
      (base dst.id).val + Objects.header da + offset + (stop - start) ≤ address → target.mem address = machine.mem address) :
    Objects.AllocatorRepr (MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd) base frame cursor target := by
  obtain ⟨_,endBound,_⟩ := typed_capture_spans heap src sa dst da start stop offset hs hd base frame cursor machine allocator
  have positive : 0 < frame := allocator.free.reserved
  have above : frame ≤ (base dst.id).val := allocator.heap.owner.above dst
  refine ⟨typed_capture_heap heap src sa dst da start stop offset hs hd base frame machine target allocator.heap copied outside,
    ⟨allocator.free.reserved,allocator.free.above,?_,?_⟩,?_⟩
  · rw [outside 0 (.inl (by omega))]
    exact allocator.free.cell
  · intro address free
    rw [outside address (.inr (by omega))]
    exact allocator.free.zero address free
  · intro T other
    rw [typed_capture_cells heap src sa dst da start stop offset hs hd other]
    exact allocator.live other

theorem typed_capture_success (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    let after := MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd
    ∃ target,
      MemoryOps.checkedCaptureOverwrite heap src sa dst da start stop offset = some after ∧
      run (typedCaptureCode base src sa dst da start stop offset) machine = .ok target 0 ∧
      Objects.AllocatorRepr after base frame cursor target ∧ target = {machine with mem := target.mem} ∧
      (∀ address, address < frame → target.mem address = machine.mem address) ∧
      (∀ {T : RefTy} (other : HRef H T), dst.id ≠ other.id → after.get other = heap.get other) := by
  obtain ⟨readBound,writeBound,countBound⟩ := typed_capture_spans heap src sa dst da start stop offset hs hd base frame cursor machine allocator
  let source := wmod ((base src.id).val + Objects.header sa + start)
  let destination := wmod ((base dst.id).val + Objects.header da + offset)
  have limit : cursor.val < W := cursor.isLt
  have sourceValue : source.val = (base src.id).val + Objects.header sa + start := Nat.mod_eq_of_lt (by omega)
  have destinationValue : destination.val = (base dst.id).val + Objects.header da + offset := Nat.mod_eq_of_lt (by omega)
  obtain ⟨target,ran,shape,copied,outside⟩ := range_overlap_success machine source destination (stop - start) countBound
    (by rw [sourceValue]; omega) (by rw [destinationValue]; omega)
  have contents : ∀ index, index < stop - start →
      target.mem ((base dst.id).val + Objects.header da + offset + index) =
        machine.mem ((base src.id).val + Objects.header sa + start + index) := by
    intro index lower
    simpa only [sourceValue,destinationValue] using copied index lower
  have untouched : ∀ address, address < (base dst.id).val + Objects.header da + offset ∨
      (base dst.id).val + Objects.header da + offset + (stop - start) ≤ address → target.mem address = machine.mem address := by
    intro address separate
    apply outside address
    simpa only [destinationValue] using separate
  refine ⟨target,MemoryOps.checkedCaptureOverwrite_some heap src sa dst da start stop offset hs hd,?_,
    typed_capture_allocator heap src sa dst da start stop offset hs hd base frame cursor machine target allocator contents untouched,
    shape,?_,fun other different => typed_capture_frame heap src sa dst da start stop offset hs hd other different⟩
  · change run ([.push (.val source),.push (.val destination)] ++ rangeOverlapCode (stop - start)) machine = _
    have entry : run [.push (.val source),.push (.val destination)] machine = .ok ((machine.push (.val source)).push (.val destination)) 0 := by rfl
    rw [run_append_ok entry]
    exact ran
  · intro address below
    apply untouched address
    left
    have above : frame ≤ (base dst.id).val := allocator.heap.owner.above dst
    omega
end Capture
def typedCapture : TypedCaptureCertificate := by
  constructor
  intro H R Q E heap src sa dst da start stop offset base frame cursor machine allocator hs hd
  exact typed_capture_success heap src sa dst da start stop offset hs hd base frame cursor machine allocator

#print axioms typed_capture_array_same
#print axioms typed_capture_frame
#print axioms typed_capture_length
#print axioms typed_capture_cells
#print axioms typed_capture_spans
#print axioms typed_capture_destination
#print axioms typed_capture_heap
#print axioms typed_capture_allocator
#print axioms typed_capture_success
#print axioms typedCapture
end Solidity.Backend.MemoryCopies
