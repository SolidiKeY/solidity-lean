import Solidity.Backend.MemoryCopies.TypedCapture
import Solidity.Backend.MemoryCopies.RangeOverlapControls
import Solidity.Evm.MemoryObjectArrayExamples

/-! Actual typed primitive overlaps and reference-word overwrites preserve
complete ownership, live allocator state and old identity-bearing aliases. -/
namespace Solidity.Backend.MemoryCopies.TypedCaptureControls
open Evm Evm.Memory Semantics
private def R (count : Nat) : RefTy := .fixed (.prim .uint) count
private def H (count : Nat) : HTy := [R count]
private def old (count : Nat) : HRef (H count) (R count) := ⟨0,rfl⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 256 < W := by decide
private def heap (payloads : List (Fin W)) : Heap (H payloads.length) :=
  (⟨values payloads,by rw [values,List.length_map]⟩,())
private def bases : Nat → Fin W := fun _ => wmod 16
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with stack := [w[77]],mem := fun address =>
    if address = 0 then w[256] else if address = 1 ∨ address = 2 then w[16]
    else if address = 7 then w[99]
    else if 16 ≤ address ∧ address < 16 + payloads.length then .val (payloads[address - 16]?.getD (wmod 0)) else w[0]}
private theorem refs {count : Nat} {Q : RefTy} (reference : HRef (H count) Q) : Q = R count ∧ HEq reference (old count) := by
  rcases reference with ⟨index,selected⟩
  cases index with
  | zero => cases selected; exact ⟨rfl,HEq.rfl⟩
  | succ index => cases selected
private theorem heap_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.HeapRepr (heap payloads) bases 8 (machine payloads) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    change 8 ≤ 16
    decide
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    have large : 256 < W := wide
    with_unfolding_all change 16 + max 1 payloads.length ≤ W
    omega
  · intro Q S left right different
    obtain ⟨rfl,leftEq⟩ := refs left
    obtain ⟨rfl,rightEq⟩ := refs right
    cases leftEq
    cases rightEq
    exact (different rfl).elim
  · intro A E shape reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    cases shape
    refine ⟨?_,?_,?_⟩
    · have large : 256 < W := wide
      with_unfolding_all change 16 + max 1 payloads.length ≤ W
      omega
    · intro impossible
      cases impossible
    · intro index item selected
      with_unfolding_all change (values payloads)[index]? = some item at selected
      simp only [values,List.getElem?_map] at selected
      cases chosen : payloads[index]? with
      | none => simp only [chosen,Option.map_none] at selected; cases selected
      | some payload =>
        simp only [chosen,Option.map_some] at selected
        cases selected
        have lower : index < payloads.length := lt_of_getElem? chosen
        change ReprV .uint (indexValue payload) ((machine payloads).mem (16 + index))
        simp only [machine,if_neg (show 16 + index ≠ 0 by omega),
          if_neg (show ¬(16 + index = 1 ∨ 16 + index = 2) by omega),if_neg (show 16 + index ≠ 7 by omega),
          if_pos (show 16 ≤ 16 + index ∧ 16 + index < 16 + payloads.length by omega),
          Nat.add_sub_cancel_left,chosen,Option.getD_some]
        exact ReprV.uint_of rfl
  · intro name reference
    obtain ⟨different,_⟩ := refs reference
    cases different
  · intro name field Q reference fieldType
    obtain ⟨different,_⟩ := refs reference
    cases different
private theorem allocator (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.AllocatorRepr (heap payloads) bases 8 (wmod 256) (machine payloads) := by
  refine ⟨heap_repr payloads bounded,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro address above
    change 256 ≤ address at above
    simp only [machine,if_neg (show address ≠ 0 by omega),
      if_neg (show ¬(address = 1 ∨ address = 2) by omega),if_neg (show address ≠ 7 by omega),
      if_neg (show ¬(16 ≤ address ∧ address < 16 + payloads.length) by omega)]
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    with_unfolding_all change 16 + max 1 payloads.length ≤ 256
    omega

private theorem uint_word {H : HTy} {A : RefTy} (heap : Heap H) (reference : HRef H A) (a : ArrTy A (.prim .uint))
    (base : Nat → Fin W) (target : Machine) (representation : Objects.ArrayRepr heap reference a base target)
    (index : Nat) (payload : Fin W) (selected : (MObj.elems a (heap.get reference))[index]? = some (indexValue payload)) :
    target.mem ((base reference.id).val + Objects.header a + index) = .val payload := by
  obtain ⟨word,stored,equal⟩ := representation.elements index (indexValue payload) selected
  have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
  subst word
  exact stored


private def captured (payloads : List (Fin W)) (start stop offset : Nat)
    (hs : MemoryOps.SliceBounds ((heap payloads).len (old payloads.length) .fixed) start stop)
    (hd : offset + (stop - start) ≤ (heap payloads).len (old payloads.length) .fixed) : Heap (H payloads.length) :=
  MemoryOps.captureOverwrite (heap payloads) (old payloads.length) .fixed (old payloads.length) .fixed start stop offset hs hd

theorem certificate_inhabited : TypedCaptureCertificate := typedCapture

theorem primitive_runtime (payloads : List (Fin W)) (bounded : payloads.length < 128) (start stop offset : Nat)
    (hs : MemoryOps.SliceBounds ((heap payloads).len (old payloads.length) .fixed) start stop)
    (hd : offset + (stop - start) ≤ (heap payloads).len (old payloads.length) .fixed) :
    ∃ target,
      run (typedCaptureCode bases (old payloads.length) .fixed (old payloads.length) .fixed start stop offset) (machine payloads) = .ok target 0 ∧
      Objects.AllocatorRepr (captured payloads start stop offset hs hd) bases 8 (wmod 256) target ∧
      target.mem 0 = w[256] ∧ target.mem 1 = w[16] ∧ target.mem 2 = w[16] ∧ target.mem 7 = w[99] ∧ target.stack = [w[77]] := by
  obtain ⟨target,_,ran,allocated,shape,lower,_⟩ := typed_capture_success (heap payloads) (old payloads.length) .fixed
    (old payloads.length) .fixed start stop offset hs hd bases 8 (wmod 256) (machine payloads) (allocator payloads bounded)
  exact ⟨target,ran,allocated,lower 0 (by decide),lower 1 (by decide),lower 2 (by decide),lower 7 (by decide),congrArg Machine.stack shape⟩

theorem primitive_right : ∃ target,
    run (typedCaptureCode bases (old 4) .fixed (old 4) .fixed 0 3 1) (machine [wmod 11,wmod 23,wmod 37,wmod 41]) = .ok target 0 ∧
      target.mem 0 = w[256] ∧ target.mem 1 = w[16] ∧ target.mem 2 = w[16] ∧
      target.mem 17 = w[11] ∧ target.mem 18 = w[23] ∧ target.mem 19 = w[37] := by
  obtain ⟨target,ran,allocated,cursor,first,second,_,_⟩ :=
    primitive_runtime [wmod 11,wmod 23,wmod 37,wmod 41] (by decide) 0 3 1 ⟨by decide,by with_unfolding_all decide +kernel⟩ (by with_unfolding_all decide +kernel)
  refine ⟨target,ran,cursor,first,second,?_,?_,?_⟩
  · exact uint_word _ (old 4) .fixed bases target (allocated.heap.arrays .fixed (old 4)) 1 (wmod 11) (by with_unfolding_all rfl)
  · exact uint_word _ (old 4) .fixed bases target (allocated.heap.arrays .fixed (old 4)) 2 (wmod 23) (by with_unfolding_all rfl)
  · exact uint_word _ (old 4) .fixed bases target (allocated.heap.arrays .fixed (old 4)) 3 (wmod 37) (by with_unfolding_all rfl)

theorem primitive_left : ∃ target,
    run (typedCaptureCode bases (old 4) .fixed (old 4) .fixed 1 4 0) (machine [wmod 11,wmod 23,wmod 37,wmod 41]) = .ok target 0 ∧
      target.mem 16 = w[23] ∧ target.mem 17 = w[37] ∧ target.mem 18 = w[41] ∧ target.mem 0 = w[256] := by
  obtain ⟨target,ran,allocated,cursor,_,_,_,_⟩ :=
    primitive_runtime [wmod 11,wmod 23,wmod 37,wmod 41] (by decide) 1 4 0 ⟨by decide,by with_unfolding_all decide +kernel⟩ (by with_unfolding_all decide +kernel)
  refine ⟨target,ran,?_,?_,?_,cursor⟩
  · exact uint_word _ (old 4) .fixed bases target (allocated.heap.arrays .fixed (old 4)) 0 (wmod 23) (by with_unfolding_all rfl)
  · exact uint_word _ (old 4) .fixed bases target (allocated.heap.arrays .fixed (old 4)) 1 (wmod 37) (by with_unfolding_all rfl)
  · exact uint_word _ (old 4) .fixed bases target (allocated.heap.arrays .fixed (old 4)) 2 (wmod 41) (by with_unfolding_all rfl)

theorem empty_endpoint (payloads : List (Fin W)) :
    run (typedCaptureCode bases (old payloads.length) .fixed (old payloads.length) .fixed payloads.length payloads.length payloads.length)
      (machine payloads) = .ok (machine payloads) 0 := by
  rw [typedCaptureCode]
  have entry : run [.push (.val (wmod ((bases (old payloads.length).id).val + Objects.header (.fixed : ArrTy (R payloads.length) (.prim .uint)) + payloads.length))),
      .push (.val (wmod ((bases (old payloads.length).id).val + Objects.header (.fixed : ArrTy (R payloads.length) (.prim .uint)) + payloads.length)))] (machine payloads) =
      .ok (((machine payloads).push (.val (wmod (16 + payloads.length)))).push (.val (wmod (16 + payloads.length)))) 0 := by rfl
  rw [run_append_ok entry]
  simpa only [Nat.sub_self] using RangeOverlapControls.empty_copy _ _ _

private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))
theorem primitive_long : ∃ target,
    run (typedCaptureCode bases (old 64) .fixed (old 64) .fixed 0 63 1) (machine long) = .ok target 0 ∧
      target.mem 0 = w[256] ∧ target.mem 1 = w[16] ∧ target.mem 2 = w[16] ∧ target.mem 79 = w[63] := by
  have hs : MemoryOps.SliceBounds ((heap long).len (old 64) .fixed) 0 63 := ⟨by decide,by with_unfolding_all decide +kernel⟩
  have hd : 1 + (63 - 0) ≤ (heap long).len (old 64) .fixed := by with_unfolding_all decide +kernel
  obtain ⟨target,ran,allocated,cursor,first,second,_,_⟩ :=
    primitive_runtime long (by rw [long,List.length_ofFn]; decide) 0 63 1 hs hd
  refine ⟨target,ran,cursor,first,second,?_⟩
  apply uint_word _ (old 64) .fixed bases target (allocated.heap.arrays .fixed (old 64)) 63 (wmod 63)
  have snapshot : (MObj.elems .fixed ((captured long 0 63 1 hs hd).get (old 64)))[63]? =
      (MObj.elems .fixed ((heap long).get (old 64)))[62]? :=
    MemoryOps.captureOverwrite_read (heap long) (old 64) .fixed (old 64) .fixed 0 63 1 62 hs hd (by decide)
  exact snapshot.trans (by with_unfolding_all rfl)

private abbrev child : RefTy := .array (.prim .uint)
private abbrev parentType : RefTy := .fixed (.ref child) 2
private abbrev RH : HTy := [child,child,parentType]
private def left : HRef RH child := ⟨0,rfl⟩
private def right : HRef RH child := ⟨1,rfl⟩
private def parent : HRef RH parentType := ⟨2,rfl⟩
private structure RefInput where
  heap : Heap RH
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def refInput : RefInput := ⟨_,_,_,ObjectArrayExamples.initial_allocator⟩
private def refHeap : Heap RH := refInput.heap.set parent (MObj.setElem .fixed (refInput.heap.get parent) 0 right)
private def refMachine : Machine := writeMachine refInput.machine 32 w[24]
private theorem refAllocator : Objects.AllocatorRepr refHeap refInput.base 8 (wmod 40) refMachine :=
  refInput.allocator.setArray parent .fixed 0 (by with_unfolding_all decide +kernel) right w[24] rfl
private def refAfter : Heap RH := MemoryOps.captureOverwrite refHeap parent .fixed parent .fixed 0 1 1 ⟨by decide,by with_unfolding_all decide +kernel⟩ (by with_unfolding_all decide +kernel)

theorem reference_runtime : ∃ target,
    run (typedCaptureCode refInput.base parent .fixed parent .fixed 0 1 1) refMachine = .ok target 0 ∧
      Objects.AllocatorRepr refAfter refInput.base 8 (wmod 40) target ∧
      target.mem 0 = w[40] ∧ target.mem 1 = w[24] ∧ target.mem 2 = w[24] ∧
      target.mem 32 = w[24] ∧ target.mem 33 = w[24] ∧ target.mem 17 = w[7] ∧ target.mem 25 = w[9] ∧ target.stack = [w[77]] := by
  obtain ⟨target,_,ran,allocated,shape,lower,frame⟩ := typed_capture_success refHeap parent .fixed parent .fixed 0 1 1
    ⟨by decide,by with_unfolding_all decide +kernel⟩ (by with_unfolding_all decide +kernel) refInput.base 8 (wmod 40) refMachine refAllocator
  refine ⟨target,ran,allocated,lower 0 (by decide),lower 1 (by decide),lower 2 (by decide),?_,?_,?_,?_,congrArg Machine.stack shape⟩
  · exact (allocated.heap.arrays .fixed parent).elements 0 right (by with_unfolding_all rfl)
  · exact (allocated.heap.arrays .fixed parent).elements 1 right (by with_unfolding_all rfl)
  · apply uint_word _ left .dyn refInput.base target (allocated.heap.arrays .dyn left) 0 (wmod 7)
    rw [frame left (by decide)]
    with_unfolding_all rfl
  · apply uint_word _ right .dyn refInput.base target (allocated.heap.arrays .dyn right) 0 (wmod 9)
    rw [frame right (by decide)]
    with_unfolding_all rfl

theorem reference_identities : (MObj.elems .fixed (refAfter.get parent)) = [right,right] ∧
    refAfter.get left = refHeap.get left ∧ refAfter.get right = refHeap.get right := by
  exact ⟨by with_unfolding_all rfl,
    typed_capture_frame refHeap parent .fixed parent .fixed 0 1 1 _ _ left (by decide),
    typed_capture_frame refHeap parent .fixed parent .fixed 0 1 1 _ _ right (by decide)⟩

theorem dynamic_runtime : ∃ target,
    run (typedCaptureCode refInput.base left .dyn right .dyn 0 1 0) refInput.machine = .ok target 0 ∧
      target.mem 0 = w[40] ∧ target.mem 24 = w[1] ∧ target.mem 25 = w[7] ∧ target.mem 17 = w[7] ∧ target.mem 32 = w[16] := by
  have hs : MemoryOps.SliceBounds (refInput.heap.len left .dyn) 0 1 := ⟨by decide,by with_unfolding_all decide +kernel⟩
  have hd : 0 + (1 - 0) ≤ refInput.heap.len right .dyn := by with_unfolding_all decide +kernel
  obtain ⟨target,_,ran,allocated,_,lower,frame⟩ := typed_capture_success refInput.heap left .dyn right .dyn 0 1 0
    hs hd refInput.base 8 (wmod 40) refInput.machine refInput.allocator
  refine ⟨target,ran,lower 0 (by decide),?_,?_,?_,?_⟩
  · have header : target.mem (refInput.base right.id).val =
        .val (wmod ((MemoryOps.captureOverwrite refInput.heap left .dyn right .dyn 0 1 0 hs hd).len right .dyn)) :=
      (allocated.heap.arrays .dyn right).length rfl
    rw [typed_capture_length refInput.heap left .dyn right .dyn 0 1 0 hs hd right .dyn] at header
    with_unfolding_all exact header
  · exact uint_word _ right .dyn refInput.base target (allocated.heap.arrays .dyn right) 0 (wmod 7) (by with_unfolding_all rfl)
  · apply uint_word _ left .dyn refInput.base target (allocated.heap.arrays .dyn left) 0 (wmod 7)
    rw [frame left (by decide)]
    with_unfolding_all rfl
  · exact (allocated.heap.arrays .fixed parent).elements 0 left (by rw [frame parent (by decide)]; with_unfolding_all rfl)

theorem streaming_rejected (target : Machine)
    (ran : run (typedCaptureCode bases (old 4) .fixed (old 4) .fixed 0 3 1) (machine [wmod 11,wmod 23,wmod 37,wmod 41]) = .ok target 0) :
    target.mem 18 ≠ w[11] := by
  obtain ⟨actual,execution,_,_,_,_,correct,_⟩ := primitive_right
  rw [ran] at execution
  have same : target.mem 18 = actual.mem 18 := congrArg (fun machine => machine.mem 18) (Out.ok.inj execution).1
  rw [same,correct]
  decide

theorem invalid_bounds : MemoryOps.checkedCaptureOverwrite (heap [wmod 11,wmod 23]) (old 2) .fixed (old 2) .fixed 0 3 0 = none := by
  apply (MemoryOps.checkedCaptureOverwrite_none_iff _ _ _ _ _ _ _ _).mpr
  right
  left
  with_unfolding_all decide +kernel

#print axioms certificate_inhabited
#print axioms primitive_runtime
#print axioms primitive_right
#print axioms primitive_left
#print axioms empty_endpoint
#print axioms primitive_long
#print axioms reference_runtime
#print axioms reference_identities
#print axioms dynamic_runtime
#print axioms streaming_rejected
#print axioms invalid_bounds
end Solidity.Backend.MemoryCopies.TypedCaptureControls
