import Solidity.Backend.MemoryCopies.CheckedCaptureInterface

/-! Bounds are tested against the same represented arrays before the existing
copy runs. Reversed, source/destination overrun and non-word endpoints revert. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem capture_length_run {H : HTy} {R : RefTy} {E : Ty} (heap : Heap H) (reference : HRef H R)
    (a : ArrTy R E) (base : Nat → Fin W) (machine : Machine)
    (represented : Objects.ArrayRepr heap reference a base machine) :
    run (captureLengthCode a (base reference.id)) machine = .ok (machine.push (.val (wmod (heap.len reference a)))) 0 := by
  cases a with
  | dyn =>
    simp only [captureLengthCode,run,exec_cons_zero,Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,represented.length rfl]
  | @fixed E count =>
    have actual : heap.len reference .fixed = count := by
      change (MObj.elems .fixed (heap.get reference)).length = count
      rw [MObj.elems_fixed]
      exact (heap.get reference).property
    rw [actual]
    rfl

theorem capture_length_bounded {H : HTy} {R : RefTy} {E : Ty} (heap : Heap H) (reference : HRef H R)
    (a : ArrTy R E) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) : heap.len reference a < W := by
  have cells : Objects.header a + heap.len reference a ≤ Objects.cells heap reference := Objects.header_len_le_cells heap a reference
  have live : (base reference.id).val + Objects.cells heap reference ≤ cursor.val := allocator.live reference
  have limit : cursor.val < W := cursor.isLt
  omega

theorem capture_endpoint_run {H : HTy} {R : RefTy} {E : Ty} (heap : Heap H) (reference : HRef H R)
    (a : ArrTy R E) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) (endpoint : Nat) :
    run (captureEndpointCode a (base reference.id) endpoint) machine =
      if endpoint ≤ heap.len reference a then .ok machine 0 else .revert := by
  have lengthBound : heap.len reference a < W := capture_length_bounded heap reference a base frame cursor machine allocator
  by_cases encoded : endpoint < W
  · rw [captureEndpointCode,if_pos encoded,List.append_assoc,
      run_append_ok (capture_length_run heap reference a base machine (allocator.heap.arrays a reference))]
    by_cases accepted : endpoint ≤ heap.len reference a
    · have comparison : ¬ heap.len reference a < endpoint := by omega
      simp only [assertTop,run,List.cons_append,List.nil_append,exec_cons_zero,Instr.step,Machine.push,Machine.next,
        Out.ok_bind,exec_nil,wmod_def,Nat.mod_eq_of_lt encoded,Nat.mod_eq_of_lt lengthBound,comparison,decide_false,decide_true,Bool.false_eq_true,↓reduceIte,bword,
        if_pos accepted,Fin.mk_one,Fin.isValue,Fin.val_one,Nat.succ_ne_self,exec_cons_succ,
        ]
    · have comparison : heap.len reference a < endpoint := by omega
      simp only [assertTop,run,List.cons_append,List.nil_append,exec_cons_zero,Instr.step,Machine.push,Machine.next,
        Out.ok_bind,exec_nil,wmod_def,Nat.mod_eq_of_lt encoded,Nat.mod_eq_of_lt lengthBound,comparison,decide_true,decide_false,Bool.false_eq_true,↓reduceIte,bword,
        if_neg accepted,Fin.mk_one,Fin.isValue,Fin.val_one,Nat.succ_ne_self,
        Out.revert_bind]
  · have rejected : ¬ endpoint ≤ heap.len reference a := by omega
    simp only [captureEndpointCode,if_neg encoded,if_neg rejected,run,exec_cons_zero,Instr.step,Out.revert_bind]

theorem checked_capture_code_run {H : HTy} {R Q : RefTy} {E : Ty} (heap : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (start stop offset : Nat)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    run (checkedTypedCaptureCode base src sa dst da start stop offset) machine =
      if start ≤ stop ∧ stop ≤ heap.len src sa ∧ offset + (stop - start) ≤ heap.len dst da
      then run (typedCaptureCode base src sa dst da start stop offset) machine else .revert := by
  by_cases ordered : start ≤ stop
  · rw [checkedTypedCaptureCode,if_pos ordered,List.append_assoc]
    by_cases sourceFits : stop ≤ heap.len src sa
    · have first : run (captureEndpointCode sa (base src.id) stop) machine = .ok machine 0 := by
        rw [capture_endpoint_run heap src sa base frame cursor machine allocator stop,if_pos sourceFits]
      rw [run_append_ok first]
      by_cases destinationFits : offset + (stop - start) ≤ heap.len dst da
      · have second : run (captureEndpointCode da (base dst.id) (offset + (stop - start))) machine = .ok machine 0 := by
          rw [capture_endpoint_run heap dst da base frame cursor machine allocator (offset + (stop - start)),if_pos destinationFits]
        rw [run_append_ok second,if_pos ⟨ordered,sourceFits,destinationFits⟩]
      · have second : run (captureEndpointCode da (base dst.id) (offset + (stop - start))) machine = .revert := by
          rw [capture_endpoint_run heap dst da base frame cursor machine allocator (offset + (stop - start)),if_neg destinationFits]
        rw [run_append_revert second,if_neg (by intro accepted; exact destinationFits accepted.2.2)]
    · have first : run (captureEndpointCode sa (base src.id) stop) machine = .revert := by
        rw [capture_endpoint_run heap src sa base frame cursor machine allocator stop,if_neg sourceFits]
      rw [run_append_revert first,if_neg (by intro accepted; exact sourceFits accepted.2.1)]
  · rw [checkedTypedCaptureCode,if_neg ordered,if_neg (by intro accepted; exact ordered accepted.1)]
    rfl

theorem checked_capture_correct {H : HTy} {R Q : RefTy} {E : Ty} (heap : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (start stop offset : Nat)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    (∃ after target,
      MemoryOps.checkedCaptureOverwrite heap src sa dst da start stop offset = some after ∧
      run (checkedTypedCaptureCode base src sa dst da start stop offset) machine = .ok target 0 ∧
      Objects.AllocatorRepr after base frame cursor target ∧ target = {machine with mem := target.mem} ∧
      (∀ address, address < frame → target.mem address = machine.mem address) ∧
      (∀ {T : RefTy} (other : HRef H T), dst.id ≠ other.id → after.get other = heap.get other)) ∨
    (MemoryOps.checkedCaptureOverwrite heap src sa dst da start stop offset = none ∧
      run (checkedTypedCaptureCode base src sa dst da start stop offset) machine = .revert) := by
  by_cases valid : start ≤ stop ∧ stop ≤ heap.len src sa ∧ offset + (stop - start) ≤ heap.len dst da
  · let hs : MemoryOps.SliceBounds (heap.len src sa) start stop := ⟨valid.1,valid.2.1⟩
    obtain ⟨target,checked,ran,allocated,shape,lower,other⟩ := typed_capture_success heap src sa dst da start stop offset hs valid.2.2
      base frame cursor machine allocator
    left
    refine ⟨_,target,checked,?_,allocated,shape,lower,other⟩
    rw [checked_capture_code_run heap src sa dst da start stop offset base frame cursor machine allocator,if_pos valid]
    exact ran
  · right
    refine ⟨?_,?_⟩
    · apply (MemoryOps.checkedCaptureOverwrite_none_iff heap src sa dst da start stop offset).mpr
      omega
    · rw [checked_capture_code_run heap src sa dst da start stop offset base frame cursor machine allocator,if_neg valid]

theorem checked_capture_success {H : HTy} {R Q : RefTy} {E : Ty} (heap : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (start stop offset : Nat)
    (hs : MemoryOps.SliceBounds (heap.len src sa) start stop)
    (hd : offset + (stop - start) ≤ heap.len dst da)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    ∃ target,
      MemoryOps.checkedCaptureOverwrite heap src sa dst da start stop offset = some (MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd) ∧
      run (checkedTypedCaptureCode base src sa dst da start stop offset) machine = .ok target 0 ∧
      Objects.AllocatorRepr (MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd) base frame cursor target ∧
      target = {machine with mem := target.mem} ∧
      (∀ address, address < frame → target.mem address = machine.mem address) ∧
      (∀ {T : RefTy} (other : HRef H T), dst.id ≠ other.id →
        (MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd).get other = heap.get other) := by
  obtain ⟨target,checked,ran,allocated,shape,lower,other⟩ :=
    typed_capture_success heap src sa dst da start stop offset hs hd base frame cursor machine allocator
  refine ⟨target,checked,?_,allocated,shape,lower,other⟩
  rw [checked_capture_code_run heap src sa dst da start stop offset base frame cursor machine allocator,
    if_pos ⟨hs.1,hs.2,hd⟩]
  exact ran

def checkedCapture : CheckedCaptureCertificate := ⟨checked_capture_correct⟩

#print axioms capture_length_run
#print axioms capture_length_bounded
#print axioms capture_endpoint_run
#print axioms checked_capture_code_run
#print axioms checked_capture_correct
#print axioms checked_capture_success
#print axioms checkedCapture
end Solidity.Backend.MemoryCopies
