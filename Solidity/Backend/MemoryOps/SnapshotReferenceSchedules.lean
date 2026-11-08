import Solidity.Backend.MemoryOps.SnapshotScheduleControls

/-! Nonprimitive and fixed-array schedule witnesses. Snapshots retain old HRef
identities; they neither allocate/deep-copy children nor manufacture Source data. -/
namespace Solidity.Backend.MemoryOps.ReferenceScheduleControls
open ScheduleControls SequenceFixtures

private theorem cycles_agree {α : Type} (xs : List α) (he : xs[2]? = xs[1]?) (copies : Nat) :
    ∀ k, xs[captureOrigin (restoreCycles copies) k]? = xs[k]? := by
  have hc : ∀ k, xs[captureOrigin cycle k]? = xs[k]? := by
    intro k
    rw [cycle_origin]
    by_cases hk : k = 1
    · subst k; rw [ite_eq_left rfl]; exact he
    · rw [ite_eq_right hk]
  induction copies with
  | zero => intro k; rfl
  | succ copies ih =>
    intro k
    rw [restoreCycles,captureOrigin_append]
    exact (hc _).trans (ih k)

private abbrev B := BoolChildRef
private abbrev C : RefTy := .array (.ref B)
private abbrev H : HTy := [B,B,C]
private def left : HRef H B := ⟨0,rfl⟩
private def right : HRef H B := ⟨1,rfl⟩
private def root : HRef H C := ⟨2,rfl⟩
private def values (n : Nat) := [left,right,right] ++ List.replicate n left
set_option backward.isDefEq.respectTransparency false in
private def hp (n : Nat) (hn : n+3 < 2^256) : Heap H :=
  (⟨[true,false],by decide⟩,⟨[false,true],by decide⟩,
   ⟨values n,by simp only [values,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,())
set_option backward.isDefEq.respectTransparency false in
private theorem len (n : Nat) (hn : n+3 < 2^256) : (hp n hn).len root .dyn = n+3 := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,root,values,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
private theorem hs (n : Nat) (hn : n+3 < 2^256) : SliceBounds ((hp n hn).len root .dyn) 0 1 := by rw [len]; exact ⟨by decide,by omega⟩
private theorem hd (n : Nat) (hn : n+3 < 2^256) : 1+(1-0) ≤ (hp n hn).len root .dyn := by rw [len]; omega
private def mid (n : Nat) (hn : n+3 < 2^256) := captureOverwrite (hp n hn) root .dyn root .dyn 0 1 1 (hs n hn) (hd n hn)

theorem reference_cycles (n copies : Nat) (hn : n+3 < 2^256) :
    runCaptures (hp n hn) root .dyn (restoreCycles copies) = some (hp n hn) := by
  have hv : CapturesValid ((hp n hn).len root .dyn) (restoreCycles copies) := by
    rw [len]; exact cycles_valid _ copies (by omega)
  obtain ⟨out,ho⟩ := (runCaptures_success_iff (hp n hn) root .dyn _).mpr hv
  have ha := cycles_agree (MObj.elems .dyn ((hp n hn).get root)) (by simp only [MObj.elems_dyn]; rfl) copies
  exact ho.trans (congrArg some ((runCaptures_heap_restore_iff _ _ _ _ _ ho).mpr ha))

/-- Complete ordered reference identities and both distinct old child contents. -/
theorem reference_final (n copies : Nat) (hn : n+3 < 2^256) :
    ∃ out, runCaptures (hp n hn) root .dyn (restoreCycles copies) = some out ∧
      MObj.elems .dyn (out.get root) = values n ∧
      (MObj.elems .dyn (out.get root)).map HRef.id = [0,1,1] ++ List.replicate n 0 ∧
      MObj.elems .dyn (out.get left) = [true,false] ∧ MObj.elems .dyn (out.get right) = [false,true] := by
  refine ⟨hp n hn,reference_cycles n copies hn,?_,?_,?_,?_⟩
  · simp only [MObj.elems_dyn]; rfl
  · simp only [MObj.elems_dyn]
    change (values n).map HRef.id = _
    simp only [values,List.map_append,List.map_cons,List.map_nil,List.map_replicate]; rfl
  · simp only [MObj.elems_dyn]; rfl
  · simp only [MObj.elems_dyn]; rfl

/-- The first actual copy changes a reference identity and introduces an old
alias; both child objects stay live. Actual second copy recaptures that alias. -/
theorem reference_intermediate (n : Nat) (hn : n+3 < 2^256) :
    runCaptures (hp n hn) root .dyn [first] = some (mid n hn) ∧
    MObj.elems .dyn ((mid n hn).get root) = [left,left,right] ++ List.replicate n left ∧
    MObj.elems .dyn ((mid n hn).get left) = [true,false] ∧
    MObj.elems .dyn ((mid n hn).get right) = [false,true] ∧
    (mid n hn).get root ≠ (hp n hn).get root ∧
    checkedCaptureOverwrite (mid n hn) root .dyn root .dyn 1 3 0 = some (hp n hn) := by
  have hf : checkedCaptureOverwrite (hp n hn) root .dyn root .dyn 0 1 1 = some (mid n hn) :=
    checkedCaptureOverwrite_some _ _ _ _ _ _ _ _ (hs n hn) (hd n hn)
  have hv : MObj.elems .dyn ((mid n hn).get root) = [left,left,right] ++ List.replicate n left := by
    dsimp only [mid,captureOverwrite]
    rw [overwriteSlice_elems]; simp only [sliceElems,MObj.elems_dyn]; rfl
  refine ⟨?_,hv,?_,?_,?_,?_⟩
  · rw [runCaptures_singleton]; exact hf
  · rw [checkedCaptureOverwrite_frame _ _ _ _ _ _ _ _ _ hf left (by decide)]
    simp only [MObj.elems_dyn]; rfl
  · rw [checkedCaptureOverwrite_frame _ _ _ _ _ _ _ _ _ hf right (by decide)]
    simp only [MObj.elems_dyn]; rfl
  · intro he
    have hx := congrArg (fun o : MObj H C => ((MObj.elems .dyn o)[1]?).map HRef.id) he
    rw [hv] at hx
    simp only [MObj.elems_dyn] at hx
    have bad : (some 0 : Option Nat) ≠ some 1 := by decide
    exact bad hx
  · have hc : runCaptures (hp n hn) root .dyn cycle = some (hp n hn) := by
      simpa only [restoreCycles,List.append_nil] using reference_cycles n 1 hn
    obtain ⟨actual,hfirst,hsecond⟩ := (runCaptures_cons_some _ _ _ _ first [repair]).mp hc
    have he := Option.some.inj (hf.symm.trans hfirst)
    rw [← he,runCaptures_singleton] at hsecond
    exact hsecond

private abbrev F : RefTy := .fixed (.ref B) 3
private abbrev FH : HTy := [B,B,F]
private def fl : HRef FH B := ⟨0,rfl⟩
private def fr : HRef FH B := ⟨1,rfl⟩
private def fixedRoot : HRef FH F := ⟨2,rfl⟩
private def fixedHeap : Heap FH := (⟨[true],by decide⟩,⟨[false],by decide⟩,⟨[fl,fr,fr],rfl⟩,())
private theorem fixed_len : fixedHeap.len fixedRoot .fixed = 3 := by
  simp only [Heap.len,MObj.elems_fixed]; rfl

/-- Fixed nonprimitive arrays execute the SAME uncapped runtime schedules;
this is an inhabited generic-ArrTy instance, not a different executor. -/
theorem fixed_cycles (copies : Nat) :
    runCaptures fixedHeap fixedRoot .fixed (restoreCycles copies) = some fixedHeap := by
  have hv : CapturesValid (fixedHeap.len fixedRoot .fixed) (restoreCycles copies) := by
    rw [fixed_len]; exact cycles_valid 3 copies (by decide)
  obtain ⟨out,ho⟩ := (runCaptures_success_iff fixedHeap fixedRoot .fixed _).mpr hv
  have ha := cycles_agree (MObj.elems .fixed (fixedHeap.get fixedRoot)) (by simp only [MObj.elems_fixed]; rfl) copies
  exact ho.trans (congrArg some ((runCaptures_heap_restore_iff _ _ _ _ _ ho).mpr ha))

theorem fixed_intermediate :
    ∃ mid, runCaptures fixedHeap fixedRoot .fixed [first] = some mid ∧
      MObj.elems .fixed (mid.get fixedRoot) = [fl,fl,fr] ∧
      MObj.elems .dyn (mid.get fl) = [true] ∧ MObj.elems .dyn (mid.get fr) = [false] ∧
      checkedCaptureOverwrite mid fixedRoot .fixed fixedRoot .fixed 1 3 0 = some fixedHeap := by
  have hs : SliceBounds (fixedHeap.len fixedRoot .fixed) 0 1 := ⟨by decide,by rw [fixed_len]; decide⟩
  have hd : 1+(1-0) ≤ fixedHeap.len fixedRoot .fixed := by rw [fixed_len]; decide
  let mid := captureOverwrite fixedHeap fixedRoot .fixed fixedRoot .fixed 0 1 1 hs hd
  have hf := checkedCaptureOverwrite_some fixedHeap fixedRoot .fixed fixedRoot .fixed 0 1 1 hs hd
  refine ⟨mid,?_,?_,?_,?_,?_⟩
  · rw [runCaptures_singleton]; exact hf
  · dsimp only [mid,captureOverwrite]
    rw [overwriteSlice_elems]; simp only [sliceElems,MObj.elems_fixed]; rfl
  · rw [checkedCaptureOverwrite_frame _ _ _ _ _ _ _ _ _ hf fl (by decide)]
    simp only [MObj.elems_dyn]; rfl
  · rw [checkedCaptureOverwrite_frame _ _ _ _ _ _ _ _ _ hf fr (by decide)]
    simp only [MObj.elems_dyn]; rfl
  · have hc : runCaptures fixedHeap fixedRoot .fixed cycle = some fixedHeap := by
      simpa only [restoreCycles,List.append_nil] using fixed_cycles 1
    obtain ⟨actual,hfirst,hsecond⟩ := (runCaptures_cons_some _ _ _ _ first [repair]).mp hc
    have he := Option.some.inj (hf.symm.trans hfirst)
    rw [← he,runCaptures_singleton] at hsecond
    exact hsecond

theorem boundary33 :
    runCaptures (hp 33 (by decide)) root .dyn (restoreCycles 3) = some (hp 33 (by decide)) ∧
    (hp 33 (by decide)).index root .dyn (⟨32,by decide⟩ : U) = some left ∧
    (hp 33 (by decide)).index root .dyn one = some right ∧
    (hp 33 (by decide)).index root .dyn (⟨2,by decide⟩ : U) = some right := by
  refine ⟨reference_cycles 33 3 (by decide),?_,?_,?_⟩
  all_goals change (MObj.elems .dyn ((hp 33 (by decide)).get root))[_]? = _
  all_goals simp only [MObj.elems_dyn]; rfl

/-- info: 'Solidity.Backend.MemoryOps.ReferenceScheduleControls.reference_cycles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_cycles
/-- info: 'Solidity.Backend.MemoryOps.ReferenceScheduleControls.reference_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_final
/-- info: 'Solidity.Backend.MemoryOps.ReferenceScheduleControls.reference_intermediate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_intermediate
/-- info: 'Solidity.Backend.MemoryOps.ReferenceScheduleControls.fixed_cycles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fixed_cycles
/-- info: 'Solidity.Backend.MemoryOps.ReferenceScheduleControls.fixed_intermediate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fixed_intermediate
/-- info: 'Solidity.Backend.MemoryOps.ReferenceScheduleControls.boundary33' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms boundary33
end Solidity.Backend.MemoryOps.ReferenceScheduleControls
