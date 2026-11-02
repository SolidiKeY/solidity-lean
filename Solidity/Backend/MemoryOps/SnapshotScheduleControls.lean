import Solidity.Backend.MemoryOps.SnapshotProvenance

/-! Runtime schedules and actual intrinsic witnesses. restoreCycles constructs
only input argument lists; it is not an executor and imposes no schedule cap. -/
namespace Solidity.Backend.MemoryOps.ScheduleControls
open SequenceFixtures

def first : SnapshotArgs := (0,1,1)
def repair : SnapshotArgs := (1,3,0)
def cycle : List SnapshotArgs := [first,repair]
def restoreCycles : Nat → List SnapshotArgs
  | 0 => []
  | k+1 => cycle ++ restoreCycles k

theorem cycle_valid (size : Nat) (hs : 3 ≤ size) : CapturesValid size cycle := by
  intro x hx
  simp only [cycle,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · change 0 ≤ 1 ∧ 1 ≤ size ∧ 1+(1-0) ≤ size
    omega
  · change 1 ≤ 3 ∧ 3 ≤ size ∧ 0+(3-1) ≤ size
    omega

theorem cycles_valid (size k : Nat) (hs : 3 ≤ size) : CapturesValid size (restoreCycles k) := by
  induction k with
  | zero => intro x hx; cases hx
  | succ k ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact cycle_valid size hs x hx
    · exact ih x hx

theorem cycles_length (k : Nat) : (restoreCycles k).length = 2*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [restoreCycles,List.length_append,cycle,List.length_cons,List.length_nil,ih]
    omega

/-- A provenance map need NOT be identity for contents to be restored: index1
comes from original index2, whose value may agree with original index1. -/
theorem cycle_origin (k : Nat) : captureOrigin cycle k = if k = 1 then 2 else k := by
  by_cases h0 : k = 0
  · subst k; rfl
  by_cases h1 : k = 1
  · subst k; rfl
  rw [if_neg h1]
  have hk : 2 ≤ k := by omega
  change snapshotOrigin first (snapshotOrigin repair k) = k
  have hr : snapshotOrigin repair k = k := by
    change (if 0 ≤ k ∧ k < 2 then 1+(k-0) else k) = k
    rw [if_neg (by omega)]
  have hf : snapshotOrigin first k = k := by
    change (if 1 ≤ k ∧ k < 2 then 0+(k-1) else k) = k
    rw [if_neg (by omega)]
  rw [hr,hf]

private abbrev B := BoolChildRef
private abbrev H : HTy := [B,B]
private def r : HRef H B := ⟨0,rfl⟩
private def neighbor : HRef H B := ⟨1,rfl⟩
private def old (n : Nat) := [true,false,false] ++ List.replicate n false
private def hp (n : Nat) (hn : n+3 < 2^256) : Heap H :=
  (⟨old n,by simp only [old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,⟨[false,true],by decide⟩,())
private theorem len (n : Nat) (hn : n+3 < 2^256) : (hp n hn).len r .dyn = n+3 := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,r,old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
private theorem hs (n : Nat) (hn : n+3 < 2^256) : SliceBounds ((hp n hn).len r .dyn) 0 1 := by
  rw [len]; exact ⟨by decide,by omega⟩
private theorem hd (n : Nat) (hn : n+3 < 2^256) : 1+(1-0) ≤ (hp n hn).len r .dyn := by rw [len]; omega
private def mid (n : Nat) (hn : n+3 < 2^256) := captureOverwrite (hp n hn) r .dyn r .dyn 0 1 1 (hs n hn) (hd n hn)
private def sv : Source.Data D BoolChildTy := .val (.cdRef rfl 7)
private theorem initial (n : Nat) (hn : n+3 < 2^256) : BoolChildRepr (bools (old n)) (fun _ => 7) (hp n hn) sv r := by
  refine ⟨rfl,?_⟩; simp only [MObj.elems_dyn]; rfl

/-- Computed INITIAL provenance agreement for arbitrarily many restoring
cycles. No poststate or stagewise agreement is an input. -/
theorem primitive_provenance (n copies : Nat) (hn : n+3 < 2^256) :
    ∀ k, (MObj.elems .dyn ((hp n hn).get r))[captureOrigin (restoreCycles copies) k]? =
      (MObj.elems .dyn ((hp n hn).get r))[k]? := by
  have hc : ∀ k, (MObj.elems .dyn ((hp n hn).get r))[captureOrigin cycle k]? =
      (MObj.elems .dyn ((hp n hn).get r))[k]? := by
    intro k
    rw [cycle_origin]
    by_cases hk : k = 1
    · subst k; rw [if_pos rfl]; simp only [MObj.elems_dyn]; rfl
    · rw [if_neg hk]
  induction copies with
  | zero => intro k; rfl
  | succ copies ih =>
    intro k
    rw [restoreCycles,captureOrigin_append]
    exact (hc _).trans (ih k)

/-- Success from original bounds, then restoration from computed provenance;
the run/desired restoration relation is not supplied as a premise. -/
theorem primitive_cycles (n copies : Nat) (hn : n+3 < 2^256) :
    runCaptures (hp n hn) r .dyn (restoreCycles copies) = some (hp n hn) := by
  have hv : CapturesValid ((hp n hn).len r .dyn) (restoreCycles copies) := by
    rw [len]; exact cycles_valid _ copies (by omega)
  obtain ⟨out,ho⟩ := (runCaptures_success_iff (hp n hn) r .dyn _).mpr hv
  have he := (runCaptures_heap_restore_iff (hp n hn) out r .dyn _ ho).mpr (primitive_provenance n copies hn)
  exact ho.trans (congrArg some he)

/-- Reuse actual checkpoint20 witnesses, including the FALSE intermediate
representation and second capture from that changed intermediate heap. -/
theorem primitive_intermediate (n : Nat) (hn : n+3 < 2^256) :
    runCaptures (hp n hn) r .dyn [first] = some (mid n hn) ∧
    MObj.elems .dyn ((mid n hn).get r) = [true,true,false] ++ List.replicate n false ∧
    ¬ BoolChildRepr (bools (old n)) (fun _ => 7) (mid n hn) sv r ∧
    checkedCaptureOverwrite (mid n hn) r .dyn r .dyn 1 3 0 = some (hp n hn) ∧
    MObj.elems .dyn ((mid n hn).get neighbor) = [false,true] := by
  refine ⟨?_,(RecaptureControls.payloads n hn).2.1,(RecaptureControls.actual_restore n hn).2.1,
    (RecaptureControls.reached_reads n hn).1,(RecaptureControls.reached_reads n hn).2.2.1⟩
  rw [runCaptures_singleton]
  exact (RecaptureControls.actual_restore n hn).1

theorem primitive_final (n copies : Nat) (hn : n+3 < 2^256) :
    ∃ out, runCaptures (hp n hn) r .dyn (restoreCycles copies) = some out ∧
      BoolChildRepr (bools (old n)) (fun _ => 7) out sv r ∧
      MObj.elems .dyn (out.get r) = old n ∧ MObj.elems .dyn (out.get neighbor) = [false,true] := by
  refine ⟨hp n hn,primitive_cycles n copies hn,initial n hn,?_,?_⟩
  all_goals simp only [MObj.elems_dyn]; rfl

private theorem hu (n : Nat) (hn : n+3 < 2^256) : SliceBounds ((hp n hn).len r .dyn) 1 3 := by
  rw [len]; exact ⟨by decide,by omega⟩
private theorem he (n : Nat) (hn : n+3 < 2^256) : 0+(3-1) ≤ (hp n hn).len r .dyn := by rw [len]; omega
private def bad (n : Nat) (hn : n+3 < 2^256) := captureOverwrite (hp n hn) r .dyn r .dyn 1 3 0 (hu n hn) (he n hn)

/-- Three writes each materially change the array: true,false,false ->
true,true,false -> true,false,false -> false,false,false (plus runtime tail). -/
theorem three_meaningful (n : Nat) (hn : n+3 < 2^256) :
    runCaptures (hp n hn) r .dyn [first] = some (mid n hn) ∧
    runCaptures (hp n hn) r .dyn cycle = some (hp n hn) ∧
    runCaptures (hp n hn) r .dyn [first,repair,repair] = some (bad n hn) ∧
    MObj.elems .dyn ((bad n hn).get r) = [false,false,false] ++ List.replicate n false ∧
    MObj.elems .dyn ((bad n hn).get neighbor) = [false,true] ∧
    mid n hn ≠ hp n hn ∧ hp n hn ≠ mid n hn ∧ bad n hn ≠ hp n hn := by
  have hc : runCaptures (hp n hn) r .dyn cycle = some (hp n hn) := by
    simpa only [restoreCycles,List.append_nil] using primitive_cycles n 1 hn
  have hb : runCaptures (hp n hn) r .dyn [first,repair,repair] = some (bad n hn) := by
    change runCaptures (hp n hn) r .dyn (cycle++[repair]) = _
    rw [runCaptures_append,hc,Option.bind_some,runCaptures_singleton]
    exact checkedCaptureOverwrite_some _ _ _ _ _ _ _ _ (hu n hn) (he n hn)
  have hm : mid n hn ≠ hp n hn := by
    intro h
    have hf := (primitive_intermediate n hn).2.2.1
    rw [h] at hf
    exact hf (initial n hn)
  have hv : MObj.elems .dyn ((bad n hn).get r) = [false,false,false] ++ List.replicate n false := by
    dsimp only [bad,captureOverwrite]
    rw [overwriteSlice_elems]; simp only [sliceElems,MObj.elems_dyn]; rfl
  refine ⟨(primitive_intermediate n hn).1,hc,hb,hv,?_,hm,Ne.symm hm,?_⟩
  · dsimp only [bad,captureOverwrite]
    rw [overwriteSlice_frame _ r neighbor .dyn 0 _ _ (by decide)]
    simp only [MObj.elems_dyn]; rfl
  · intro h
    have hx := congrArg (fun o : MObj H B => (MObj.elems .dyn o)[0]?) (congrArg (fun h : Heap H => h.get r) h)
    dsimp only at hx
    rw [hv] at hx
    simp only [MObj.elems_dyn] at hx
    exact (by decide : (some false : Option Bool) ≠ some true) hx

/-- Reversing the two restoring calls executes successfully but gives a
complete wrong vector, rather than the initial represented child. -/
theorem reversed_negative (n : Nat) (hn : n+3 < 2^256) :
    ∃ out, runCaptures (hp n hn) r .dyn [repair,first] = some out ∧
      MObj.elems .dyn (out.get r) = [false,false,false] ++ List.replicate n false ∧
      MObj.elems .dyn (out.get neighbor) = [false,true] ∧ out ≠ hp n hn := by
  let out := captureTwice (hp n hn) r .dyn 1 3 0 (hu n hn) (he n hn) 0 1 1 (hs n hn) (hd n hn)
  have ho : runCaptures (hp n hn) r .dyn [repair,first] = some out := by
    rw [runCaptures_two]
    exact captureTwice_checked _ _ _ _ _ _ (hu n hn) (he n hn) _ _ _ (hs n hn) (hd n hn)
  have hv : MObj.elems .dyn (out.get r) = [false,false,false] ++ List.replicate n false := by
    simp only [out,captureTwice,captureOverwrite,sliceElems,overwriteSlice_elems,MObj.elems_dyn]
    rfl
  refine ⟨out,ho,hv,?_,?_⟩
  · rw [runCaptures_frame _ _ _ _ _ ho neighbor (by decide)]
    simp only [MObj.elems_dyn]; rfl
  · intro h
    have hx := congrArg (fun h : Heap H => (MObj.elems .dyn (h.get r))[0]?) h
    dsimp only at hx
    rw [hv] at hx
    simp only [MObj.elems_dyn] at hx
    exact (by decide : (some false : Option Bool) ≠ some true) hx

/-- The initial second source is NOT the recaptured source; complete frozen
negative vector is inherited from the checked two-step instance. -/
theorem frozen_negative (n : Nat) (hn : n+3 < 2^256) :
    runCaptures (hp n hn) r .dyn cycle = some (hp n hn) ∧
    sliceElems (hp n hn) r .dyn 1 3 = [false,false] ∧
    captureOrigin cycle 0 = 0 ∧
    (MObj.elems .dyn ((hp n hn).get r))[captureOrigin cycle 0]? = some true ∧
    (MObj.elems .dyn ((hp n hn).get r))[snapshotOrigin repair 0]? = some false := by
  refine ⟨?_,(RecaptureControls.payloads n hn).2.2.2,rfl,?_,?_⟩
  · simpa only [restoreCycles,List.append_nil] using primitive_cycles n 1 hn
  all_goals simp only [MObj.elems_dyn]; rfl

/-- A successful three-step prefix reaches a real changed heap. Its invalid
next destination stops before the supplied suffix; no suffix heap is claimed. -/
theorem invalid_later (n : Nat) (hn : n+3 < 2^256) :
    runCaptures (hp n hn) r .dyn [first,repair,repair] = some (bad n hn) ∧
    checkedCaptureOverwrite (bad n hn) r .dyn r .dyn 0 1 (n+3) = none ∧
    runCaptures (hp n hn) r .dyn ([first,repair,repair]++(0,1,n+3)::cycle) = none := by
  have hpref := (three_meaningful n hn).2.2.1
  have hf : checkedCaptureOverwrite (bad n hn) r .dyn r .dyn 0 1 (n+3) = none := by
    apply (checkedCaptureOverwrite_none_iff _ _ _ _ _ _ _ _).mpr
    apply Or.inr; apply Or.inr
    rw [runCaptures_all_len _ _ _ _ _ hpref r .dyn,len]
    omega
  refine ⟨hpref,hf,?_⟩
  exact (runCaptures_none_first _ _ _ _).mpr ⟨[first,repair,repair],(0,1,n+3),cycle,bad n hn,rfl,hpref,hf⟩

/-- Empty schedule, singleton actual call, and empty exact-end source/target. -/
theorem endpoints (n : Nat) (hn : n+3 < 2^256) :
    runCaptures (hp n hn) r .dyn [] = some (hp n hn) ∧
    runCaptures (hp n hn) r .dyn [first] = some (mid n hn) ∧
    runCaptures (hp n hn) r .dyn [(n+3,n+3,n+3)] = some (hp n hn) := by
  refine ⟨rfl,(primitive_intermediate n hn).1,?_⟩
  rw [runCaptures_singleton]
  exact checkedCaptureOverwrite_empty _ _ _ _ _ _ _ (by rw [len]; exact Nat.le_refl _) (by rw [len]; exact Nat.le_refl _)

theorem touching (n : Nat) (hn : n+3 < 2^256) :
    ∃ out, runCaptures (hp n hn) r .dyn [first,(0,1,2)] = some out ∧
      MObj.elems .dyn (out.get r) = [true,true,true] ++ List.replicate n false ∧
      MObj.elems .dyn (out.get neighbor) = [false,true] := by
  have hd2 : 2+(1-0) ≤ (hp n hn).len r .dyn := by rw [len]; omega
  let out := captureTwice (hp n hn) r .dyn 0 1 1 (hs n hn) (hd n hn) 0 1 2 (hs n hn) hd2
  have ho : runCaptures (hp n hn) r .dyn [first,(0,1,2)] = some out := by
    rw [runCaptures_two]
    exact captureTwice_checked _ _ _ _ _ _ (hs n hn) (hd n hn) _ _ _ (hs n hn) hd2
  refine ⟨out,ho,?_,?_⟩
  · simp only [out,captureTwice,captureOverwrite,sliceElems,overwriteSlice_elems,MObj.elems_dyn]
    rfl
  · rw [runCaptures_frame _ _ _ _ _ ho neighbor (by decide)]
    simp only [MObj.elems_dyn]; rfl

/-- Recover the COMPLETE frozen-initial-source negative as an instance beside
this schedule's actual restoring result. No second frozen executor is defined. -/
theorem frozen_full (n : Nat) (hn : n+3 < 2^256) :
    ∃ (h1 : 1+(sliceElems (hp n hn) r .dyn 0 1).length ≤ (hp n hn).len r .dyn)
      (h2 : 0+(sliceElems (hp n hn) r .dyn 1 3).length ≤ (hp n hn).len r .dyn),
      let frozen := overwriteIntervals (hp n hn) r .dyn 1 (sliceElems (hp n hn) r .dyn 0 1) h1 0 (sliceElems (hp n hn) r .dyn 1 3) h2
      runCaptures (hp n hn) r .dyn cycle = some (hp n hn) ∧
      MObj.elems .dyn (frozen.get r) = [false,false,false] ++ List.replicate n false ∧ frozen ≠ hp n hn := by
  obtain ⟨h1,h2,hv,hne⟩ := RecaptureControls.frozen_negative n hn
  have he := (RecaptureControls.actual_restore n hn).2.2.2.1
  rw [he] at hne
  refine ⟨h1,h2,?_,hv,hne⟩
  simpa only [restoreCycles,List.append_nil] using primitive_cycles n 1 hn

/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.touching' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms touching
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.frozen_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frozen_full
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.three_meaningful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms three_meaningful
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.reversed_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reversed_negative
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.frozen_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frozen_negative
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.invalid_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms invalid_later
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms endpoints
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.cycle_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cycle_valid
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.cycles_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cycles_valid
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.cycles_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cycles_length
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.cycle_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cycle_origin
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.primitive_provenance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms primitive_provenance
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.primitive_cycles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_cycles
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.primitive_intermediate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_intermediate
/-- info: 'Solidity.Backend.MemoryOps.ScheduleControls.primitive_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms primitive_final
end Solidity.Backend.MemoryOps.ScheduleControls
