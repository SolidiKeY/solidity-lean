import Solidity.Backend.MemoryOps.CalldataSchedule
import Solidity.Backend.MemoryOps.SnapshotScheduleControls

namespace Solidity.Backend.MemoryOps.CalldataScheduleControls
open SequenceFixtures ScheduleControls
private abbrev B := BoolChildRef
private abbrev H : HTy := [B,B]
private def r : HRef H B := ⟨0,rfl⟩
private def neighbor : HRef H B := ⟨1,rfl⟩
private def old (n : Nat) := [true,false,false] ++ List.replicate n false
private def hp (n : Nat) (hn : n+3 < 2^256) : Heap H :=
  (⟨old n,by simp only [old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,⟨[false,true],by decide⟩,())
private def mid (n : Nat) (hn : n+3 < 2^256) := captureOverwrite (hp n hn) r .dyn r .dyn 0 1 1
  (by constructor; decide; simp only [Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn,old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega)
  (by simp only [Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn,old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega)
private def sv : Source.Data D BoolChildTy := .val (.cdRef rfl 7)
private theorem initial (n : Nat) (hn : n+3 < 2^256) :
    BoolChildRepr (bools (old n)) (fun _ => 7) (hp n hn) sv r := by
  refine ⟨rfl,?_⟩
  simp only [MObj.elems_dyn]; rfl
private theorem hlen (n : Nat) (hn : n+3 < 2^256) : (hp n hn).len r .dyn = n+3 := by
  simp only [Heap.len,Heap.get,Objs.get,r,hp,MObj.elems_dyn,old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega

/-- The payload is eliminated from a real populated Source table. -/
theorem decoded_first (n : Nat) (hn : n+3 < 2^256) :
    checkedCalldataBools (bools [true]) 7 (hp n hn) r .dyn 0 1 1 = some (mid n hn) := by
  have h := checkedCalldataBools_some (bool_repr [true]) (hp n hn) r .dyn 0 1 1
    (⟨by decide,by decide⟩) (by rw [hlen]; omega)
  simpa only [mid,captureOverwrite,sliceElems,MObj.elems_dyn,Heap.get,Objs.get,hp,r,old,bool_values,List.drop_zero,List.take_succ_cons,List.take_zero] using h

/-- Complete reached values, old immutable relation false, actual repairing
call and unrelated neighbor: materially changed decoded initialization. -/
theorem intermediate (n : Nat) (hn : n+3 < 2^256) :
    MObj.elems .dyn ((hp n hn).get r) = old n ∧
    MObj.elems .dyn ((mid n hn).get r) = [true,true,false]++List.replicate n false ∧
    ¬ BoolChildRepr (bools (old n)) (fun _ => 7) (mid n hn) sv r ∧
    checkedCaptureOverwrite (mid n hn) r .dyn r .dyn 1 3 0 = some (hp n hn) ∧
    MObj.elems .dyn ((mid n hn).get neighbor) = [false,true] := by
  exact ⟨by simp only [MObj.elems_dyn]; rfl,(primitive_intermediate n hn).2.1,(primitive_intermediate n hn).2.2.1,
    (primitive_intermediate n hn).2.2.2.1,(primitive_intermediate n hn).2.2.2.2⟩

/-- Runtime schedule length is unrestricted. Recapture repairs the decoded
write and subsequent REAL restoring cycles each read their reached heap. -/
theorem runtime_run (n copies : Nat) (hn : n+3 < 2^256) :
    checkedBoolCaptures (bools [true]) 7 (hp n hn) r .dyn 0 1 1
      (repair :: restoreCycles copies) = some (hp n hn) := by
  unfold checkedBoolCaptures
  rw [decoded_first,Option.bind_some]
  change (checkedCaptureOverwrite (mid n hn) r .dyn r .dyn 1 3 0).bind _ = _
  rw [(intermediate n hn).2.2.2.1,Option.bind_some]
  exact primitive_cycles n copies hn

/-- Directly apply the general exact child criterion to actual decoded and
runtime-recaught contents; no desired output relation is an input. -/
theorem criterion_applied (n copies : Nat) (hn : n+3 < 2^256) :
    ∃ bs, calldataBools (bools [true]) 7 = some bs ∧
      ∀ k, (replaceSlice (MObj.elems .dyn ((hp n hn).get r)) 1 ((bs.drop 0).take (1-0)))[captureOrigin (repair::restoreCycles copies) k]? =
        (MObj.elems .dyn ((hp n hn).get r))[k]? := by
  refine ⟨[true],?_,?_⟩
  · rw [calldataBools_lookup (bool_repr [true]),bool_values]
  · have one : ∀ j, (replaceSlice (MObj.elems .dyn ((hp n hn).get r)) 1
        (([true].drop 0).take (1-0)))[snapshotOrigin repair j]? =
        (MObj.elems .dyn ((hp n hn).get r))[j]? := by
      intro j
      simp only [MObj.elems_dyn]
      change ([true,true,false]++List.replicate n false)[snapshotOrigin repair j]? =
        ([true,false,false]++List.replicate n false)[j]?
      cases j with
      | zero => rfl
      | succ j =>
        cases j with
        | zero => rfl
        | succ j =>
          have he : snapshotOrigin repair (j+1+1) = j+1+1 := by
            unfold snapshotOrigin repair
            dsimp only
            rw [if_neg (by omega)]
          rw [he]
          rfl
    intro k
    change (replaceSlice _ _ _)[snapshotOrigin repair (captureOrigin (restoreCycles copies) k)]? = _
    exact (one _).trans (primitive_provenance n copies hn k)

theorem final_observations (n copies : Nat) (hn : n+3 < 2^256) :
    ∃ out, checkedBoolCaptures (bools [true]) 7 (hp n hn) r .dyn 0 1 1
        (repair::restoreCycles copies) = some out ∧
      BoolChildRepr (bools (old n)) (fun _ => 7) out sv r ∧
      MObj.elems .dyn (out.get r) = old n ∧
      MObj.elems .dyn (out.get neighbor) = [false,true] ∧ r.id = 0 ∧ neighbor.id = 1 := by
  refine ⟨hp n hn,runtime_run n copies hn,?_,?_,?_,rfl,rfl⟩
  · exact (BoolChildRepr.calldata_schedule_iff (initial n hn) 7 0 1 1 _ _
      (runtime_run n copies hn)).mpr (criterion_applied n copies hn)
  · simp only [MObj.elems_dyn]; rfl
  · simp only [MObj.elems_dyn]; rfl

/-- A real successful decoded call and nonempty recapture prefix precede the
invalid schedule step. The suffix has no invented heap. -/
theorem late_failure (n : Nat) (hn : n+3 < 2^256) :
    checkedCalldataBools (bools [true]) 7 (hp n hn) r .dyn 0 1 1 = some (mid n hn) ∧
    runCaptures (mid n hn) r .dyn [repair] = some (hp n hn) ∧
    checkedCaptureOverwrite (hp n hn) r .dyn r .dyn 0 1 (n+3) = none ∧
    checkedBoolCaptures (bools [true]) 7 (hp n hn) r .dyn 0 1 1
      [repair,(0,1,n+3),first] = none := by
  have hb : checkedCaptureOverwrite (hp n hn) r .dyn r .dyn 0 1 (n+3) = none := by
    rw [checkedCaptureOverwrite_none_iff,hlen]
    omega
  refine ⟨decoded_first n hn,?_,hb,?_⟩
  · rw [runCaptures_singleton]; exact (intermediate n hn).2.2.2.1
  · unfold checkedBoolCaptures
    rw [decoded_first,Option.bind_some]
    change (checkedCaptureOverwrite (mid n hn) r .dyn r .dyn 1 3 0).bind _ = _
    rw [(intermediate n hn).2.2.2.1,Option.bind_some]
    change (checkedCaptureOverwrite (hp n hn) r .dyn r .dyn 0 1 (n+3)).bind _ = _
    rw [hb,Option.bind_none]

/-- Independent initial lookup, reversed source, source overrun and destination
overrun reject before any schedule operation. -/
theorem transfer_failures (n : Nat) (hn : n+3 < 2^256) (xs : List SnapshotArgs) :
    checkedBoolCaptures (bools [true]) 8 (hp n hn) r .dyn 0 1 1 xs = none ∧
    checkedBoolCaptures (bools [true]) 7 (hp n hn) r .dyn 1 0 0 xs = none ∧
    checkedBoolCaptures (bools [true]) 7 (hp n hn) r .dyn 0 2 0 xs = none ∧
    checkedBoolCaptures (bools [true]) 7 (hp n hn) r .dyn 0 1 (n+3) xs = none := by
  have h0 : checkedCalldataBools (bools [true]) 8 (hp n hn) r .dyn 0 1 1 = none := by rfl
  have h1 := (checkedCalldataBools_none_iff (bool_repr [true]) (hp n hn) r .dyn 1 0 0).mpr (Or.inl (by decide))
  have h2 := (checkedCalldataBools_none_iff (bool_repr [true]) (hp n hn) r .dyn 0 2 0).mpr (Or.inr (Or.inl (by decide)))
  have h3 := (checkedCalldataBools_none_iff (bool_repr [true]) (hp n hn) r .dyn 0 1 (n+3)).mpr
    (Or.inr (Or.inr (by rw [hlen]; omega)))
  simp only [checkedBoolCaptures,h0,h1,h2,h3,Option.bind_none,and_self]

/-- Empty decoded interval and empty/exact-end schedule are actual successes. -/
theorem endpoints (n : Nat) (hn : n+3 < 2^256) :
    checkedBoolCaptures (bools []) 7 (hp n hn) r .dyn 0 0 (n+3) [] = some (hp n hn) ∧
    checkedBoolCaptures (bools []) 7 (hp n hn) r .dyn 0 0 (n+3)
      [(n+3,n+3,n+3)] = some (hp n hn) := by
  have hi : checkedCalldataBools (bools []) 7 (hp n hn) r .dyn 0 0 (n+3) = some (hp n hn) := by
    have h := checkedCalldataBools_some (bool_repr []) (hp n hn) r .dyn 0 0 (n+3)
      ⟨by decide,by decide⟩ (by rw [hlen]; omega)
    simpa only [bool_values,List.drop_nil,List.take_nil,overwriteSlice_empty] using h
  have he : checkedCaptureOverwrite (hp n hn) r .dyn r .dyn (n+3) (n+3) (n+3) = some (hp n hn) := by
    have h := checkedCaptureOverwrite_some (hp n hn) r .dyn r .dyn (n+3) (n+3) (n+3)
      ⟨Nat.le_refl _,by rw [hlen]; exact Nat.le_refl _⟩ (by rw [hlen]; omega)
    simpa only [captureOverwrite,sliceElems,Nat.sub_self,List.take_zero,overwriteSlice_empty] using h
  simp only [checkedBoolCaptures,hi,Option.bind_some,runCaptures,he,and_self]

/-- Apply the new full read law at remapped and exterior indices, including
all runtime indices, rather than only invoking earlier schedule controls. -/
theorem all_reads (n copies : Nat) (hn : n+3 < 2^256) :
    ∃ bs, calldataBools (bools [true]) 7 = some bs ∧
      ∀ k, (MObj.elems .dyn ((hp n hn).get r))[k]? =
        (replaceSlice (MObj.elems .dyn ((hp n hn).get r)) 1 ((bs.drop 0).take (1-0)))[captureOrigin (repair::restoreCycles copies) k]? :=
  checkedBoolCaptures_read (bools [true]) 7 (hp n hn) r .dyn 0 1 1 _ _ (runtime_run n copies hn)

/-- Ignoring the repair is a successful operation with a complete WRONG
vector, false old correspondence and false exact INITIAL restoration criterion. -/
theorem no_repair_negative (n : Nat) (hn : n+3 < 2^256) :
    checkedBoolCaptures (bools [true]) 7 (hp n hn) r .dyn 0 1 1 [] = some (mid n hn) ∧
    MObj.elems .dyn ((mid n hn).get r) = [true,true,false]++List.replicate n false ∧
    MObj.elems .dyn ((mid n hn).get neighbor) = [false,true] ∧
    ¬ BoolChildRepr (bools (old n)) (fun _ => 7) (mid n hn) sv r ∧
    ¬ (∃ bs, calldataBools (bools [true]) 7 = some bs ∧
      ∀ k, (replaceSlice (MObj.elems .dyn ((hp n hn).get r)) 1 ((bs.drop 0).take (1-0)))[captureOrigin [] k]? = (MObj.elems .dyn ((hp n hn).get r))[k]?) := by
  have ho : checkedBoolCaptures (bools [true]) 7 (hp n hn) r .dyn 0 1 1 [] = some (mid n hn) := by
    unfold checkedBoolCaptures
    rw [decoded_first,Option.bind_some]
    rfl
  refine ⟨ho,(intermediate n hn).2.1,(intermediate n hn).2.2.2.2,(intermediate n hn).2.2.1,?_⟩
  intro ha
  have he := (checkedBoolCaptures_restore (bools [true]) 7 (hp n hn) r .dyn 0 1 1 [] _ ho).mpr ha
  have hf := (intermediate n hn).2.2.1
  rw [he] at hf
  exact hf (initial n hn)

/-- Replacing the actual changed source with a frozen INITIAL payload gives
false,false,false, whereas the real recapture repairs true,false,false. -/
theorem frozen_negative (n : Nat) (hn : n+3 < 2^256) :
    ∃ frozen : Heap H, MObj.elems .dyn (frozen.get r) = [false,false,false]++List.replicate n false ∧
      MObj.elems .dyn (frozen.get neighbor) = [false,true] ∧
      frozen ≠ hp n hn ∧
      checkedBoolCaptures (bools [true]) 7 (hp n hn) r .dyn 0 1 1 [repair] = some (hp n hn) := by
  let frozen := overwriteSlice (mid n hn) r .dyn 0 [false,false]
    (by rw [boolTransfer_all_len (bools [true]) 7 (hp n hn) r .dyn 0 1 1 (mid n hn) (decoded_first n hn) r .dyn]; rw [hlen]; change 0+2 ≤ n+3; omega)
  have hv : MObj.elems .dyn (frozen.get r) = [false,false,false]++List.replicate n false := by
    dsimp only [frozen]
    rw [overwriteSlice_elems,(intermediate n hn).2.1]
    rfl
  refine ⟨frozen,hv,?_,?_,?_⟩
  · dsimp only [frozen]
    rw [overwriteSlice_frame _ r neighbor .dyn 0 _ _ (by decide)]
    exact (intermediate n hn).2.2.2.2
  · intro he
    have he' := congrArg (fun h : Heap H => (MObj.elems .dyn (h.get r))[0]?) he
    dsimp only at he'
    rw [hv] at he'
    simp only [MObj.elems_dyn] at he'
    change (some false : Option Bool) = some true at he'
    cases he'
  · exact runtime_run n 0 hn

/-- A provenance-remapped final interior read is the exact immutable-table
read, not a caller-supplied converted value. -/
theorem actual_source_read (n : Nat) (hn : n+3 < 2^256) :
    ∃ b, (MObj.elems .dyn ((hp n hn).get r))[0]? = some b ∧
      DecodedArrayRead (bools [true]) 7 .bool none 0 (.val (.bool b)) :=
  checkedBoolCaptures_source_read (bools [true]) 7 (hp n hn) r .dyn 0 1 1
    (bool_repr [true]) [repair] (hp n hn) (runtime_run n 0 hn) 0 (by decide)

/-- Runtime element32 remains an element observation, not a physical byte
encoding claim. Existing primitive/reference boundary fixtures stay intact. -/
theorem boundary33 :
    checkedBoolCaptures (bools [true]) 7 (hp 33 (by decide)) r .dyn 0 1 1
      (repair::restoreCycles 4) = some (hp 33 (by decide)) ∧
    (MObj.elems .dyn ((hp 33 (by decide)).get r))[0]? = some true ∧
    (MObj.elems .dyn ((hp 33 (by decide)).get r))[32]? = some false := by
  refine ⟨runtime_run 33 4 (by decide),?_,?_⟩
  all_goals simp only [MObj.elems_dyn]; rfl

/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.decoded_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decoded_first
/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.intermediate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms intermediate
/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.runtime_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms runtime_run
/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.criterion_applied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms criterion_applied
/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.final_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms final_observations
/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.late_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms late_failure
/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.transfer_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms transfer_failures
/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.endpoints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms endpoints
/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.all_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms all_reads
/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.no_repair_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms no_repair_negative
/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.frozen_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms frozen_negative
/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.actual_source_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_source_read
/-- info: 'Solidity.Backend.MemoryOps.CalldataScheduleControls.boundary33' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms boundary33
end Solidity.Backend.MemoryOps.CalldataScheduleControls
