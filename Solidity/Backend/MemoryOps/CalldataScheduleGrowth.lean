import Solidity.Backend.MemoryOps.CalldataScheduleControls
import Solidity.Backend.MemoryOps.SnapshotScheduleGrowth

/-! Concrete context applications of the decoded-initialized finite schedule.
Initial Keeps is independent; actual Heap.alloc corollaries discharge it. No
fresh Source object or deep-child liveness follows from fresh own-field frames. -/
namespace Solidity.Backend.MemoryOps

theorem checkedBoolCaptures_keeps {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {values : Fin len → Source.Data D .bool} (hc : DecodedArrayAt c off len hn values)
    {H H' : HTy} {R : RefTy} {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp') (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedBoolCaptures c off hp r a s t d xs = some out) :
    ∃ out', checkedBoolCaptures c off hp' (r.wk e) a s t d xs = some out' ∧ Heap.Keeps e out out' := by
  obtain ⟨mid,hfirst,htail⟩ := (checkedBoolCaptures_some c off hp r a s t d xs out).mp ho
  obtain ⟨mid',hfirst',hk1⟩ := checkedCalldataBools_keeps hc e hk r a s t d mid hfirst
  obtain ⟨out',htail',hk2⟩ := runCaptures_keeps e hk1 r a xs out htail
  exact ⟨out',(checkedBoolCaptures_some c off hp' (r.wk e) a s t d xs out').mpr ⟨mid',hfirst',htail'⟩,hk2⟩

theorem checkedBoolCaptures_none_keeps {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {values : Fin len → Source.Data D .bool} (hc : DecodedArrayAt c off len hn values)
    {H H' : HTy} {R : RefTy} {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp') (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) (xs : List SnapshotArgs) :
    checkedBoolCaptures c off hp' (r.wk e) a s t d xs = none ↔
      checkedBoolCaptures c off hp r a s t d xs = none := by
  cases hf : checkedCalldataBools c off hp r a s t d with
  | none =>
    have hf' := (boolTransfer_none_keeps c off e hk r a s t d).mpr hf
    simp only [checkedBoolCaptures,hf,hf',Option.bind_none]
  | some mid =>
    obtain ⟨mid',hf',hk1⟩ := checkedCalldataBools_keeps hc e hk r a s t d mid hf
    simp only [checkedBoolCaptures,hf,hf',Option.bind_some]
    exact runCaptures_none_keeps e hk1 r a xs

/-- Actual allocation occurs AFTER the real decoded transfer, whose contents
may have broken the old child relation. The finite tail reads that changed mid. -/
theorem checkedBoolCaptures_interstage_alloc {D : Source.Layout} {H : HTy} {R A : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp out : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) (xs : List SnapshotArgs)
    (ho : checkedBoolCaptures c off hp r a s t d xs = some out) (obj : MObj H A) :
    let e := List.prefix_append H [A]
    ∃ mid out', checkedCalldataBools c off hp r a s t d = some mid ∧
      runCaptures (mid.alloc obj).1 (r.wk e) a xs = some out' ∧ Heap.Keeps e out out' ∧
      out'.get (mid.alloc obj).2 = (mid.alloc obj).1.get (mid.alloc obj).2 := by
  dsimp only
  obtain ⟨mid,hfirst,htail⟩ := (checkedBoolCaptures_some c off hp r a s t d xs out).mp ho
  obtain ⟨out',htail',hk,hfresh⟩ := runCaptures_alloc mid obj r a xs out htail
  exact ⟨mid,out',hfirst,htail',hk,hfresh⟩

namespace DecodedScheduleGrowthControls
open SequenceFixtures ScheduleControls
private abbrev B := BoolChildRef
private abbrev C : RefTy := .array (.ref B)
private abbrev H : HTy := [B,B]
private def r : HRef H B := ⟨0,rfl⟩
private def neighbor : HRef H B := ⟨1,rfl⟩
private def old (n : Nat) := [true,false,false]++List.replicate n false
private def hp (n : Nat) (hn : n+3 < 2^256) : Heap H :=
  (⟨old n,by simp only [old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,⟨[false,true],by decide⟩,())
private def obj : MObj H C := ⟨[r,r],by decide⟩
private def e := List.prefix_append H [C]

/-- Real decoded initialization, actual allocation on its broken output and
arbitrary recapture tail; fresh parent keeps aliases while child changes. -/
theorem interstage (n copies : Nat) (hn : n+3 < 2^256) :
    ∃ mid out, checkedCalldataBools (bools [true]) 7 (hp n hn) r .dyn 0 1 1 = some mid ∧
      MObj.elems .dyn (mid.get r) = [true,true,false]++List.replicate n false ∧
      ¬ BoolChildRepr (bools (old n)) (fun _ => 7) mid (.val (.cdRef rfl 7)) r ∧
      runCaptures (mid.alloc obj).1 (r.wk e) .dyn (repair::restoreCycles copies) = some out ∧
      MObj.elems .dyn (out.get (r.wk e)) = old n ∧
      MObj.elems .dyn (out.get (neighbor.wk e)) = [false,true] ∧
      (MObj.elems .dyn (out.get (mid.alloc obj).2)).map HRef.id = [0,0] ∧
      (r.wk e).id ≠ (mid.alloc obj).2.id := by
  have ho : checkedBoolCaptures (bools [true]) 7 (hp n hn) r .dyn 0 1 1
      (repair::restoreCycles copies) = some (hp n hn) := CalldataScheduleControls.runtime_run n copies hn
  obtain ⟨mid,out,hfirst,htail,hk,hfresh⟩ := checkedBoolCaptures_interstage_alloc
    (bools [true]) 7 (hp n hn) (hp n hn) r .dyn 0 1 1 _ ho obj
  have hi := CalldataScheduleControls.decoded_first n hn
  have he := Option.some.inj (hfirst.symm.trans hi)
  have hm := (CalldataScheduleControls.intermediate n hn).2.1
  have hbad := (CalldataScheduleControls.intermediate n hn).2.2.1
  rw [← he] at hm hbad
  refine ⟨mid,out,hfirst,hm,hbad,htail,?_,?_,?_,old_ne_fresh mid obj r⟩
  · rw [hk r,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]
    rfl
  · rw [hk neighbor,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]
    rfl
  · rw [hfresh,Heap.get_alloc,MObj.elems_wk,List.map_map]
    simp only [MObj.elems_dyn]; rfl

/-- Direct positive application of the new decoded-composition Keeps law to
an ACTUAL initial allocation, with fresh own-field frame and full old vectors. -/
theorem initial_allocated (n copies : Nat) (hn : n+3 < 2^256) :
    ∃ out, checkedBoolCaptures (bools [true]) 7 ((hp n hn).alloc obj).1 (r.wk e) .dyn 0 1 1
        (repair::restoreCycles copies) = some out ∧ Heap.Keeps e (hp n hn) out ∧
      MObj.elems .dyn (out.get (r.wk e)) = old n ∧
      MObj.elems .dyn (out.get (neighbor.wk e)) = [false,true] ∧
      (MObj.elems .dyn (out.get ((hp n hn).alloc obj).2)).map HRef.id = [0,0] ∧
      (r.wk e).id ≠ ((hp n hn).alloc obj).2.id := by
  have ho : checkedBoolCaptures (bools [true]) 7 (hp n hn) r .dyn 0 1 1 _ = some (hp n hn) :=
    CalldataScheduleControls.runtime_run n copies hn
  obtain ⟨out,ho',hk⟩ := checkedBoolCaptures_keeps (bool_repr [true]) e (Heap.keeps_alloc (hp n hn) obj)
    r .dyn 0 1 1 _ (hp n hn) ho
  refine ⟨out,ho',hk,?_,?_,?_,old_ne_fresh (hp n hn) obj r⟩
  · rw [hk r,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [hk neighbor,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [checkedBoolCaptures_frame _ _ _ _ _ _ _ _ _ _ ho' ((hp n hn).alloc obj).2
      (old_ne_fresh (hp n hn) obj r),Heap.get_alloc,MObj.elems_wk,List.map_map]
    simp only [MObj.elems_dyn]; rfl

/-- Actual initial allocation preserves the complete ordered failure trace:
decoded Some, nonempty repair prefix Some, reached invalid call None, full None. -/
theorem rejected_alloc (n : Nat) (hn : n+3 < 2^256) :
    ∃ mid reached, checkedCalldataBools (bools [true]) 7 ((hp n hn).alloc obj).1 (r.wk e) .dyn 0 1 1 = some mid ∧
      runCaptures mid (r.wk e) .dyn [repair] = some reached ∧
      checkedCaptureOverwrite reached (r.wk e) .dyn (r.wk e) .dyn 0 1 (n+3) = none ∧
      checkedBoolCaptures (bools [true]) 7 ((hp n hn).alloc obj).1 (r.wk e) .dyn 0 1 1
        [repair,(0,1,n+3),first] = none := by
  have hfirst := (CalldataScheduleControls.late_failure n hn).1
  obtain ⟨mid,hfirst',hk1⟩ := checkedCalldataBools_keeps (bool_repr [true]) e
    (Heap.keeps_alloc (hp n hn) obj) r .dyn 0 1 1 _ hfirst
  obtain ⟨reached,hpre,hk2⟩ := runCaptures_keeps e hk1 r .dyn [repair] (hp n hn)
    (CalldataScheduleControls.late_failure n hn).2.1
  refine ⟨mid,reached,hfirst',hpre,?_,?_⟩
  · exact (checkedCaptureOverwrite_none_keeps e hk2 r .dyn r .dyn 0 1 (n+3)).mpr
      (CalldataScheduleControls.late_failure n hn).2.2.1
  · apply (checkedBoolCaptures_none_keeps (bool_repr [true]) e (Heap.keeps_alloc (hp n hn) obj) r .dyn 0 1 1 _).mpr
    exact (CalldataScheduleControls.late_failure n hn).2.2.2
end DecodedScheduleGrowthControls

/-- info: 'Solidity.Backend.MemoryOps.checkedBoolCaptures_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolCaptures_keeps
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolCaptures_none_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolCaptures_none_keeps
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolCaptures_interstage_alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolCaptures_interstage_alloc
/-- info: 'Solidity.Backend.MemoryOps.DecodedScheduleGrowthControls.interstage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms DecodedScheduleGrowthControls.interstage
/-- info: 'Solidity.Backend.MemoryOps.DecodedScheduleGrowthControls.initial_allocated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms DecodedScheduleGrowthControls.initial_allocated
/-- info: 'Solidity.Backend.MemoryOps.DecodedScheduleGrowthControls.rejected_alloc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms DecodedScheduleGrowthControls.rejected_alloc
end Solidity.Backend.MemoryOps
