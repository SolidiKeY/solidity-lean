import Solidity.Backend.MemoryOps.SnapshotReferenceSchedules

/-! Operation-side finite-schedule growth, consuming published checked-step
Keeps. Initial prefix preservation is explicit and actual Heap.alloc discharges
it; fresh own fields are framed without claiming referenced-child liveness. -/
namespace Solidity.Backend.MemoryOps

theorem runCaptures_keeps {H H' : HTy} {R : RefTy} {E : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs) (out : Heap H)
    (ho : runCaptures hp r a xs = some out) :
    ∃ out', runCaptures hp' (r.wk e) a xs = some out' ∧ Heap.Keeps e out out' := by
  induction xs generalizing hp hp' with
  | nil =>
    have he := Option.some.inj ho
    subst out
    exact ⟨hp',rfl,hk⟩
  | cons x xs ih =>
    obtain ⟨mid,hf,ht⟩ := (runCaptures_cons_some hp out r a x xs).mp ho
    obtain ⟨mid',hf',hk1⟩ := checkedCaptureOverwrite_keeps e hk r a r a x.1 x.2.1 x.2.2 mid hf
    obtain ⟨out',ht',hk2⟩ := ih hk1 ht
    exact ⟨out',(runCaptures_cons_some hp' out' (r.wk e) a x xs).mpr ⟨mid',hf',ht'⟩,hk2⟩

/-- Rejection is identical through an initial preserving extension because
original runtime lengths, not supplied poststates, determine all bounds. -/
theorem runCaptures_none_keeps {H H' : HTy} {R : RefTy} {E : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs) :
    runCaptures hp' (r.wk e) a xs = none ↔ runCaptures hp r a xs = none := by
  rw [runCaptures_none_iff,runCaptures_none_iff,hk.len]

theorem runCaptures_alloc {H : HTy} {R A : RefTy} {E : Ty}
    (hp : Heap H) (obj : MObj H A) (r : HRef H R) (a : ArrTy R E)
    (xs : List SnapshotArgs) (out : Heap H) (ho : runCaptures hp r a xs = some out) :
    let e := List.prefix_append H [A]
    let g := hp.alloc obj
    ∃ out', runCaptures g.1 (r.wk e) a xs = some out' ∧ Heap.Keeps e out out' ∧
      out'.get g.2 = g.1.get g.2 := by
  dsimp only
  have hk : Heap.Keeps (List.prefix_append H [A]) hp (hp.alloc obj).1 := Heap.keeps_alloc hp obj
  obtain ⟨out',ho',hk'⟩ := runCaptures_keeps _ hk r a xs out ho
  exact ⟨out',ho',hk',runCaptures_frame _ _ _ _ _ ho' (hp.alloc obj).2 (old_ne_fresh hp obj r)⟩

/-- Allocation occurs after the ACTUAL successful prefix, then the remaining
arbitrary schedule recaptures each changed reached heap. Fresh fields frame;
no Source entry, constructor/compiler or deep-child preservation is assumed. -/
theorem runCaptures_interstage_alloc {H : HTy} {R A : RefTy} {E : Ty}
    (hp out : Heap H) (r : HRef H R) (a : ArrTy R E) (pre tail : List SnapshotArgs)
    (ho : runCaptures hp r a (pre++tail) = some out) (obj : MObj H A) :
    let e := List.prefix_append H [A]
    ∃ mid out', runCaptures hp r a pre = some mid ∧
      runCaptures (mid.alloc obj).1 (r.wk e) a tail = some out' ∧ Heap.Keeps e out out' ∧
      out'.get (mid.alloc obj).2 = (mid.alloc obj).1.get (mid.alloc obj).2 := by
  dsimp only
  obtain ⟨mid,hpre,htail⟩ := (runCaptures_split_some hp out r a pre tail).mp ho
  obtain ⟨out',ho',hk,hfresh⟩ := runCaptures_alloc mid obj r a tail out htail
  exact ⟨mid,out',hpre,ho',hk,hfresh⟩

namespace ScheduleGrowthControls
open ScheduleControls SequenceFixtures
private abbrev B := BoolChildRef
private abbrev C : RefTy := .array (.ref B)
private abbrev H : HTy := [B,B]
private def r : HRef H B := ⟨0,rfl⟩
private def neighbor : HRef H B := ⟨1,rfl⟩
private def old (n : Nat) := [true,false,false] ++ List.replicate n false
private def hp (n : Nat) (hn : n+3 < 2^256) : Heap H :=
  (⟨old n,by simp only [old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,⟨[false,true],by decide⟩,())
private theorem len (n : Nat) (hn : n+3 < 2^256) : (hp n hn).len r .dyn = n+3 := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,r,old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
private theorem hu (n : Nat) (hn : n+3 < 2^256) : SliceBounds ((hp n hn).len r .dyn) 1 3 := by rw [len]; exact ⟨by decide,by omega⟩
private theorem he (n : Nat) (hn : n+3 < 2^256) : 0+(3-1) ≤ (hp n hn).len r .dyn := by rw [len]; omega
private def bad (n : Nat) (hn : n+3 < 2^256) := captureOverwrite (hp n hn) r .dyn r .dyn 1 3 0 (hu n hn) (he n hn)
private def obj : MObj H C := ⟨[r,r],by decide⟩
private def e := List.prefix_append H [C]

/-- Actual allocation is between a meaningful first write and a runtime
finite tail of actual recaptures. New parent fields retain old aliases while child changes. -/
theorem interstage (n copies : Nat) (hn : n+3 < 2^256) :
    ∃ mid out, runCaptures (hp n hn) r .dyn [first] = some mid ∧
      MObj.elems .dyn (mid.get r) = [true,true,false] ++ List.replicate n false ∧
      ¬ BoolChildRepr (bools (old n)) (fun _ => 7) mid (.val (.cdRef rfl 7 0)) r ∧
      runCaptures (mid.alloc obj).1 (r.wk e) .dyn ([repair]++restoreCycles copies++[repair]) = some out ∧
      (r.wk e).id ≠ (mid.alloc obj).2.id ∧
      (MObj.elems .dyn (out.get (mid.alloc obj).2)).map HRef.id = [0,0] ∧
      MObj.elems .dyn (out.get (r.wk e)) = [false,false,false] ++ List.replicate n false ∧
      MObj.elems .dyn (out.get (neighbor.wk e)) = [false,true] ∧
      (bools (old n)).objects (7+(mid.alloc obj).2.id) = none := by
  have hc : runCaptures (hp n hn) r .dyn cycle = some (hp n hn) := by
    simpa only [restoreCycles,List.append_nil] using ScheduleControls.primitive_cycles n 1 hn
  have hcycles : runCaptures (hp n hn) r .dyn (restoreCycles copies) = some (hp n hn) := ScheduleControls.primitive_cycles n copies hn
  have ho : runCaptures (hp n hn) r .dyn ([first]++([repair]++restoreCycles copies++[repair])) = some (bad n hn) := by
    change runCaptures (hp n hn) r .dyn (cycle++(restoreCycles copies++[repair])) = _
    rw [runCaptures_append,hc,Option.bind_some,runCaptures_append,hcycles,Option.bind_some,runCaptures_singleton]
    exact checkedCaptureOverwrite_some _ _ _ _ _ _ _ _ (hu n hn) (he n hn)
  obtain ⟨mid,out,hpre,htail,hko,hfresh⟩ := runCaptures_interstage_alloc _ _ r .dyn [first] ([repair]++restoreCycles copies++[repair]) ho obj
  have hv : MObj.elems .dyn (mid.get r) = [true,true,false] ++ List.replicate n false := by
    have hf := (ScheduleControls.primitive_intermediate n hn).1
    have hid := Option.some.inj (hf.symm.trans hpre)
    rw [← hid]
    exact (ScheduleControls.primitive_intermediate n hn).2.1
  have hbroken : ¬ BoolChildRepr (bools (old n)) (fun _ => 7) mid (.val (.cdRef rfl 7 0)) r := by
    have hf := (ScheduleControls.primitive_intermediate n hn).1
    have hid := Option.some.inj (hf.symm.trans hpre)
    rw [← hid]
    exact (ScheduleControls.primitive_intermediate n hn).2.2.1
  refine ⟨mid,out,hpre,hv,hbroken,htail,old_ne_fresh mid obj r,?_,?_,?_,?_⟩
  · rw [hfresh,Heap.get_alloc,MObj.elems_wk,List.map_map]
    simp only [MObj.elems_dyn]; rfl
  · rw [hko r,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
    exact (ScheduleControls.three_meaningful n hn).2.2.2.1
  · rw [hko neighbor,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
    exact (ScheduleControls.three_meaningful n hn).2.2.2.2.1
  · change (bools (old n)).objects 9 = none
    rfl

/-- An actually allocated extension preserves a later invalid schedule result,
including a real successful three-write prefix before its bad step. -/
theorem allocated_failure (n : Nat) (hn : n+3 < 2^256) :
    ∃ reachedHeap, runCaptures ((hp n hn).alloc obj).1 (r.wk e) .dyn [first,repair,repair] = some reachedHeap ∧
      checkedCaptureOverwrite reachedHeap (r.wk e) .dyn (r.wk e) .dyn 0 1 (n+3) = none ∧
      runCaptures ((hp n hn).alloc obj).1 (r.wk e) .dyn ([first,repair,repair]++(0,1,n+3)::cycle) = none := by
  have hk : Heap.Keeps e (hp n hn) ((hp n hn).alloc obj).1 := Heap.keeps_alloc (hp n hn) obj
  have hpref : runCaptures (hp n hn) r .dyn [first,repair,repair] = some (bad n hn) := (ScheduleControls.three_meaningful n hn).2.2.1
  obtain ⟨reachedHeap,hprefix,hkp⟩ := runCaptures_keeps e hk r .dyn [first,repair,repair] (bad n hn) hpref
  have hf : checkedCaptureOverwrite (bad n hn) r .dyn r .dyn 0 1 (n+3) = none := (ScheduleControls.invalid_later n hn).2.1
  refine ⟨reachedHeap,hprefix,(checkedCaptureOverwrite_none_keeps e hkp r .dyn r .dyn 0 1 (n+3)).mpr hf,?_⟩
  exact (runCaptures_none_keeps e hk r .dyn _).mpr (ScheduleControls.invalid_later n hn).2.2

/-- info: 'Solidity.Backend.MemoryOps.ScheduleGrowthControls.interstage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms interstage
/-- info: 'Solidity.Backend.MemoryOps.ScheduleGrowthControls.allocated_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms allocated_failure
end ScheduleGrowthControls
namespace ScheduleReferenceGrowthControls
open ScheduleControls SequenceFixtures
private abbrev B := BoolChildRef
private abbrev C : RefTy := .array (.ref B)
private abbrev Q : RefTy := .array (.ref C)
private abbrev H : HTy := [B,B,C]
private def left : HRef H B := ⟨0,rfl⟩
private def right : HRef H B := ⟨1,rfl⟩
private def root : HRef H C := ⟨2,rfl⟩
private def hp (n : Nat) (hn : n+3 < 2^256) : Heap H :=
  (⟨[true,false],by decide⟩,⟨[false,true],by decide⟩,
   ⟨[left,right,right]++List.replicate n left,by simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,())
private def obj : MObj H Q := ⟨[root,root],by decide⟩
private def e := List.prefix_append H [Q]
private theorem hs (n : Nat) (hn : n+3 < 2^256) : SliceBounds ((hp n hn).len root .dyn) 0 1 := by
  constructor
  · decide
  · simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,root,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
private theorem hd (n : Nat) (hn : n+3 < 2^256) : 1+(1-0) ≤ (hp n hn).len root .dyn := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,root,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
private def mid (n : Nat) (hn : n+3 < 2^256) := captureOverwrite (hp n hn) root .dyn root .dyn 0 1 1 (hs n hn) (hd n hn)

/-- Nonprimitive weakening is exercised by actual allocated schedules: the
old reference array changes aliases in its real first output then recaptures. -/
theorem reference_allocated (n copies : Nat) (hn : n+3 < 2^256) :
    ∃ out firstOut,
      runCaptures ((hp n hn).alloc obj).1 (root.wk e) .dyn (restoreCycles copies) = some out ∧
      runCaptures ((hp n hn).alloc obj).1 (root.wk e) .dyn [first] = some firstOut ∧
      MObj.elems .dyn (out.get (root.wk e)) = [left.wk e,right.wk e,right.wk e]++List.replicate n (left.wk e) ∧
      MObj.elems .dyn (firstOut.get (root.wk e)) = [left.wk e,left.wk e,right.wk e]++List.replicate n (left.wk e) ∧
      (MObj.elems .dyn (out.get ((hp n hn).alloc obj).2)).map HRef.id = [2,2] ∧
      (MObj.elems .dyn (firstOut.get ((hp n hn).alloc obj).2)).map HRef.id = [2,2] ∧
      MObj.elems .dyn (out.get (left.wk e)) = [true,false] ∧
      MObj.elems .dyn (out.get (right.wk e)) = [false,true] ∧
      (copies = 1 → checkedCaptureOverwrite firstOut (root.wk e) .dyn (root.wk e) .dyn 1 3 0 = some out) := by
  have ho : runCaptures (hp n hn) root .dyn (restoreCycles copies) = some (hp n hn) := ReferenceScheduleControls.reference_cycles n copies hn
  have hf : runCaptures (hp n hn) root .dyn [first] = some (mid n hn) := (ReferenceScheduleControls.reference_intermediate n hn).1
  obtain ⟨out,ho',hko,hfresh⟩ := runCaptures_alloc (hp n hn) obj root .dyn _ (hp n hn) ho
  obtain ⟨firstOut,hf',hkf,hfreshf⟩ := runCaptures_alloc (hp n hn) obj root .dyn [first] (mid n hn) hf
  have hvfirst : MObj.elems .dyn ((mid n hn).get root) = [left,left,right]++List.replicate n left :=
    (ReferenceScheduleControls.reference_intermediate n hn).2.1
  refine ⟨out,firstOut,ho',hf',?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hko root,MObj.elems_wk]
    simp only [MObj.elems_dyn]
    change ([left,right,right]++List.replicate n left).map (MVal.wk e (.ref B)) = _
    simp only [List.map_append,List.map_cons,List.map_nil,List.map_replicate]; rfl
  · rw [hkf root,MObj.elems_wk,hvfirst]
    simp only [List.map_append,List.map_cons,List.map_nil,List.map_replicate]; rfl
  · rw [hfresh,Heap.get_alloc,MObj.elems_wk,List.map_map]
    simp only [MObj.elems_dyn]; rfl
  · rw [hfreshf,Heap.get_alloc,MObj.elems_wk,List.map_map]
    simp only [MObj.elems_dyn]; rfl
  · rw [hko left,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [hko right,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · intro hc
    subst copies
    have ht : runCaptures ((hp n hn).alloc obj).1 (root.wk e) .dyn cycle = some out := by
      simpa only [restoreCycles,List.append_nil] using ho'
    obtain ⟨actual,ha,hb⟩ := (runCaptures_cons_some _ _ _ _ first [repair]).mp ht
    rw [runCaptures_singleton] at hf'
    have heq := Option.some.inj (hf'.symm.trans ha)
    rw [← heq,runCaptures_singleton] at hb
    exact hb

/-- info: 'Solidity.Backend.MemoryOps.ScheduleReferenceGrowthControls.reference_allocated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_allocated
end ScheduleReferenceGrowthControls
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_keeps
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_none_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_none_keeps
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_alloc
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_interstage_alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_interstage_alloc
end Solidity.Backend.MemoryOps
