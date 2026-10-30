import Solidity.Backend.MemoryOps.CopyMirrorFrame
import Solidity.Backend.MemoryOps.CopyMirrorSchedule

/-! Arbitrary-length, nested published copies/defaults with actual first and
second operations, plus failure of an unframed old-object mirror. -/
namespace Solidity.Backend.MemoryOps.CopyMirrorControls
private abbrev B : RefTy := .array (.prim .bool)
private abbrev C : RefTy := .fixed (.ref B) 2
private abbrev A (n : Nat) : RefTy := .fixed (.ref C) n
private abbrev H : HTy := [B]
private def r : HRef H B := ⟨0,rfl⟩
private def hp : Heap H := (⟨[true,false,false,false], by decide⟩, ())
private theorem hs : SliceBounds (hp.len r .dyn) 0 1 :=
  ⟨by decide, by simp only [Heap.len,MObj.elems_dyn]; decide⟩
private theorem hd : 1+(1-0) ≤ hp.len r .dyn := by simp only [Heap.len,MObj.elems_dyn]; decide
private def mid := captureOverwrite hp r .dyn r .dyn 0 1 1 hs hd
private theorem first_some : checkedCaptureOverwrite hp r .dyn r .dyn 0 1 1 = some mid :=
  checkedCaptureOverwrite_some hp r .dyn r .dyn 0 1 1 hs hd
private theorem ml : mid.len r .dyn = 4 := by
  change (captureOverwrite hp r .dyn r .dyn 0 1 1 hs hd).len r .dyn = 4
  rw [captureOverwrite_all_len]; simp only [Heap.len,MObj.elems_dyn]; rfl
private theorem bs : SliceBounds (mid.len r .dyn) 1 2 := ⟨by decide, by rw [ml]; decide⟩
private theorem bd : 2+(2-1) ≤ mid.len r .dyn := by rw [ml]; decide
private def child : SVal (.ref B) := .array (.cons (.prim true) .nil) .nil (by decide)
private def tree (n : Nat) : SVal (.ref (A n)) :=
  .fixed (SVec.replicate (.fixed (SVec.replicate child 2)) n)
private def copied (n : Nat) := (tree n).copyStToM mid rfl
private def defaults (n : Nat) := mid.allocDefault (A n) rfl
private def out (n : Nat) := captureAfterCopy mid (tree n) rfl r .dyn r .dyn 1 2 2 bs bd
private def dout (n : Nat) := captureAfterCopy mid (SVal.dflt (.ref (A n))) rfl r .dyn r .dyn 1 2 2 bs bd

/-- No payload cap: the whole nested typed mirror is present at final output
for every runtime family size, including zero. All operations are actual. -/
theorem nested_copy (n : Nat) :
    checkedCaptureOverwrite hp r .dyn r .dyn 0 1 1 = some mid ∧
    checkedCaptureOverwrite (copied n).heap (r.wk (copied n).ext) .dyn
      (r.wk (copied n).ext) .dyn 1 2 2 = some (out n) ∧
    (tree n).Mirrors (out n) H.length (copied n).val :=
  ⟨first_some,captureAfterCopy_checked mid (tree n) rfl r .dyn r .dyn 1 2 2 bs bd,
    captureAfterCopy_mirrors mid (tree n) rfl r .dyn r .dyn 1 2 2 bs bd⟩

theorem nested_default (n : Nat) :
    checkedCaptureOverwrite hp r .dyn r .dyn 0 1 1 = some mid ∧
    checkedCaptureOverwrite (defaults n).heap (r.wk (defaults n).ext) .dyn
      (r.wk (defaults n).ext) .dyn 1 2 2 = some (dout n) ∧
    (SVal.dflt (.ref (A n))).Mirrors (dout n) H.length (defaults n).val :=
  ⟨first_some,captureAfterCopy_checked mid (SVal.dflt (.ref (A n))) rfl r .dyn r .dyn 1 2 2 bs bd,
    captureAfterDefault_mirrors mid rfl r .dyn r .dyn 1 2 2 bs bd⟩

/-- Copied recursive contents survive while the old destination really changes. -/
theorem old_recapture (n : Nat) :
    (MObj.elems .dyn (hp.get r))[2]? = some false ∧
    (MObj.elems .dyn ((out n).get (r.wk (copied n).ext)))[2]? = some true := by
  constructor
  · simp only [MObj.elems_dyn]; rfl
  · simpa only [MObj.elems_dyn] using copy_interstage_read_cases hp r .dyn r .dyn 0 1 1 mid first_some
      (tree n) rfl r .dyn 1 2 2 bs bd 0 (by decide)

private def originalElems : SVec (.prim .bool) 4 :=
  .cons (.prim true) (.cons (.prim false) (.cons (.prim false) (.cons (.prim false) .nil)))
private def original : SVal (.ref B) := .array originalElems .nil (by decide)
private theorem mv : MObj.elems .dyn (mid.get r) = [true,true,false,false] := by
  simp only [mid,captureOverwrite,overwriteSlice_elems,sliceElems,MObj.elems_dyn]; rfl
/-- An old mirror is inhabited, but the actual first write destroys it. The
fresh-ID frame cannot be dropped just because a relation held initially. -/
theorem old_mirror_negative : original.Mirrors hp 0 r ∧ ¬ original.Mirrors mid 0 r := by
  constructor
  · change 0 ≤ r.id ∧ originalElems.Mirrors hp 0 (MObj.elems .dyn (hp.get r))
    refine ⟨by decide,?e⟩
    simp only [originalElems,SVec.Mirrors,SVal.Mirrors,MObj.elems_dyn]
    exact ⟨true,[false,false,false],rfl,rfl,false,[false,false],rfl,rfl,false,[false],rfl,rfl,false,[],rfl,rfl,rfl⟩
  · intro h
    change 0 ≤ r.id ∧ originalElems.Mirrors mid 0 (MObj.elems .dyn (mid.get r)) at h
    have he := SVec.Mirrors.getElem originalElems _ h.2 1
    rcases he with he | ⟨v,w,hv,hw,hm⟩
    · have hh := he.1
      simp only [originalElems,SVec.toList_cons,SVec.toList_nil,List.getElem?_cons_succ,List.getElem?_cons_zero] at hh
      change some (SVal.prim false : SVal (.prim .bool)) = none at hh
      cases hh
    · simp only [originalElems,SVec.toList_cons,SVec.toList_nil,List.getElem?_cons_succ,List.getElem?_cons_zero] at hv
      change some (SVal.prim false : SVal (.prim .bool)) = some v at hv
      cases hv
      rw [mv] at hw
      change some true = some w at hw
      cases hw
      change true = false at hm
      cases hm

private abbrev Per : RefTy := .struct "Person"
private def person : SVal (.ref Per) := .struct
  (.cons (.struct (.cons (.prim (uintOfNat 9))
    (.cons (.struct (.cons (.prim (uintOfNat 7)) .nil)) .nil)))
    (.cons (.prim (uintOfNat 11)) .nil))
private theorem pm : (Ty.ref Per).mapFree = true := by decide
private def pg := person.copyStToM mid pm
private def pout := captureAfterCopy mid person pm r .dyn r .dyn 1 2 2 bs bd

/-- Published Person/Account/Token fields exercise the nonempty struct branch,
with nonzero contents and actual second output field observation. -/
theorem person_copy :
    checkedCaptureOverwrite hp r .dyn r .dyn 0 1 1 = some mid ∧
    checkedCaptureOverwrite pg.heap (r.wk pg.ext) .dyn (r.wk pg.ext) .dyn 1 2 2 = some pout ∧
    person.Mirrors pout H.length pg.val ∧
    pout.field pg.val (f := "age") rfl = uintOfNat 11 := by
  have hm : person.Mirrors pout H.length pg.val :=
    captureAfterCopy_mirrors mid person pm r .dyn r .dyn 1 2 2 bs bd
  refine ⟨first_some,captureAfterCopy_checked mid person pm r .dyn r .dyn 1 2 2 bs bd,hm,?_⟩
  simp only [person,SVal.Mirrors,SFields.Mirrors] at hm
  change (pout.get pg.val).2.1 = uintOfNat 11
  exact hm.2.2.1

theorem person_default :
    (SVal.dflt (.ref Per)).Mirrors
      (captureAfterCopy mid (SVal.dflt (.ref Per)) pm r .dyn r .dyn 1 2 2 bs bd)
      H.length (mid.allocDefault Per pm).val :=
  captureAfterDefault_mirrors mid pm r .dyn r .dyn 1 2 2 bs bd

private theorem cons_eq {α : Type} {a b : α} {xs ys : List α} (ha : a=b) (hs : xs=ys) : a::xs=b::ys := by
  cases ha; cases hs; rfl
private def tail (copies : Nat) : List SnapshotArgs := (1,2,2)::List.replicate copies (4,4,4)
private def changed := captureOverwrite mid r .dyn r .dyn 1 2 2 bs bd
private theorem tail_some (copies : Nat) : runCaptures mid r .dyn (tail copies)=some changed := by
  rw [tail,runCaptures,checkedCaptureOverwrite_some mid r .dyn r .dyn 1 2 2 bs bd,Option.bind_some]
  exact runCaptures_end_replicate changed r .dyn 4 copies (by change (captureOverwrite mid r .dyn r .dyn 1 2 2 bs bd).len r .dyn=4; rw [captureOverwrite_all_len,ml])
private theorem changed_values : MObj.elems .dyn (changed.get r)=[true,true,true,false] := by
  simp only [changed,captureOverwrite,overwriteSlice_elems,sliceElems,mv]
  rfl

/-- Real changed prefix then the published nested recursive builder and a
runtime tail of reached operations. Copy/default mirrors and complete old
vectors are derived; no final representation is supplied. -/
theorem nested_schedule (n copies : Nat) :
    ∃ final : Heap (copied n).H',
      checkedCaptureOverwrite hp r .dyn r .dyn 0 1 1=some mid ∧
      runCaptures (copied n).heap (r.wk (copied n).ext) .dyn (tail copies)=some final ∧
      Heap.Keeps (copied n).ext changed final ∧ (tree n).Mirrors final H.length (copied n).val ∧
      (copied n).val.id ≠ (r.wk (copied n).ext).id ∧
      final.get (copied n).val=(copied n).heap.get (copied n).val ∧
      [MObj.elems .dyn (hp.get r),MObj.elems .dyn (mid.get r),
        MObj.elems (H := (copied n).H') .dyn ((copied n).heap.get (r.wk (copied n).ext)),MObj.elems (H := (copied n).H') .dyn (final.get (r.wk (copied n).ext))]=
        [[true,false,false,false],[true,true,false,false],[true,true,false,false],[true,true,true,false]] := by
  obtain ⟨final,ho,hk,hm,hframe⟩ := copy_schedule_transport mid changed (tree n) rfl r .dyn (tail copies) (tail_some copies)
  refine ⟨final,first_some,ho,hk,hm,?_,hframe _ (SVal.copyStToM_id_ge mid (tree n) rfl),?_⟩
  · exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le r.id_lt (SVal.copyStToM_id_ge mid (tree n) rfl))).symm
  · have hcopy : (copied n).heap.get (r.wk (copied n).ext)=MObj.wk (copied n).ext B (mid.get r) := SVal.keeps_copyStToM (tree n) rfl mid r
    have hc : MObj.elems (H := (copied n).H') .dyn ((copied n).heap.get (r.wk (copied n).ext))=MObj.elems .dyn (mid.get r) := by
      rw [hcopy]
      exact (MObj.elems_wk (copied n).ext .dyn (mid.get r)).trans
        (List.map_id'' (f := MVal.wk (copied n).ext (.prim .bool)) (fun _ => rfl) _)
    have hf : MObj.elems (H := (copied n).H') .dyn (final.get (r.wk (copied n).ext))=MObj.elems .dyn (changed.get r) := by
      rw [hk r]
      exact (MObj.elems_wk (copied n).ext .dyn (changed.get r)).trans
        (List.map_id'' (f := MVal.wk (copied n).ext (.prim .bool)) (fun _ => rfl) _)
    exact cons_eq (show MObj.elems (H := H) .dyn (hp.get r)=[true,false,false,false] from by simp only [MObj.elems_dyn]; rfl)
      (cons_eq mv (cons_eq (hc.trans mv)
        (cons_eq (hf.trans changed_values) rfl)))

theorem default_schedule (n copies : Nat) :
    ∃ final : Heap (defaults n).H',
      runCaptures (defaults n).heap (r.wk (defaults n).ext) .dyn (tail copies)=some final ∧
      (SVal.dflt (.ref (A n))).Mirrors final H.length (defaults n).val ∧
      MObj.elems .dyn (final.get (r.wk (defaults n).ext))=[true,true,true,false] := by
  obtain ⟨final,ho,hk,hm,hframe⟩ := copy_schedule_transport mid changed (SVal.dflt (.ref (A n))) rfl r .dyn (tail copies) (tail_some copies)
  refine ⟨final,ho,default_schedule_mirrors mid rfl r .dyn (tail copies) final ho,?_⟩
  rw [hk r,MObj.elems_wk]
  simpa only [List.map_id'' (f := MVal.wk (defaults n).ext (.prim .bool)) (fun _ => rfl)] using changed_values

/-- All nonzero Person/Account/Token observations survive the runtime tail,
while the actual OLD destination changes. No descendant liveness is assumed. -/
theorem person_schedule (copies : Nat) :
    ∃ final : Heap pg.H', runCaptures pg.heap (r.wk pg.ext) .dyn (tail copies)=some final ∧
      person.Mirrors final H.length pg.val ∧
      final.field pg.val (f := "age") rfl=uintOfNat 11 ∧
      final.field (final.field pg.val (f := "account") rfl) (f := "balance") rfl=uintOfNat 9 ∧
      final.field (final.field (final.field pg.val (f := "account") rfl) (f := "token") rfl) (f := "value") rfl=uintOfNat 7 := by
  obtain ⟨final,ho,hk,hm,hframe⟩ := copy_schedule_transport mid changed person pm r .dyn (tail copies) (tail_some copies)
  refine ⟨final,ho,hm,?_⟩
  simp only [person,SVal.Mirrors,SFields.Mirrors] at hm
  exact ⟨hm.2.2.1,hm.2.1.2.1,hm.2.1.2.2.1.2.1⟩

/-- A real nonempty changed successful tail precedes an invalid call. The
recursive mirror holds at that reached prefix, with no fictitious suffix heap. -/
theorem late_failure (n copies : Nat) :
    ∃ final : Heap (copied n).H',
      runCaptures (copied n).heap (r.wk (copied n).ext) .dyn (tail copies)=some final ∧
      checkedCaptureOverwrite final (r.wk (copied n).ext) .dyn (r.wk (copied n).ext) .dyn 0 5 0=none ∧
      runCaptures (copied n).heap (r.wk (copied n).ext) .dyn (tail copies++[(0,5,0)])=none ∧
      (tree n).Mirrors final H.length (copied n).val := by
  obtain ⟨final,hfirst,ho,hk,hm,hne,hframe,hvectors⟩ := nested_schedule n copies
  have hl : final.len (r.wk (copied n).ext) .dyn=4 := by
    rw [hk.len]
    change (captureOverwrite mid r .dyn r .dyn 1 2 2 bs bd).len r .dyn=4
    rw [captureOverwrite_all_len,ml]
  have hf : checkedCaptureOverwrite final (r.wk (copied n).ext) .dyn (r.wk (copied n).ext) .dyn 0 5 0=none := by
    apply (checkedCaptureOverwrite_none_iff _ _ _ _ _ _ _ _).mpr
    rw [hl]; exact Or.inr (Or.inl (by decide))
  have hnone := (copy_schedule_none_first mid (tree n) rfl r .dyn (tail copies++[(0,5,0)])).mpr
    ⟨tail copies,(0,5,0),[],final,rfl,ho,hf,hm⟩
  exact ⟨final,ho,hf,hnone,hm⟩

/-- Two material post-builder calls recapture a changed source. All ordered
vectors and both actual Some calls distinguish the frozen-initial source. -/
theorem reached_changed_source (n : Nat) :
    ∃ first final : Heap (copied n).H',
      checkedCaptureOverwrite (copied n).heap (r.wk (copied n).ext) .dyn (r.wk (copied n).ext) .dyn 1 2 2=some first ∧
      checkedCaptureOverwrite first (r.wk (copied n).ext) .dyn (r.wk (copied n).ext) .dyn 2 3 3=some final ∧
      runCaptures (copied n).heap (r.wk (copied n).ext) .dyn [(1,2,2),(2,3,3)]=some final ∧
      (tree n).Mirrors final H.length (copied n).val ∧
      MObj.elems .dyn (first.get (r.wk (copied n).ext))=[true,true,true,false] ∧
      MObj.elems .dyn (final.get (r.wk (copied n).ext))=[true,true,true,true] ∧
      (MObj.elems .dyn ((copied n).heap.get (r.wk (copied n).ext)))[2]?=some false ∧
      (MObj.elems .dyn (final.get (r.wk (copied n).ext)))[3]? ≠
        (MObj.elems .dyn ((copied n).heap.get (r.wk (copied n).ext)))[2]? := by
  have hb : SliceBounds (changed.len r .dyn) 2 3 := ⟨by decide,by change 3 ≤ (captureOverwrite mid r .dyn r .dyn 1 2 2 bs bd).len r .dyn; rw [captureOverwrite_all_len,ml]; decide⟩
  have hd' : 3+(3-2) ≤ changed.len r .dyn := by change 3+(3-2) ≤ (captureOverwrite mid r .dyn r .dyn 1 2 2 bs bd).len r .dyn; rw [captureOverwrite_all_len,ml]; decide
  let last := captureOverwrite changed r .dyn r .dyn 2 3 3 hb hd'
  have hv : MObj.elems .dyn (last.get r)=[true,true,true,true] := by
    simp only [last,captureOverwrite,overwriteSlice_elems,sliceElems,changed_values]; rfl
  obtain ⟨first,hfirst,hk1⟩ := checkedCaptureOverwrite_keeps (copied n).ext (SVal.keeps_copyStToM (tree n) rfl mid)
    r .dyn r .dyn 1 2 2 changed (checkedCaptureOverwrite_some mid r .dyn r .dyn 1 2 2 bs bd)
  obtain ⟨final,hfinal,hk2⟩ := checkedCaptureOverwrite_keeps (copied n).ext hk1 r .dyn r .dyn 2 3 3 last
    (checkedCaptureOverwrite_some changed r .dyn r .dyn 2 3 3 hb hd')
  have ho : runCaptures (copied n).heap (r.wk (copied n).ext) .dyn [(1,2,2),(2,3,3)]=some final := by
    apply (runCaptures_cons_some _ _ _ .dyn (1,2,2) [(2,3,3)]).mpr
    refine ⟨first,hfirst,?_⟩
    rw [runCaptures_singleton]
    exact hfinal
  have hfv : MObj.elems .dyn (first.get (r.wk (copied n).ext))=[true,true,true,false] := by
    rw [hk1 r,MObj.elems_wk,List.map_id'' (f := MVal.wk (copied n).ext (.prim .bool)) (fun _ => rfl)]
    exact changed_values
  have hlv : MObj.elems .dyn (final.get (r.wk (copied n).ext))=[true,true,true,true] := by
    rw [hk2 r,MObj.elems_wk,List.map_id'' (f := MVal.wk (copied n).ext (.prim .bool)) (fun _ => rfl)]
    exact hv
  have hi : (MObj.elems .dyn ((copied n).heap.get (r.wk (copied n).ext)))[2]?=some false := by
    have hk : Heap.Keeps (copied n).ext mid (copied n).heap := SVal.keeps_copyStToM (tree n) rfl mid
    change (MObj.elems .dyn ((copied n).heap.get (r.wk (copied n).ext)))[2]?=some false
    rw [show (copied n).heap.get (r.wk (copied n).ext)=MObj.wk (copied n).ext B (mid.get r) from hk r,MObj.elems_wk,
      List.map_id'' (f := MVal.wk (copied n).ext (.prim .bool)) (fun _ => rfl),mv]
    rfl
  refine ⟨first,final,hfirst,hfinal,ho,copy_schedule_mirrors mid (tree n) rfl r .dyn _ final ho,hfv,hlv,hi,?_⟩
  rw [hlv,hi]
  change (some true : Option Bool) ≠ some false
  decide

/-- info: 'Solidity.Backend.MemoryOps.CopyMirrorControls.person_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms person_copy
/-- info: 'Solidity.Backend.MemoryOps.CopyMirrorControls.person_default' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms person_default
/-- info: 'Solidity.Backend.MemoryOps.CopyMirrorControls.nested_copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nested_copy
/-- info: 'Solidity.Backend.MemoryOps.CopyMirrorControls.nested_default' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nested_default
/-- info: 'Solidity.Backend.MemoryOps.CopyMirrorControls.old_recapture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms old_recapture
/-- info: 'Solidity.Backend.MemoryOps.CopyMirrorControls.old_mirror_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms old_mirror_negative
/-- info: 'Solidity.Backend.MemoryOps.CopyMirrorControls.reached_changed_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reached_changed_source
/-- info: 'Solidity.Backend.MemoryOps.CopyMirrorControls.nested_schedule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nested_schedule
/-- info: 'Solidity.Backend.MemoryOps.CopyMirrorControls.default_schedule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms default_schedule
/-- info: 'Solidity.Backend.MemoryOps.CopyMirrorControls.person_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms person_schedule
/-- info: 'Solidity.Backend.MemoryOps.CopyMirrorControls.late_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms late_failure
end Solidity.Backend.MemoryOps.CopyMirrorControls
