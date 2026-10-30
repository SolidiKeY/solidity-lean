import Solidity.Backend.MemoryOps.CopyMirrorFrame

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
end Solidity.Backend.MemoryOps.CopyMirrorControls
