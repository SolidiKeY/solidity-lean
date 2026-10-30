import Solidity.Backend.MemoryOps.BuilderComposition
import Solidity.Backend.MemoryOps.CopyMirrorSchedule

/-! Two real builder generations: nonzero published structs and arbitrary-length
nested fixed/dynamic arrays. Boundaries are element indices, not byte encoding. -/
namespace Solidity.Backend.MemoryOps.BuilderPairControls
private abbrev B : RefTy := .array (.prim .bool)
private abbrev A (n : Nat) : RefTy := .fixed (.ref B) n
private abbrev H : HTy := [B]
private def r : HRef H B := ⟨0,rfl⟩
private def hp : Heap H := (⟨true :: List.replicate 33 false, by decide⟩,())
private theorem hl : hp.len r .dyn = 34 := by
  simp only [Heap.len,MObj.elems_dyn,List.length_cons,List.length_replicate]; rfl
private theorem hs : SliceBounds (hp.len r .dyn) 0 1 := ⟨by decide,by rw [hl]; decide⟩
private theorem hd : 32+(1-0) ≤ hp.len r .dyn := by rw [hl]; decide
private def g1 {T : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true) := sv.copyStToM hp hm
private def mid {T : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true) :=
  captureAfterCopy hp sv hm r .dyn r .dyn 0 1 32 hs hd
private def old1 {T : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true) := r.wk (g1 sv hm).ext
private theorem ml {T : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true) :
    (mid sv hm).len (old1 sv hm) .dyn = 34 :=
  (captureAfterCopy_old_len hp sv hm r .dyn r .dyn 0 1 32 hs hd r .dyn).trans hl
private theorem bs {T : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true) :
    SliceBounds ((mid sv hm).len (old1 sv hm) .dyn) 32 33 := ⟨by decide,by rw [ml]; decide⟩
private theorem bd {T : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true) :
    33+(33-32) ≤ (mid sv hm).len (old1 sv hm) .dyn := by rw [ml]; decide
private def g2 {T U : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true)
    (v : SVal (.ref U)) (hv : (Ty.ref U).mapFree = true) := v.copyStToM (mid sv hm) hv
private def out {T U : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true)
    (v : SVal (.ref U)) (hv : (Ty.ref U).mapFree = true) :=
  captureAfterCopy (mid sv hm) v hv (old1 sv hm) .dyn (old1 sv hm) .dyn 32 33 33 (bs sv hm) (bd sv hm)
private def old2 {T U : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true)
    (v : SVal (.ref U)) (hv : (Ty.ref U).mapFree = true) := (old1 sv hm).wk (g2 sv hm v hv).ext
private theorem first_some {T : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true) :
    checkedCaptureOverwrite (g1 sv hm).heap (old1 sv hm) .dyn (old1 sv hm) .dyn 0 1 32 = some (mid sv hm) :=
  captureAfterCopy_checked hp sv hm r .dyn r .dyn 0 1 32 hs hd
private theorem second_some {T U : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true)
    (v : SVal (.ref U)) (hv : (Ty.ref U).mapFree = true) :
    checkedCaptureOverwrite (g2 sv hm v hv).heap (old2 sv hm v hv) .dyn (old2 sv hm v hv) .dyn 32 33 33 = some (out sv hm v hv) :=
  captureAfterCopy_checked (mid sv hm) v hv (old1 sv hm) .dyn (old1 sv hm) .dyn 32 33 33 (bs sv hm) (bd sv hm)
private theorem both {T U : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true)
    (v : SVal (.ref U)) (hv : (Ty.ref U).mapFree = true) :
    sv.Mirrors (out sv hm v hv) H.length ((g1 sv hm).val.wk (g2 sv hm v hv).ext) ∧
    v.Mirrors (out sv hm v hv) (g1 sv hm).H'.length (g2 sv hm v hv).val ∧
    ∀ {K : RefTy} (q : HRef (g1 sv hm).H' K),
      (q.wk (g2 sv hm v hv).ext).id ≠ (g2 sv hm v hv).val.id ∧
      (H.length ≤ q.id → (out sv hm v hv).get (q.wk (g2 sv hm v hv).ext) =
        MObj.wk (g2 sv hm v hv).ext K ((mid sv hm).get q)) :=
  two_builders_mirrors hp sv hm r .dyn r .dyn 0 1 32 hs hd v hv r .dyn r .dyn 32 33 33 (out sv hm v hv) (second_some sv hm v hv)
private theorem ol {T U : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true)
    (v : SVal (.ref U)) (hv : (Ty.ref U).mapFree = true) :
    (out sv hm v hv).len (old2 sv hm v hv) .dyn = 34 :=
  (captureAfterCopy_old_len (mid sv hm) v hv (old1 sv hm) .dyn (old1 sv hm) .dyn 32 33 33 (bs sv hm) (bd sv hm) (old1 sv hm) .dyn).trans (ml sv hm)

private def zero : PrimTy.uint.Denote := ⟨0,by decide⟩
private def thirtythree : PrimTy.uint.Denote := ⟨33,by decide⟩
private def child : SVal (.ref B) := .array (.cons (.prim true) .nil) .nil (by decide)
private def tree (n : Nat) : SVal (.ref (A n)) := .fixed (SVec.replicate child n)
private abbrev Per : RefTy := .struct "Person"
private def person : SVal (.ref Per) := .struct
  (.cons (.struct (.cons (.prim (uintOfNat 9))
    (.cons (.struct (.cons (.prim (uintOfNat 7)) .nil)) .nil)))
    (.cons (.prim (uintOfNat 11)) .nil))
private theorem pm : (Ty.ref Per).mapFree = true := by decide

private theorem head {K : HTy} (hp' : Heap K) (n k : Nat) (v : SVal (.ref B))
    (root : HRef K (A (k+1))) (h : (SVal.fixed (SVec.replicate v (k+1))).Mirrors hp' n root) :
    ∃ q : HRef K B, hp'.index root .fixed zero = some q ∧ v.Mirrors hp' n q := by
  have hh := h.2
  change ∃ w ws, MObj.elems .fixed (hp'.get root) = w :: ws ∧ v.Mirrors hp' n w ∧ _ at hh
  obtain ⟨q,qs,he,hq,_⟩ := hh
  refine ⟨q,?_,hq⟩
  change (MObj.elems .fixed (hp'.get root))[0]? = some q
  rw [he]; rfl
private theorem child_values {K : HTy} (hp' : Heap K) (n : Nat) (q : HRef K B)
    (h : child.Mirrors hp' n q) : MObj.elems .dyn (hp'.get q) = [true] := by
  obtain ⟨w,ws,he,hw,ht⟩ := h.2
  change w = true at hw
  change ws = [] at ht
  rw [hw,ht] at he
  exact he

private theorem old_read {T U : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true)
    (v : SVal (.ref U)) (hv : (Ty.ref U).mapFree = true) :
    (MObj.elems .dyn ((out sv hm v hv).get (old2 sv hm v hv)))[33]? = some true := by
  have h := copy_interstage_read_cases (g1 sv hm).heap (old1 sv hm) .dyn (old1 sv hm) .dyn
    0 1 32 (mid sv hm) (first_some sv hm) v hv (old1 sv hm) .dyn 32 33 33 (bs sv hm) (bd sv hm) 0 (by decide)
  change (MObj.elems .dyn ((out sv hm v hv).get (old2 sv hm v hv)))[33]? =
    ((MObj.elems .dyn ((g1 sv hm).heap.get (old1 sv hm)))[0]?).map (MVal.wk (g2 sv hm v hv).ext (.prim .bool)) at h
  have hi : (MObj.elems .dyn ((g1 sv hm).heap.get (old1 sv hm)))[0]? = some true := by
    rw [show (g1 sv hm).heap.get (old1 sv hm) = MObj.wk (g1 sv hm).ext B (hp.get r) from SVal.keeps_copyStToM sv hm hp r,
      MObj.elems_wk]
    simp only [MObj.elems_dyn]; rfl
  rw [hi] at h
  exact h

/-- Actual default growth after a nonzero struct copy preserves BOTH trees;
explicit final Person/Account/Token field observations follow separately. -/
theorem person_then_default (n : Nat) :
    checkedCaptureOverwrite (g1 person pm).heap (old1 person pm) .dyn (old1 person pm) .dyn 0 1 32 = some (mid person pm) ∧
    checkedCaptureOverwrite (g2 person pm (SVal.dflt (.ref (A n))) rfl).heap
      (old2 person pm (SVal.dflt (.ref (A n))) rfl) .dyn (old2 person pm (SVal.dflt (.ref (A n))) rfl) .dyn 32 33 33 =
      some (out person pm (SVal.dflt (.ref (A n))) rfl) ∧
    person.Mirrors (out person pm (SVal.dflt (.ref (A n))) rfl) H.length
      ((g1 person pm).val.wk (g2 person pm (SVal.dflt (.ref (A n))) rfl).ext) ∧
    (SVal.dflt (.ref (A n))).Mirrors (out person pm (SVal.dflt (.ref (A n))) rfl) (g1 person pm).H'.length
      (g2 person pm (SVal.dflt (.ref (A n))) rfl).val :=
  ⟨first_some person pm,second_some person pm _ rfl,(both person pm (SVal.dflt (.ref (A n))) rfl).1,(both person pm (SVal.dflt (.ref (A n))) rfl).2.1⟩

/-- Explicit final field observations, rather than only the mirror proposition. -/
theorem person_fields (n : Nat) :
    let v := SVal.dflt (.ref (A n))
    let final := out person pm v rfl
    let root := HRef.wk (g2 person pm v rfl).ext (g1 person pm).val
    final.field root (f := "age") rfl = uintOfNat 11 ∧
    final.field (final.field root (f := "account") rfl) (f := "balance") rfl = uintOfNat 9 ∧
    final.field (final.field (final.field root (f := "account") rfl) (f := "token") rfl) (f := "value") rfl = uintOfNat 7 := by
  dsimp only
  have h := (both person pm (SVal.dflt (.ref (A n))) rfl).1
  simp only [person,SVal.Mirrors,SFields.Mirrors] at h
  exact ⟨h.2.2.1,h.2.1.2.1,h.2.1.2.2.1.2.1⟩

/-- A final default child retains empty contents and is distinct from an actual
observed earlier Account child; the earlier final field retains its old ID. -/
theorem default_child (n : Nat) :
    let v := SVal.dflt (.ref (A (n+1)))
    let first := g1 person pm
    let later := g2 person pm v rfl
    let final := out person pm v rfl
    let account := first.heap.field first.val (f := "account") rfl
    ∃ q : HRef later.H' B,
      final.index later.val .fixed zero = some q ∧
      final.field (HRef.wk later.ext first.val) (f := "account") rfl = account.wk later.ext ∧
      MObj.elems .dyn (final.get q) = [] ∧ (account.wk later.ext).id ≠ q.id := by
  dsimp only
  let v := SVal.dflt (.ref (A (n+1)))
  let first := g1 person pm
  let later := g2 person pm v rfl
  let final := out person pm v rfl
  let account := first.heap.field first.val (f := "account") rfl
  have hh := both person pm v rfl
  have hdef : (SVal.dflt (.ref (A (n+1)))).Mirrors final first.H'.length later.val := hh.2.1
  rw [SVal.dflt_fixed] at hdef
  obtain ⟨q,hiq,hq⟩ := head final first.H'.length n (SVal.dflt (.ref B)) later.val hdef
  have fr := (hh.2.2 first.val).2 (SVal.copyStToM_id_ge hp person pm)
  rw [show (mid person pm).get first.val = first.heap.get first.val from
    (captureAfterCopy_fresh hp person pm r .dyn r .dyn 0 1 32 hs hd).2.2] at fr
  refine ⟨q,hiq,?_,?_,generations_mirror_ne later.ext account (SVal.dflt (.ref B)) q hq⟩
  · exact congrArg (fun o : MObj later.H' Per => o.1) fr
  · rw [SVal.dflt_array] at hq
    exact hq.2

/-- Same-type roots and observed Boolean children are separated across real
builder generations; no pairwise disjointness within a generation is assumed. -/
theorem array_generations (n : Nat) :
    let sv := tree (n+1)
    let first := g1 sv rfl
    let later := g2 sv rfl sv rfl
    let final := out sv rfl sv rfl
    ∃ q : HRef first.H' B, ∃ q' : HRef later.H' B,
      (mid sv rfl).index first.val .fixed zero = some q ∧
      final.index (first.val.wk later.ext) .fixed zero = some (q.wk later.ext) ∧
      final.index later.val .fixed zero = some q' ∧
      (first.val.wk later.ext).id ≠ later.val.id ∧ (q.wk later.ext).id ≠ q'.id ∧
      MObj.elems .dyn (final.get (q.wk later.ext)) = [true] ∧
      MObj.elems .dyn (final.get q') = [true] := by
  dsimp only
  let sv := tree (n+1)
  let first := g1 sv rfl
  let later := g2 sv rfl sv rfl
  let final := out sv rfl sv rfl
  have h1 := captureAfterCopy_mirrors hp sv rfl r .dyn r .dyn 0 1 32 hs hd
  obtain ⟨q,hq,hv⟩ := head (mid sv rfl) H.length n child first.val h1
  have hh := both sv rfl sv rfl
  obtain ⟨q',hq',hv'⟩ := head final first.H'.length n child later.val hh.2.1
  have qb : H.length ≤ q.id := SVal.Mirrors.id_ge child q hv
  have fr := (hh.2.2 first.val).2 (SVal.copyStToM_id_ge hp sv rfl)
  have fq := (hh.2.2 q).2 qb
  refine ⟨q,q',hq,?_,hq',(hh.2.2 first.val).1,generations_mirror_ne later.ext q child q' hv',?_,child_values final _ q' hv'⟩
  · change (MObj.elems .fixed (final.get (first.val.wk later.ext)))[0]? = _
    dsimp only [MVal.wk]
    rw [show final.get (HRef.wk later.ext first.val) = MObj.wk later.ext (A (n+1)) ((mid sv rfl).get first.val) from fr,MObj.elems_wk,List.getElem?_map]
    change ((MObj.elems .fixed ((mid sv rfl).get first.val))[0]?).map (HRef.wk later.ext) = _
    rw [show (MObj.elems .fixed ((mid sv rfl).get first.val))[0]? = some q from hq]
    rfl
  · rw [fq,MObj.elems_wk,child_values (mid sv rfl) _ q hv]
    rfl

/-- Complete ordered checked results and both final recursive mirrors, with
original alias identity retained across both actual prefix extensions. -/
theorem array_checked (n : Nat) :
    let sv := tree n
    let first := g1 sv rfl
    let later := g2 sv rfl sv rfl
    checkedCaptureOverwrite first.heap (old1 sv rfl) .dyn (old1 sv rfl) .dyn 0 1 32 = some (mid sv rfl) ∧
    checkedCaptureOverwrite later.heap (old2 sv rfl sv rfl) .dyn (old2 sv rfl sv rfl) .dyn 32 33 33 = some (out sv rfl sv rfl) ∧
    sv.Mirrors (out sv rfl sv rfl) H.length (HRef.wk later.ext first.val) ∧
    sv.Mirrors (out sv rfl sv rfl) first.H'.length later.val ∧
    (old2 sv rfl sv rfl).id = r.id := by
  dsimp only
  exact ⟨first_some _ rfl,second_some _ rfl _ rfl,(both (tree n) rfl (tree n) rfl).1,
    (both (tree n) rfl (tree n) rfl).2.1,rfl⟩

/-- Actual recapture crosses the 32-element boundary and changes the old alias;
the original snapshot's index32 was false. This is not a physical byte claim. -/
theorem recapture_boundary (n : Nat) :
    (out (tree n) rfl (tree n) rfl).index (old2 (tree n) rfl (tree n) rfl) .dyn thirtythree = some true ∧
    (MObj.elems .dyn (hp.get r))[32]? = some false := by
  exact ⟨old_read _ rfl _ rfl,by simp only [MObj.elems_dyn]; rfl⟩

/-- Empty builder payloads and exact-end empty snapshots remain actual values. -/
theorem empty_end :
    (tree 0).Mirrors (out (tree 0) rfl (tree 0) rfl) H.length
      ((g1 (tree 0) rfl).val.wk (g2 (tree 0) rfl (tree 0) rfl).ext) ∧
    checkedCaptureOverwrite (out (tree 0) rfl (tree 0) rfl) (old2 (tree 0) rfl (tree 0) rfl) .dyn
      (old2 (tree 0) rfl (tree 0) rfl) .dyn 34 34 34 = some (out (tree 0) rfl (tree 0) rfl) := by
  refine ⟨(both (tree 0) rfl (tree 0) rfl).1,?_⟩
  apply checkedCaptureOverwrite_empty <;> rw [ol] <;> decide

/-- Reversed endpoints, source overrun and destination overrun are independent
second-stage Option failures after two real multi-object builders. -/
theorem isolated_failures (n : Nat) :
    let sv := tree (n+1)
    let later := g2 sv rfl sv rfl
    let old := old2 sv rfl sv rfl
    checkedCaptureOverwrite later.heap old .dyn old .dyn 33 32 0 = none ∧
    checkedCaptureOverwrite later.heap old .dyn old .dyn 34 35 0 = none ∧
    checkedCaptureOverwrite later.heap old .dyn old .dyn 0 2 33 = none := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  all_goals
    apply (two_builders_none_iff hp (tree (n+1)) rfl r .dyn r .dyn 0 1 32 hs hd (tree (n+1)) rfl r .dyn r .dyn _ _ _).mpr
    rw [hl]; decide

private theorem old_false {T U : RefTy} (sv : SVal (.ref T)) (hm : (Ty.ref T).mapFree = true)
    (v : SVal (.ref U)) (hv : (Ty.ref U).mapFree = true) :
    (MObj.elems .dyn ((out sv hm v hv).get (old2 sv hm v hv)))[1]? = some false := by
  have h1 := checkedCaptureOverwrite_read_cases (g1 sv hm).heap (old1 sv hm) .dyn (old1 sv hm) .dyn
    0 1 32 (mid sv hm) (first_some sv hm) 1
  change (MObj.elems .dyn ((mid sv hm).get (old1 sv hm)))[1]? =
    (MObj.elems .dyn ((g1 sv hm).heap.get (old1 sv hm)))[1]? at h1
  have hi : (MObj.elems .dyn ((g1 sv hm).heap.get (old1 sv hm)))[1]? = some false := by
    rw [show (g1 sv hm).heap.get (old1 sv hm) = MObj.wk (g1 sv hm).ext B (hp.get r) from SVal.keeps_copyStToM sv hm hp r,MObj.elems_wk]
    simp only [MObj.elems_dyn]; rfl
  have h2 := checkedCaptureOverwrite_read_cases (g2 sv hm v hv).heap (old2 sv hm v hv) .dyn (old2 sv hm v hv) .dyn
    32 33 33 (out sv hm v hv) (second_some sv hm v hv) 1
  change (MObj.elems .dyn ((out sv hm v hv).get (old2 sv hm v hv)))[1]? =
    (MObj.elems .dyn ((g2 sv hm v hv).heap.get (old2 sv hm v hv)))[1]? at h2
  rw [show (g2 sv hm v hv).heap.get (old2 sv hm v hv) = MObj.wk (g2 sv hm v hv).ext B ((mid sv hm).get (old1 sv hm)) from
    SVal.keeps_copyStToM v hv (mid sv hm) (old1 sv hm),MObj.elems_wk] at h2
  change (MObj.elems .dyn ((out sv hm v hv).get (old2 sv hm v hv)))[1]? =
    ((MObj.elems .dyn ((mid sv hm).get (old1 sv hm))).map (fun b : Bool => b))[1]? at h2
  rw [List.map_id'] at h2
  exact h2.trans (h1.trans hi)

/-- An actual permitted write INTO a copied child destroys the later recursive
mirror although its parent field still selects the same child. This operation
is outside the old-original-destination frame, not an excluded source shape. -/
theorem descendant_mutation_negative (n : Nat) :
    let sv := tree (n+1)
    let later := g2 sv rfl sv rfl
    let final := out sv rfl sv rfl
    let old := old2 sv rfl sv rfl
    ∃ (q : HRef later.H' B) (bad : Heap later.H'),
      final.index later.val .fixed zero = some q ∧
      checkedCaptureOverwrite final old .dyn q .dyn 1 2 0 = some bad ∧
      bad.index later.val .fixed zero = some q ∧ bad.index q .dyn zero = some false ∧
      ¬ sv.Mirrors bad (g1 sv rfl).H'.length later.val := by
  dsimp only
  let sv := tree (n+1)
  let later := g2 sv rfl sv rfl
  let final := out sv rfl sv rfl
  let old := old2 sv rfl sv rfl
  obtain ⟨q,hiq,hq⟩ := head final (g1 sv rfl).H'.length n child later.val (both sv rfl sv rfl).2.1
  have vals := child_values final _ q hq
  have hb : SliceBounds (final.len old .dyn) 1 2 := ⟨by decide,by rw [ol]; decide⟩
  have hc : 0+(2-1) ≤ final.len q .dyn := by
    change 0+(2-1) ≤ (MObj.elems .dyn (final.get q)).length
    rw [vals]; exact Nat.le_refl 1
  let bad := captureOverwrite final old .dyn q .dyn 1 2 0 hb hc
  have hsbad := checkedCaptureOverwrite_some final old .dyn q .dyn 1 2 0 hb hc
  have rootframe : bad.get later.val = final.get later.val :=
    checkedCaptureOverwrite_frame final old .dyn q .dyn 1 2 0 bad hsbad later.val
      (boolChild_parent_ne later.val .fixed q).symm
  have rootindex : bad.index later.val .fixed zero = some q := by
    change (MObj.elems .fixed (bad.get later.val))[0]? = _
    rw [rootframe]; exact hiq
  have badread : bad.index q .dyn zero = some false := by
    have hr := checkedCaptureOverwrite_read final old .dyn q .dyn 1 2 0 0 bad hsbad (by decide)
    change (MObj.elems .dyn (bad.get q))[0]? = (MObj.elems .dyn (final.get old))[1]? at hr
    rw [old_false] at hr
    exact hr
  refine ⟨q,bad,hiq,hsbad,rootindex,badread,?_⟩
  intro wrong
  obtain ⟨z,hiz,hz⟩ := head bad (g1 sv rfl).H'.length n child later.val wrong
  have eqz : q = z := Option.some.inj (rootindex.symm.trans hiz)
  subst z
  have values := child_values bad _ q hz
  change (MObj.elems .dyn (bad.get q))[0]? = some false at badread
  rw [values] at badread
  cases badread

/-- Both real generations and existing element32 recapture are executed as
schedules, with an arbitrary runtime exact-end tail. Both recursive mirrors,
including nonzero structs and all nested default children, are derived anew. -/
theorem scheduled_person_default (n copies : Nat) :
    let v := SVal.dflt (.ref (A n))
    let later := g2 person pm v rfl
    let final := out person pm v rfl
    runCaptures (g1 person pm).heap (old1 person pm) .dyn [(0,1,32)]=some (mid person pm) ∧
    runCaptures later.heap (old2 person pm v rfl) .dyn ((32,33,33)::List.replicate copies (34,34,34))=some final ∧
    person.Mirrors final H.length ((g1 person pm).val.wk later.ext) ∧
    v.Mirrors final (g1 person pm).H'.length later.val := by
  dsimp only
  have hfirst : runCaptures (g1 person pm).heap (old1 person pm) .dyn [(0,1,32)]=some (mid person pm) := by
    rw [runCaptures_singleton]; exact first_some person pm
  have htail : runCaptures (g2 person pm (SVal.dflt (.ref (A n))) rfl).heap
      (old2 person pm (SVal.dflt (.ref (A n))) rfl) .dyn
      ((32,33,33)::List.replicate copies (34,34,34))=some (out person pm (SVal.dflt (.ref (A n))) rfl) := by
    rw [runCaptures,second_some,Option.bind_some]
    exact runCaptures_end_replicate _ _ .dyn 34 copies (ol person pm _ rfl)
  have hh := two_builder_schedules_mirrors hp person pm r .dyn [(0,1,32)] (mid person pm) hfirst
    (SVal.dflt (.ref (A n))) rfl _ _ htail
  exact ⟨hfirst,htail,hh⟩

/-- info: 'Solidity.Backend.MemoryOps.BuilderPairControls.person_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms person_fields
/-- info: 'Solidity.Backend.MemoryOps.BuilderPairControls.default_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms default_child
/-- info: 'Solidity.Backend.MemoryOps.BuilderPairControls.descendant_mutation_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms descendant_mutation_negative
/-- info: 'Solidity.Backend.MemoryOps.BuilderPairControls.person_then_default' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms person_then_default
/-- info: 'Solidity.Backend.MemoryOps.BuilderPairControls.array_generations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms array_generations
/-- info: 'Solidity.Backend.MemoryOps.BuilderPairControls.array_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms array_checked
/-- info: 'Solidity.Backend.MemoryOps.BuilderPairControls.recapture_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms recapture_boundary
/-- info: 'Solidity.Backend.MemoryOps.BuilderPairControls.empty_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_end
/-- info: 'Solidity.Backend.MemoryOps.BuilderPairControls.isolated_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms isolated_failures
/-- info: 'Solidity.Backend.MemoryOps.BuilderPairControls.scheduled_person_default' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scheduled_person_default
end Solidity.Backend.MemoryOps.BuilderPairControls
