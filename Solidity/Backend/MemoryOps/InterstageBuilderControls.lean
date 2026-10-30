import Solidity.Backend.MemoryOps.InterstageBuilders

/-! Real three-object nested defaults and nonempty storage copies on the changed
first output. Old shallow snapshots and fresh construction are distinct. -/
namespace Solidity.Backend.MemoryOps.InterstageBuilderControls
private abbrev B : RefTy := .array (.prim .bool)
private abbrev P : RefTy := .fixed (.ref B) 2
private abbrev H : HTy := [B]
private def r : HRef H B := ⟨0, rfl⟩
private def hp : Heap H := (⟨[true, false, false, true, false, false], by decide⟩, ())
private theorem hs : SliceBounds (hp.len r .dyn) 0 2 := ⟨by decide, by simp only [Heap.len, MObj.elems_dyn]; decide⟩
private theorem hd : 2+(2-0) ≤ hp.len r .dyn := by simp only [Heap.len, MObj.elems_dyn]; decide
private def mid := captureOverwrite hp r .dyn r .dyn 0 2 2 hs hd
private theorem hf : checkedCaptureOverwrite hp r .dyn r .dyn 0 2 2 = some mid :=
  checkedCaptureOverwrite_some hp r .dyn r .dyn 0 2 2 hs hd
private theorem ml : mid.len r .dyn = 6 := by
  change (captureOverwrite hp r .dyn r .dyn 0 2 2 hs hd).len r .dyn = 6
  rw [captureOverwrite_all_len]; simp only [Heap.len, MObj.elems_dyn]; rfl
private theorem bs : SliceBounds (mid.len r .dyn) 2 4 := ⟨by decide, by rw [ml]; decide⟩
private theorem bd : 4+(4-2) ≤ mid.len r .dyn := by rw [ml]; decide
private def tree : SVal (.ref P) := .fixed
  (.cons (.array (.cons (.prim true) .nil) .nil (by decide))
    (.cons (.array (.cons (.prim false) .nil) .nil (by decide)) .nil))
private theorem default_value : SVal.dflt (.ref P) =
    .fixed (.cons (.array .nil .nil SVal.zero_lt_bound) (.cons (.array .nil .nil SVal.zero_lt_bound) .nil)) := by
  rw [SVal.dflt_fixed, SVal.dflt_array]
  rfl
private def dg := mid.allocDefault P rfl
private theorem dg_eq : dg =
    (SVal.fixed (.cons (.array .nil .nil SVal.zero_lt_bound)
      (.cons (.array .nil .nil SVal.zero_lt_bound) .nil))).copyStToM mid rfl := by
  unfold dg Heap.allocDefault
  rw [default_value]
private def cg := tree.copyStToM mid rfl
private theorem dg_type : dg.H' = [B,B,B,P] := by
  rw [dg_eq]; simp only [P, B, SVal.copyStToM_fixed, SVal.copyStToM_array, SVec.copyStToM_cons, SVec.copyStToM_nil, P, B, Grown.alloc, Heap.alloc, Objs.snoc, Objs.wk, MObj.wk, MVal.wk, HRef.wk]; rfl
private def dfirst : HRef dg.H' B := ⟨1, by rw [dg_type]; rfl⟩
private theorem cg_type : cg.H' = [B,B,B,P] := by
  simp only [cg, tree, SVal.copyStToM_fixed, SVal.copyStToM_array, SVal.copyStToM_prim, SVec.copyStToM_cons, SVec.copyStToM_nil, P, B, Grown.alloc, Heap.alloc, Objs.snoc, Objs.wk, MObj.wk, MVal.wk, HRef.wk]; rfl
private def cfirst : HRef cg.H' B := ⟨1, by rw [cg_type]; rfl⟩
private def csecond : HRef cg.H' B := ⟨2, by rw [cg_type]; rfl⟩
private def dout := captureAfterCopy mid (SVal.dflt (.ref P)) rfl r .dyn r .dyn 2 4 4 bs bd
private def cout := captureAfterCopy mid tree rfl r .dyn r .dyn 2 4 4 bs bd
private theorem mv : MObj.elems .dyn (mid.get r) = [true,false,true,false,false,false] := by
  simp only [mid, captureOverwrite, overwriteSlice_elems, sliceElems, MObj.elems_dyn]; rfl
private theorem values (v : SVal (.ref P)) :
    MObj.elems .dyn ((captureAfterCopy mid v rfl r .dyn r .dyn 2 4 4 bs bd).get (r.wk (v.copyStToM mid rfl).ext)) =
      [true,false,true,false,true,false] := by
  rw [captureAfterCopy_keeps mid v rfl r .dyn r .dyn 2 4 4 bs bd r, MObj.elems_wk]
  simp only [captureOverwrite, overwriteSlice_elems, sliceElems, mv]
  rfl

/-- Both actual builders add two children and a root between checked captures. -/
theorem actual_chains :
    checkedCaptureOverwrite hp r .dyn r .dyn 0 2 2 = some mid ∧
    dg.H' = [B,B,B,P] ∧ cg.H' = [B,B,B,P] ∧
    checkedCaptureOverwrite dg.heap (r.wk dg.ext) .dyn (r.wk dg.ext) .dyn 2 4 4 = some dout ∧
    checkedCaptureOverwrite cg.heap (r.wk cg.ext) .dyn (r.wk cg.ext) .dyn 2 4 4 = some cout ∧
    MObj.elems .dyn (dout.get (r.wk dg.ext)) = [true,false,true,false,true,false] ∧
    MObj.elems .dyn (cout.get (r.wk cg.ext)) = [true,false,true,false,true,false] :=
  ⟨hf,dg_type,cg_type,captureAfterCopy_checked mid _ rfl r .dyn r .dyn 2 4 4 bs bd,
    captureAfterCopy_checked mid tree rfl r .dyn r .dyn 2 4 4 bs bd,values _,values tree⟩

private def zero : PrimTy.uint.Denote := ⟨0, by decide⟩
private def four : PrimTy.uint.Denote := ⟨4, by decide⟩
/-- Actual typed reads distinguish changed recapture from the original payload. -/
theorem recapture : dout.index (r.wk dg.ext) .dyn four = some true ∧
    cout.index (r.wk cg.ext) .dyn four = some true ∧ hp.index r .dyn four = some false := by
  refine ⟨?_,?_,by simp only [Heap.index, MObj.elems_dyn]; rfl⟩
  · change (MObj.elems .dyn (dout.get (r.wk dg.ext)))[4]? = _
    rw [show MObj.elems .dyn (dout.get (r.wk dg.ext)) = _ from values (SVal.dflt (.ref P))]; rfl
  · change (MObj.elems .dyn (cout.get (r.wk cg.ext)))[4]? = _
    rw [show MObj.elems .dyn (cout.get (r.wk cg.ext)) = _ from values tree]; rfl

private def rootIDs (g : Grown H (MVal · (.ref P))) : List Nat :=
  (MObj.elems .fixed (g.heap.get g.val)).map HRef.id
private def rootChildValues (g : Grown H (MVal · (.ref P))) : Option (List Bool) :=
  (g.heap.index g.val .fixed zero).map (fun (q : HRef g.H' B) => MObj.elems (E := .prim .bool) .dyn (g.heap.get q))
private theorem default_ids : rootIDs dg = [1,2] := by
  rw [dg_eq]
  simp only [rootIDs, SVal.copyStToM_fixed, SVal.copyStToM_array, SVec.copyStToM_cons, SVec.copyStToM_nil, P, B, Grown.alloc, Heap.alloc, Heap.get, Objs.snoc, Objs.wk, MObj.wk, MVal.wk, HRef.wk, MObj.elems_fixed]; rfl
private theorem default_child : rootChildValues dg = some [] := by
  rw [dg_eq]
  simp only [rootChildValues, Heap.index, SVal.copyStToM_fixed, SVal.copyStToM_array, SVec.copyStToM_cons, SVec.copyStToM_nil, P, B, Grown.alloc, Heap.alloc, Heap.get, Objs.snoc, Objs.wk, MObj.wk, MVal.wk, HRef.wk, MObj.elems_dyn, MObj.elems_fixed]; rfl

/-- Fresh root fields keep the actual builder's new child IDs, not old aliases. -/
theorem fresh_roots : dg.val.id = 3 ∧ cg.val.id = 3 ∧
    (r.wk dg.ext).id = 0 ∧ (r.wk cg.ext).id = 0 ∧
    (r.wk dg.ext).id ≠ dg.val.id ∧ (r.wk cg.ext).id ≠ cg.val.id ∧
    dout.get dg.val = dg.heap.get dg.val ∧ cout.get cg.val = cg.heap.get cg.val ∧
    (MObj.elems .fixed (dout.get dg.val)).map HRef.id = [1,2] ∧
    (MObj.elems .fixed (cout.get cg.val)).map HRef.id = [1,2] := by
  have d := captureAfterCopy_fresh mid (SVal.dflt (.ref P)) rfl r .dyn r .dyn 2 4 4 bs bd
  have c := captureAfterCopy_fresh mid tree rfl r .dyn r .dyn 2 4 4 bs bd
  refine ⟨by rw [dg_eq]; simp only [P, B, SVal.copyStToM_fixed, SVal.copyStToM_array, SVec.copyStToM_cons, SVec.copyStToM_nil, P, B, Grown.alloc, Heap.alloc, Objs.snoc, Objs.wk, MObj.wk, MVal.wk, HRef.wk]; rfl,by simp only [cg, tree, SVal.copyStToM_fixed, SVal.copyStToM_array, SVal.copyStToM_prim, SVec.copyStToM_cons, SVec.copyStToM_nil, P, B, Grown.alloc, Heap.alloc, Objs.snoc, Objs.wk, MObj.wk, MVal.wk, HRef.wk]; rfl,rfl,rfl,d.2.1,c.2.1,d.2.2,c.2.2,?_,?_⟩
  · rw [show dout.get dg.val = dg.heap.get dg.val from d.2.2]
    exact default_ids
  · rw [show cout.get cg.val = cg.heap.get cg.val from c.2.2]; simp only [cg, tree, SVal.copyStToM_fixed, SVal.copyStToM_array, SVal.copyStToM_prim, SVec.copyStToM_cons, SVec.copyStToM_nil, P, B, Grown.alloc, Heap.alloc, Heap.get, Objs.snoc, Objs.wk, MObj.wk, MVal.wk, HRef.wk, MObj.elems_fixed]; rfl

/-- Defaults have empty dynamic children; the storage tree has real payloads. -/
theorem constructed_contents :
    (dout.index dg.val .fixed zero).map HRef.id = some 1 ∧
    cout.index cg.val .fixed zero = some cfirst ∧
    (dg.heap.index dg.val .fixed zero).map (fun (q : HRef dg.H' B) => MObj.elems (E := .prim .bool) .dyn (dg.heap.get q)) = some [] ∧
    MObj.elems .dyn (cg.heap.get cfirst) = [true] ∧
    MObj.elems .dyn (cg.heap.get csecond) = [false] := by
  refine ⟨?_,?_,default_child,?_,?_⟩
  · change ((MObj.elems .fixed (dout.get dg.val))[0]?).map HRef.id = _
    rw [fresh_roots.2.2.2.2.2.2.1]
    have he : (rootIDs dg)[0]? = some 1 := congrArg (fun xs : List Nat => xs[0]?) default_ids
    change ((MObj.elems .fixed (dg.heap.get dg.val)).map HRef.id)[0]? = some 1 at he
    rw [List.getElem?_map] at he
    exact he
  · change (MObj.elems .fixed (cout.get cg.val))[0]? = _
    rw [fresh_roots.2.2.2.2.2.2.2.1]
    simp only [cfirst, cg, tree, SVal.copyStToM_fixed, SVal.copyStToM_array, SVal.copyStToM_prim,
      SVec.copyStToM_cons, SVec.copyStToM_nil, P, B, Grown.alloc, Heap.alloc, Heap.get,
      Objs.snoc, Objs.wk, MObj.wk, MVal.wk, HRef.wk, MObj.elems_fixed]; rfl
  · simp only [cfirst, cg, tree, SVal.copyStToM_fixed, SVal.copyStToM_array, SVal.copyStToM_prim,
      SVec.copyStToM_cons, SVec.copyStToM_nil, P, B, Grown.alloc, Heap.alloc, Heap.get,
      Objs.snoc, Objs.wk, MObj.wk, MVal.wk, HRef.wk, MObj.elems_dyn]; rfl
  · simp only [csecond, cg, tree, SVal.copyStToM_fixed, SVal.copyStToM_array, SVal.copyStToM_prim,
      SVec.copyStToM_cons, SVec.copyStToM_nil, P, B, Grown.alloc, Heap.alloc, Heap.get,
      Objs.snoc, Objs.wk, MObj.wk, MVal.wk, HRef.wk, MObj.elems_dyn]; rfl

/-- Concrete fresh copied children keep their actual payloads at final output. -/
theorem final_child_contents :
    MObj.elems .dyn (cout.get cfirst) = [true] ∧
    MObj.elems .dyn (cout.get csecond) = [false] := by
  constructor
  · rw [show cout.get cfirst = cg.heap.get cfirst from
      captureAfterCopy_new_frame mid tree rfl r .dyn r .dyn 2 4 4 bs bd cfirst (by decide)]
    exact constructed_contents.2.2.2.1
  · rw [show cout.get csecond = cg.heap.get csecond from
      captureAfterCopy_new_frame mid tree rfl r .dyn r .dyn 2 4 4 bs bd csecond (by decide)]
    exact constructed_contents.2.2.2.2

/-- The generic checked-success and ordered-read theorems are concretely
instantiated with each real builder, not a supplied Keeps premise. -/
theorem success_transport :
    ∃ (d : Heap dg.H') (c : Heap cg.H'),
      checkedCaptureOverwrite hp r .dyn r .dyn 0 2 2 = some mid ∧
      checkedCaptureOverwrite dg.heap (r.wk dg.ext) .dyn (r.wk dg.ext) .dyn 2 4 4 = some d ∧
      checkedCaptureOverwrite cg.heap (r.wk cg.ext) .dyn (r.wk cg.ext) .dyn 2 4 4 = some c ∧
      Heap.Keeps dg.ext (captureOverwrite mid r .dyn r .dyn 2 4 4 bs bd) d ∧
      Heap.Keeps cg.ext (captureOverwrite mid r .dyn r .dyn 2 4 4 bs bd) c := by
  obtain ⟨d, hfirst, hd, hkd, _⟩ := copy_interstage_success hp r .dyn r .dyn 0 2 2 mid hf
    (SVal.dflt (.ref P)) rfl r .dyn r .dyn 2 4 4 bs bd
  obtain ⟨c, _, hc, hkc, _⟩ := copy_interstage_success hp r .dyn r .dyn 0 2 2 mid hf
    tree rfl r .dyn r .dyn 2 4 4 bs bd
  exact ⟨d,c,hfirst,hd,hc,hkd,hkc⟩

theorem ordered_read_laws :
    (MObj.elems .dyn (dout.get (r.wk dg.ext)))[4]? = some true ∧
    (MObj.elems .dyn (cout.get (r.wk cg.ext)))[4]? = some true := by
  constructor
  · simpa only [MObj.elems_dyn] using copy_interstage_read_cases hp r .dyn r .dyn 0 2 2 mid hf
      (SVal.dflt (.ref P)) rfl r .dyn 2 4 4 bs bd 0 (by decide)
  · simpa only [MObj.elems_dyn] using copy_interstage_read_cases hp r .dyn r .dyn 0 2 2 mid hf
      tree rfl r .dyn 2 4 4 bs bd 0 (by decide)

/-- Independent second-stage guards for both real multi-object builders. -/
theorem failures :
    checkedCaptureOverwrite dg.heap (r.wk dg.ext) .dyn (r.wk dg.ext) .dyn 3 1 0 = none ∧
    checkedCaptureOverwrite dg.heap (r.wk dg.ext) .dyn (r.wk dg.ext) .dyn 5 7 0 = none ∧
    checkedCaptureOverwrite dg.heap (r.wk dg.ext) .dyn (r.wk dg.ext) .dyn 0 2 5 = none ∧
    checkedCaptureOverwrite cg.heap (r.wk cg.ext) .dyn (r.wk cg.ext) .dyn 3 1 0 = none ∧
    checkedCaptureOverwrite cg.heap (r.wk cg.ext) .dyn (r.wk cg.ext) .dyn 5 7 0 = none ∧
    checkedCaptureOverwrite cg.heap (r.wk cg.ext) .dyn (r.wk cg.ext) .dyn 0 2 5 = none := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals
    apply (copy_interstage_none_iff mid _ rfl r .dyn r .dyn _ _ _).mpr
    rw [ml]
    decide

/-- Exact endpoint empty operations preserve each actual builder heap. -/
theorem empty_end :
    checkedCaptureOverwrite dg.heap (r.wk dg.ext) .dyn (r.wk dg.ext) .dyn 6 6 6 = some dg.heap ∧
    checkedCaptureOverwrite cg.heap (r.wk cg.ext) .dyn (r.wk cg.ext) .dyn 6 6 6 = some cg.heap := by
  constructor
  · apply checkedCaptureOverwrite_empty <;> rw [Heap.Keeps.len (SVal.keeps_copyStToM _ rfl mid) r .dyn,ml] <;> decide
  · apply checkedCaptureOverwrite_empty <;> change 6 ≤ cg.heap.len (r.wk cg.ext) .dyn
    all_goals exact (show cg.heap.len (r.wk cg.ext) .dyn = 6 from Heap.Keeps.len (SVal.keeps_copyStToM tree rfl mid) r .dyn |>.trans ml).symm ▸ Nat.le_refl 6

/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderControls.actual_chains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_chains
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderControls.recapture' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recapture
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderControls.fresh_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fresh_roots
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderControls.constructed_contents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms constructed_contents
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderControls.final_child_contents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms final_child_contents
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderControls.success_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms success_transport
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderControls.ordered_read_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered_read_laws
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderControls.failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failures
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderControls.empty_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_end
end Solidity.Backend.MemoryOps.InterstageBuilderControls
