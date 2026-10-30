import Solidity.Backend.MemoryOps.InterstageBuilders
import Solidity.Backend.MemoryOps.CalldataChildControls
import Solidity.Backend.MemoryOps.CalldataNestedControls

/-! Existing immutable certificates across actual multi-object builders.
No new calldata tables or fresh Source representations are manufactured. -/
namespace Solidity.Backend.MemoryOps.InterstageBuilderChildControls
private abbrev A : RefTy := .fixed (.ref BoolChildRef) 2
private def tree : SVal (.ref A) := .fixed
  (.cons (.array (.cons (.prim true) .nil) .nil (by decide))
    (.cons (.array (.cons (.prim false) .nil) .nil (by decide)) .nil))
private def copyGrow {H : HTy} (mid : Heap H) := tree.copyStToM mid rfl
private def defaultGrow {H : HTy} (mid : Heap H) := mid.allocDefault A rfl

private theorem boolean_chain {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp s r) (parent : HRef H (.array (.ref BoolChildRef)))
    (hb : (MObj.elems .dyn (hp.get parent)).map HRef.id = [1,0,1]) :
    ∃ (mid : Heap H) (out : Heap (copyGrow mid).H'),
      checkedCaptureOverwrite hp parent .dyn parent .dyn 1 2 0 = some mid ∧
      checkedCaptureOverwrite (copyGrow mid).heap (parent.wk (copyGrow mid).ext) .dyn
        (parent.wk (copyGrow mid).ext) .dyn 2 3 1 = some out ∧
      BoolChildRepr c address out s (r.wk (copyGrow mid).ext) ∧
      (MObj.elems .dyn (mid.get parent)).map HRef.id = [0,0,1] ∧
      out.get (copyGrow mid).val = (copyGrow mid).heap.get (copyGrow mid).val := by
  have hn : hp.len parent .dyn = 3 := by
    have hl := congrArg List.length hb
    simpa only [List.length_map, List.length_cons, List.length_nil] using hl
  have hs : SliceBounds (hp.len parent .dyn) 1 2 := ⟨by decide, by rw [hn]; decide⟩
  have hd : 0+(2-1) ≤ hp.len parent .dyn := by rw [hn]; decide
  let mid := captureOverwrite hp parent .dyn parent .dyn 1 2 0 hs hd
  have hml : mid.len parent .dyn = 3 := by
    change (captureOverwrite hp parent .dyn parent .dyn 1 2 0 hs hd).len parent .dyn = 3
    rw [captureOverwrite_all_len, hn]
  have hs' : SliceBounds (mid.len parent .dyn) 2 3 := ⟨by decide, by rw [hml]; decide⟩
  have hd' : 1+(3-2) ≤ mid.len parent .dyn := by rw [hml]; decide
  let out := captureAfterCopy mid tree rfl parent .dyn parent .dyn 2 3 1 hs' hd'
  have hf := checkedCaptureOverwrite_some hp parent .dyn parent .dyn 1 2 0 hs hd
  have ho := captureAfterCopy_checked mid tree rfl parent .dyn parent .dyn 2 3 1 hs' hd'
  have hc : BoolChildRepr c address out s (r.wk (copyGrow mid).ext) :=
    hr.captureAfterCopy parent .dyn parent .dyn 1 2 0 mid hf tree rfl
      parent .dyn parent .dyn 2 3 1 hs' hd'
      (boolChild_parent_ne parent .dyn r) (boolChild_parent_ne parent .dyn r)
  refine ⟨mid, out, hf, ho, hc, ?_, (captureAfterCopy_fresh mid tree rfl parent .dyn parent .dyn 2 3 1 hs' hd').2.2⟩
  simp only [mid, captureOverwrite, overwriteSlice_elems, ← replaceSlice_map, sliceElems, List.map_take, List.map_drop]
  rw [hb]; rfl

theorem existing_boolean_chain :
    ∃ (D : Source.Layout) (H : HTy) (c : Source.Calldata D) (address : Nat → Nat)
      (hp mid : Heap H) (out : Heap (copyGrow mid).H')
      (s : Source.Data D BoolChildTy) (r : HRef H BoolChildRef) (parent : HRef H (.array (.ref BoolChildRef))),
      BoolChildRepr c address hp s r ∧
      checkedCaptureOverwrite hp parent .dyn parent .dyn 1 2 0 = some mid ∧
      checkedCaptureOverwrite (copyGrow mid).heap (parent.wk (copyGrow mid).ext) .dyn
        (parent.wk (copyGrow mid).ext) .dyn 2 3 1 = some out ∧
      BoolChildRepr c address out s (r.wk (copyGrow mid).ext) ∧
      (MObj.elems .dyn (hp.get parent)).map HRef.id = [1,0,1] ∧
      (MObj.elems .dyn (mid.get parent)).map HRef.id = [0,0,1] ∧
      out.get (copyGrow mid).val = (copyGrow mid).heap.get (copyGrow mid).val := by
  have hr := ChildControls.changed_shared.2.2
  obtain ⟨mid, out, hf, ho, hc, hm, hroot⟩ := boolean_chain hr ⟨2,rfl⟩ ChildControls.changed_shared.2.1
  exact ⟨_,_,_,_,_,mid,out,_,_,⟨2,rfl⟩,hr,hf,ho,hc,ChildControls.changed_shared.2.1,hm,hroot⟩
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderChildControls.existing_boolean_chain' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms existing_boolean_chain

private theorem nested_chain {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D RefChildTy} {r : HRef H RefChildRef}
    (hr : RefChildRepr c address hp s r) (parent : HRef H (.array (.ref RefChildRef)))
    (hb : (MObj.elems .dyn (hp.get parent)).map HRef.id = [3,2]) :
    ∃ (mid : Heap H) (out : Heap (defaultGrow mid).H'),
      checkedCaptureOverwrite hp parent .dyn parent .dyn 0 1 1 = some mid ∧
      checkedCaptureOverwrite (defaultGrow mid).heap (parent.wk (defaultGrow mid).ext) .dyn
        (parent.wk (defaultGrow mid).ext) .dyn 1 2 0 = some out ∧
      RefChildRepr c address out s (r.wk (defaultGrow mid).ext) ∧
      (MObj.elems .dyn (mid.get parent)).map HRef.id = [3,3] ∧
      out.get (defaultGrow mid).val = (defaultGrow mid).heap.get (defaultGrow mid).val := by
  have hn : hp.len parent .dyn = 2 := by
    have hl := congrArg List.length hb
    simpa only [List.length_map, List.length_cons, List.length_nil] using hl
  have hs : SliceBounds (hp.len parent .dyn) 0 1 := ⟨by decide, by rw [hn]; decide⟩
  have hd : 1+(1-0) ≤ hp.len parent .dyn := by rw [hn]; decide
  let mid := captureOverwrite hp parent .dyn parent .dyn 0 1 1 hs hd
  have hml : mid.len parent .dyn = 2 := by
    change (captureOverwrite hp parent .dyn parent .dyn 0 1 1 hs hd).len parent .dyn = 2
    rw [captureOverwrite_all_len, hn]
  have hs' : SliceBounds (mid.len parent .dyn) 1 2 := ⟨by decide, by rw [hml]; decide⟩
  have hd' : 0+(2-1) ≤ mid.len parent .dyn := by rw [hml]; decide
  let out := captureAfterCopy mid (SVal.dflt (.ref A)) rfl parent .dyn parent .dyn 1 2 0 hs' hd'
  have hf := checkedCaptureOverwrite_some hp parent .dyn parent .dyn 0 1 1 hs hd
  have ho := captureAfterCopy_checked mid (SVal.dflt (.ref A)) rfl parent .dyn parent .dyn 1 2 0 hs' hd'
  have hc : RefChildRepr c address out s (r.wk (defaultGrow mid).ext) :=
    hr.captureAfterCopy parent .dyn parent .dyn 0 1 1 mid hf (SVal.dflt (.ref A)) rfl
      parent .dyn parent .dyn 1 2 0 hs' hd'
      (refChild_parent_ne parent .dyn r) (refChild_parent_ne parent .dyn r)
      (fun q _ => refChild_leaf_ne parent .dyn q) (fun q _ => refChild_leaf_ne parent .dyn q)
  refine ⟨mid, out, hf, ho, hc, ?_, (captureAfterCopy_fresh mid (SVal.dflt (.ref A)) rfl parent .dyn parent .dyn 1 2 0 hs' hd').2.2⟩
  simp only [mid, captureOverwrite, overwriteSlice_elems, ← replaceSlice_map, sliceElems, List.map_take, List.map_drop]
  rw [hb]; rfl

theorem existing_nested_chain :
    ∃ (D : Source.Layout) (H : HTy) (c : Source.Calldata D) (address : Nat → Nat)
      (hp mid : Heap H) (out : Heap (defaultGrow mid).H')
      (s : Source.Data D RefChildTy) (r : HRef H RefChildRef) (parent : HRef H (.array (.ref RefChildRef))),
      RefChildRepr c address hp s r ∧
      checkedCaptureOverwrite hp parent .dyn parent .dyn 0 1 1 = some mid ∧
      checkedCaptureOverwrite (defaultGrow mid).heap (parent.wk (defaultGrow mid).ext) .dyn
        (parent.wk (defaultGrow mid).ext) .dyn 1 2 0 = some out ∧
      RefChildRepr c address out s (r.wk (defaultGrow mid).ext) ∧
      (MObj.elems .dyn (hp.get parent)).map HRef.id = [3,2] ∧
      (MObj.elems .dyn (mid.get parent)).map HRef.id = [3,3] ∧
      out.get (defaultGrow mid).val = (defaultGrow mid).heap.get (defaultGrow mid).val := by
  have hr := NestedChildControls.final_child
  obtain ⟨mid, out, hf, ho, hc, hm, hroot⟩ := nested_chain hr ⟨4,rfl⟩ NestedChildControls.changed_nested.2.1
  exact ⟨_,_,_,_,_,mid,out,_,_,⟨4,rfl⟩,hr,hf,ho,hc,NestedChildControls.changed_nested.2.1,hm,hroot⟩
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderChildControls.existing_nested_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms existing_nested_chain
end Solidity.Backend.MemoryOps.InterstageBuilderChildControls
