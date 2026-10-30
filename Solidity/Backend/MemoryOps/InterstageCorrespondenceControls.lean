import Solidity.Backend.MemoryOps.InterstageCorrespondence
import Solidity.Backend.MemoryOps.CalldataChildControls
import Solidity.Backend.MemoryOps.CalldataNestedControls

/-! Reuse an existing proved child certificate across actual interstage allocation.
No immutable Source entry, fresh Source representation or injectivity is invented. -/
namespace Solidity.Backend.MemoryOps.InterstageCorrespondenceControls

private theorem singleton_room : ([false] : List Bool).length < 2 ^ 256 := by decide

private theorem certificate_chain {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp s r) (parent : HRef H (.array (.ref BoolChildRef)))
    (hb : (MObj.elems .dyn (hp.get parent)).map HRef.id = [1, 0, 1]) :
    ∃ (mid : Heap H) (out : Heap (H ++ [BoolChildRef])) (o : MObj H BoolChildRef),
      checkedCaptureOverwrite hp parent .dyn parent .dyn 1 2 0 = some mid ∧
      checkedCaptureOverwrite (mid.alloc o).1 (parent.wk (List.prefix_append H [BoolChildRef])) .dyn
        (parent.wk (List.prefix_append H [BoolChildRef])) .dyn 2 3 1 = some out ∧
      BoolChildRepr c address out s (r.wk (List.prefix_append H [BoolChildRef])) ∧
      (MObj.elems .dyn (mid.get parent)).map HRef.id = [0, 0, 1] ∧
      (MObj.elems .dyn (out.get (parent.wk (List.prefix_append H [BoolChildRef])))).map HRef.id = [0, 1, 1] := by
  have hn : hp.len parent .dyn = 3 := by
    have hl := congrArg List.length hb
    simpa only [List.length_map, List.length_cons, List.length_nil] using hl
  have hs : SliceBounds (hp.len parent .dyn) 1 2 := ⟨by decide, by rw [hn]; decide⟩
  have hd : 0 + (2 - 1) ≤ hp.len parent .dyn := by rw [hn]; decide
  let mid := captureOverwrite hp parent .dyn parent .dyn 1 2 0 hs hd
  have hml : mid.len parent .dyn = 3 := by
    change (captureOverwrite hp parent .dyn parent .dyn 1 2 0 hs hd).len parent .dyn = 3
    rw [captureOverwrite_all_len, hn]
  have hs' : SliceBounds (mid.len parent .dyn) 2 3 := ⟨by decide, by rw [hml]; decide⟩
  have hd' : 1 + (3 - 2) ≤ mid.len parent .dyn := by rw [hml]; decide
  let o : MObj H BoolChildRef := ⟨[false], singleton_room⟩
  let e := List.prefix_append H [BoolChildRef]
  let out := captureAfterAlloc mid o parent .dyn parent .dyn 2 3 1 hs' hd'
  have hc : BoolChildRepr c address out s (r.wk e) :=
    hr.captureAfterFirstAlloc parent .dyn parent .dyn 1 2 0 hs hd o parent .dyn parent .dyn 2 3 1 hs' hd'
      (boolChild_parent_ne parent .dyn r) (boolChild_parent_ne parent .dyn r)
  have hm : (MObj.elems .dyn (mid.get parent)).map HRef.id = [0, 0, 1] := by
    simp only [mid, captureOverwrite, overwriteSlice_elems, ← replaceSlice_map, sliceElems, List.map_take, List.map_drop]
    rw [hb]
    rfl
  refine ⟨mid, out, o, checkedCaptureOverwrite_some hp parent .dyn parent .dyn 1 2 0 hs hd,
    captureAfterAlloc_checked mid o parent .dyn parent .dyn 2 3 1 hs' hd', hc, hm, ?_⟩
  have hk : Heap.Keeps e (captureOverwrite mid parent .dyn parent .dyn 2 3 1 hs' hd') out :=
    captureAfterAlloc_keeps mid o parent .dyn parent .dyn 2 3 1 hs' hd'
  rw [hk parent, MObj.elems_wk, List.map_map]
  change (MObj.elems .dyn ((captureOverwrite mid parent .dyn parent .dyn 2 3 1 hs' hd').get parent)).map HRef.id = _
  simp only [captureOverwrite, overwriteSlice_elems, ← replaceSlice_map, sliceElems, List.map_take, List.map_drop]
  rw [hm]
  rfl

theorem existing_certificate_chain :
    ∃ (D : Source.Layout) (H : HTy) (c : Source.Calldata D) (address : Nat → Nat)
      (hp mid : Heap H) (out : Heap (H ++ [BoolChildRef]))
      (s : Source.Data D BoolChildTy) (r : HRef H BoolChildRef)
      (parent : HRef H (.array (.ref BoolChildRef))) (o : MObj H BoolChildRef),
      BoolChildRepr c address hp s r ∧
      checkedCaptureOverwrite hp parent .dyn parent .dyn 1 2 0 = some mid ∧
      checkedCaptureOverwrite (mid.alloc o).1 (parent.wk (List.prefix_append H [BoolChildRef])) .dyn
        (parent.wk (List.prefix_append H [BoolChildRef])) .dyn 2 3 1 = some out ∧
      BoolChildRepr c address out s (r.wk (List.prefix_append H [BoolChildRef])) ∧
      (MObj.elems .dyn (hp.get parent)).map HRef.id = [1, 0, 1] ∧
      (MObj.elems .dyn (mid.get parent)).map HRef.id = [0, 0, 1] ∧
      (MObj.elems .dyn (out.get (parent.wk (List.prefix_append H [BoolChildRef])))).map HRef.id = [0, 1, 1] := by
  have hr := ChildControls.changed_shared.2.2
  obtain ⟨mid, out, o, hf, ho, hc, hm, hout⟩ := certificate_chain hr ⟨2, rfl⟩ ChildControls.changed_shared.2.1
  exact ⟨_, _, _, _, _, mid, out, _, _, ⟨2, rfl⟩, o, hr, hf, ho, hc, ChildControls.changed_shared.2.1, hm, hout⟩

private theorem nested_chain {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D RefChildTy} {r : HRef H RefChildRef}
    (hr : RefChildRepr c address hp s r) (parent : HRef H (.array (.ref RefChildRef)))
    (hb : (MObj.elems .dyn (hp.get parent)).map HRef.id = [3, 2]) :
    ∃ (mid : Heap H) (out : Heap (H ++ [BoolChildRef])) (o : MObj H BoolChildRef),
      checkedCaptureOverwrite hp parent .dyn parent .dyn 0 1 1 = some mid ∧
      checkedCaptureOverwrite (mid.alloc o).1 (parent.wk (List.prefix_append H [BoolChildRef])) .dyn
        (parent.wk (List.prefix_append H [BoolChildRef])) .dyn 1 2 0 = some out ∧
      RefChildRepr c address out s (r.wk (List.prefix_append H [BoolChildRef])) ∧
      (MObj.elems .dyn (mid.get parent)).map HRef.id = [3, 3] := by
  have hn : hp.len parent .dyn = 2 := by
    have hl := congrArg List.length hb
    simpa only [List.length_map, List.length_cons, List.length_nil] using hl
  have hs : SliceBounds (hp.len parent .dyn) 0 1 := ⟨by decide, by rw [hn]; decide⟩
  have hd : 1 + (1 - 0) ≤ hp.len parent .dyn := by rw [hn]; decide
  let mid := captureOverwrite hp parent .dyn parent .dyn 0 1 1 hs hd
  have hml : mid.len parent .dyn = 2 := by
    change (captureOverwrite hp parent .dyn parent .dyn 0 1 1 hs hd).len parent .dyn = 2
    rw [captureOverwrite_all_len, hn]
  have hs' : SliceBounds (mid.len parent .dyn) 1 2 := ⟨by decide, by rw [hml]; decide⟩
  have hd' : 0 + (2 - 1) ≤ mid.len parent .dyn := by rw [hml]; decide
  let o : MObj H BoolChildRef := ⟨[false], singleton_room⟩
  let e := List.prefix_append H [BoolChildRef]
  let out := captureAfterAlloc mid o parent .dyn parent .dyn 1 2 0 hs' hd'
  have hf := checkedCaptureOverwrite_some hp parent .dyn parent .dyn 0 1 1 hs hd
  have ho := captureAfterAlloc_checked mid o parent .dyn parent .dyn 1 2 0 hs' hd'
  have hc : RefChildRepr c address out s (r.wk e) :=
    hr.interstage parent .dyn parent .dyn 0 1 1 mid hf e (mid.alloc o).1
      (Heap.keeps_alloc mid o) parent .dyn parent .dyn 1 2 0 out ho
      (refChild_parent_ne parent .dyn r) (refChild_parent_ne parent .dyn r)
      (fun q _ => refChild_leaf_ne parent .dyn q) (fun q _ => refChild_leaf_ne parent .dyn q)
  refine ⟨mid, out, o, hf, ho, hc, ?_⟩
  simp only [mid, captureOverwrite, overwriteSlice_elems, ← replaceSlice_map, sliceElems, List.map_take, List.map_drop]
  rw [hb]
  rfl

/-- An inhabited nested certificate is framed across nonempty first capture,
actual allocation and recapture of its changed parent slot. -/
theorem existing_nested_chain :
    ∃ (D : Source.Layout) (H : HTy) (c : Source.Calldata D) (address : Nat → Nat)
      (hp mid : Heap H) (out : Heap (H ++ [BoolChildRef]))
      (s : Source.Data D RefChildTy) (r : HRef H RefChildRef)
      (parent : HRef H (.array (.ref RefChildRef))) (o : MObj H BoolChildRef),
      RefChildRepr c address hp s r ∧
      checkedCaptureOverwrite hp parent .dyn parent .dyn 0 1 1 = some mid ∧
      checkedCaptureOverwrite (mid.alloc o).1 (parent.wk (List.prefix_append H [BoolChildRef])) .dyn
        (parent.wk (List.prefix_append H [BoolChildRef])) .dyn 1 2 0 = some out ∧
      RefChildRepr c address out s (r.wk (List.prefix_append H [BoolChildRef])) ∧
      (MObj.elems .dyn (hp.get parent)).map HRef.id = [3, 2] ∧
      (MObj.elems .dyn (mid.get parent)).map HRef.id = [3, 3] := by
  have hr := NestedChildControls.final_child
  obtain ⟨mid, out, o, hf, ho, hc, hm⟩ := nested_chain hr ⟨4, rfl⟩ NestedChildControls.changed_nested.2.1
  exact ⟨_, _, _, _, _, mid, out, _, _, ⟨4, rfl⟩, o, hr, hf, ho, hc, NestedChildControls.changed_nested.2.1, hm⟩

/-- info: 'Solidity.Backend.MemoryOps.InterstageCorrespondenceControls.existing_nested_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms existing_nested_chain

/-- info: 'Solidity.Backend.MemoryOps.InterstageCorrespondenceControls.existing_certificate_chain' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms existing_certificate_chain
end Solidity.Backend.MemoryOps.InterstageCorrespondenceControls
