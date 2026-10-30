import Solidity.Backend.MemoryOps.CheckedSnapshot

/-! Actual typed reference overlap, exact checked bounds, allocator growth and
nonempty element-boundary controls. None is not a Source/target halt claim. -/
namespace Solidity.Backend.MemoryOps.CheckedControls
private abbrev B : RefTy := .array (.prim .bool)
private abbrev P : RefTy := .fixed (.ref B) 4
private abbrev H : HTy := [B, B, P]
private def first : HRef H B := ⟨0, rfl⟩
private def second : HRef H B := ⟨1, rfl⟩
private def parent : HRef H P := ⟨2, rfl⟩
private def hp : Heap H := (⟨[true], by decide⟩, ⟨[false], by decide⟩,
  ⟨[first, second, first, first], rfl⟩, ())
private theorem hs : SliceBounds (hp.len parent .fixed) 0 3 := by
  constructor
  · decide
  · simp only [Heap.len, MObj.elems_fixed]; decide
private theorem hd : 1 + (3 - 0) ≤ hp.len parent .fixed := by
  simp only [Heap.len, MObj.elems_fixed]; decide
private def out := captureOverwrite hp parent .fixed parent .fixed 0 3 1 hs hd
private theorem success : checkedCaptureOverwrite hp parent .fixed parent .fixed 0 3 1 = some out :=
  checkedCaptureOverwrite_some hp parent .fixed parent .fixed 0 3 1 hs hd

/-- A true same-object right overlap retains captured child identities. -/
theorem right_overlap :
    checkedCaptureOverwrite hp parent .fixed parent .fixed 0 3 1 = some out ∧
    (MObj.elems .fixed (out.get parent)).map HRef.id = [0, 0, 1, 0] ∧
    out.get first = hp.get first ∧ out.get second = hp.get second := by
  refine ⟨success, ?_, ?_, ?_⟩
  · rw [out, captureOverwrite, overwriteSlice_elems]
    simp only [sliceElems, MObj.elems_fixed]; rfl
  · exact checkedCaptureOverwrite_frame hp parent .fixed parent .fixed 0 3 1 out success first (by decide)
  · exact checkedCaptureOverwrite_frame hp parent .fixed parent .fixed 0 3 1 out success second (by decide)

/-- Generic successful-read transport applies to the actual overlapped slot. -/
theorem captured_read : (MObj.elems .fixed (out.get parent))[2]? = some second := by
  simpa only [MObj.elems_fixed] using
    checkedCaptureOverwrite_read hp parent .fixed parent .fixed 0 3 1 1 out success (by decide)

private theorem left_hs : SliceBounds (hp.len parent .fixed) 1 4 := by
  constructor
  · decide
  · simp only [Heap.len, MObj.elems_fixed]; decide
private theorem left_hd : 0 + (4 - 1) ≤ hp.len parent .fixed := by
  simp only [Heap.len, MObj.elems_fixed]; decide
private def leftOut := captureOverwrite hp parent .fixed parent .fixed 1 4 0 left_hs left_hd

theorem left_overlap :
    checkedCaptureOverwrite hp parent .fixed parent .fixed 1 4 0 = some leftOut ∧
    (MObj.elems .fixed (leftOut.get parent)).map HRef.id = [1, 0, 0, 0] := by
  refine ⟨checkedCaptureOverwrite_some hp parent .fixed parent .fixed 1 4 0 left_hs left_hd, ?_⟩
  rw [leftOut, captureOverwrite, overwriteSlice_elems]
  simp only [sliceElems, MObj.elems_fixed]; rfl

/-- Forward streaming would erase the second child's identity, unlike snapshot. -/
theorem streaming_negative : (MObj.elems .fixed (out.get parent)).map HRef.id ≠ [0, 0, 0, 0] := by
  rw [right_overlap.2.1]
  decide

theorem reversed_failure : checkedCaptureOverwrite hp parent .fixed parent .fixed 3 1 0 = none :=
  (checkedCaptureOverwrite_none_iff hp parent .fixed parent .fixed 3 1 0).mpr (.inl (by decide))
theorem source_failure : checkedCaptureOverwrite hp parent .fixed parent .fixed 3 5 0 = none :=
  (checkedCaptureOverwrite_none_iff hp parent .fixed parent .fixed 3 5 0).mpr
    (.inr (.inl (by simp only [Heap.len, MObj.elems_fixed]; decide)))
theorem destination_failure : checkedCaptureOverwrite hp parent .fixed parent .fixed 0 3 2 = none :=
  (checkedCaptureOverwrite_none_iff hp parent .fixed parent .fixed 0 3 2).mpr
    (.inr (.inr (by simp only [Heap.len, MObj.elems_fixed]; decide)))
theorem empty_end : checkedCaptureOverwrite hp parent .fixed parent .fixed 4 4 4 = some hp :=
  checkedCaptureOverwrite_empty hp parent .fixed parent .fixed 4 4
    (by simp only [Heap.len, MObj.elems_fixed]; decide)
    (by simp only [Heap.len, MObj.elems_fixed]; decide)

/-- The source-only negative leaves ordering and destination capacity valid. -/
theorem source_guard_isolated :
    checkedCaptureOverwrite hp parent .fixed parent .fixed 3 5 0 = none ∧
    3 ≤ 5 ∧ 0 + (5 - 3) ≤ hp.len parent .fixed := by
  refine ⟨source_failure, by decide, ?_⟩
  simp only [Heap.len, MObj.elems_fixed]
  decide

private abbrev EmptyH : HTy := [B]
private def emptyRef : HRef EmptyH B := ⟨0, rfl⟩
private def emptyHeap : Heap EmptyH := (⟨[], by decide⟩, ())
/-- A real zero-length dynamic object succeeds unchanged; empty intervals still
reject invalid source endpoints and invalid destination offsets independently. -/
theorem empty_dynamic :
    checkedCaptureOverwrite emptyHeap emptyRef .dyn emptyRef .dyn 0 0 0 = some emptyHeap ∧
    checkedCaptureOverwrite emptyHeap emptyRef .dyn emptyRef .dyn 1 1 0 = none ∧
    checkedCaptureOverwrite emptyHeap emptyRef .dyn emptyRef .dyn 0 0 1 = none := by
  refine ⟨checkedCaptureOverwrite_empty emptyHeap emptyRef .dyn emptyRef .dyn 0 0
    (Nat.zero_le _) (Nat.zero_le _), ?_, ?_⟩
  · apply (checkedCaptureOverwrite_none_iff emptyHeap emptyRef .dyn emptyRef .dyn 1 1 0).mpr
    exact .inr (.inl (by simp only [Heap.len, MObj.elems_dyn]; decide))
  · apply (checkedCaptureOverwrite_none_iff emptyHeap emptyRef .dyn emptyRef .dyn 0 0 1).mpr
    exact .inr (.inr (by simp only [Heap.len, MObj.elems_dyn]; decide))

/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.source_guard_isolated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_guard_isolated
/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.empty_dynamic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms empty_dynamic

private def obj : MObj H P := ⟨[first, first, first, first], rfl⟩
private def e := List.prefix_append H [P]
/-- The allocator supplies initial growth, output preservation is derived, and
the fresh reference-containing object's own slots are actually untouched. -/
theorem allocation_success : ∃ out',
    checkedCaptureOverwrite (hp.alloc obj).1 (parent.wk e) .fixed (parent.wk e) .fixed 0 3 1 = some out' ∧
    Heap.Keeps e out out' ∧ out'.get (hp.alloc obj).2 = (hp.alloc obj).1.get (hp.alloc obj).2 := by
  obtain ⟨out', ho, hk⟩ := checkedCaptureOverwrite_keeps e (Heap.keeps_alloc hp obj)
    parent .fixed parent .fixed 0 3 1 out success
  exact ⟨out', ho, hk, checkedCaptureOverwrite_frame (hp.alloc obj).1
    (parent.wk e) .fixed (parent.wk e) .fixed 0 3 1 out' ho (hp.alloc obj).2 (old_ne_fresh hp obj parent)⟩

theorem allocation_failure :
    checkedCaptureOverwrite (hp.alloc obj).1 (parent.wk e) .fixed (parent.wk e) .fixed 0 3 2 = none :=
  (checkedCaptureOverwrite_none_keeps e (Heap.keeps_alloc hp obj) parent .fixed parent .fixed 0 3 2).mpr destination_failure

private abbrev BigH : HTy := [B]
private def big : HRef BigH B := ⟨0, rfl⟩
private def bits : List Bool := List.ofFn (fun i : Fin 65 => i.val = 32)
private def bigHeap : Heap BigH := (⟨bits, by simp only [bits, List.length_ofFn]; decide⟩, ())
private theorem bigHs : SliceBounds (bigHeap.len big .dyn) 31 64 := by
  constructor
  · decide
  · simp only [Heap.len, MObj.elems_dyn]; decide
private theorem bigHd : 32 + (64 - 31) ≤ bigHeap.len big .dyn := by
  simp only [Heap.len, MObj.elems_dyn]; decide
private def bigOut := captureOverwrite bigHeap big .dyn big .dyn 31 64 32 bigHs bigHd
/-- Thirty-three captured elements overlap across element index32; no payload cap. -/
theorem boundary_overlap :
    checkedCaptureOverwrite bigHeap big .dyn big .dyn 31 64 32 = some bigOut ∧
    (MObj.elems .dyn (bigOut.get big))[33]? = some true := by
  have ho := checkedCaptureOverwrite_some bigHeap big .dyn big .dyn 31 64 32 bigHs bigHd
  refine ⟨ho, ?_⟩
  have hr := checkedCaptureOverwrite_read bigHeap big .dyn big .dyn 31 64 32 1 bigOut ho (by decide)
  simpa only [MObj.elems_dyn] using hr

/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.right_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms right_overlap
/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.captured_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captured_read
/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.left_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms left_overlap
/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.streaming_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms streaming_negative
/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.reversed_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reversed_failure
/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.source_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_failure
/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.destination_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms destination_failure
/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.empty_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_end
/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.allocation_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms allocation_success
/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.allocation_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms allocation_failure
/-- info: 'Solidity.Backend.MemoryOps.CheckedControls.boundary_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms boundary_overlap
end Solidity.Backend.MemoryOps.CheckedControls
