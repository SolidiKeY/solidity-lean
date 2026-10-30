import Solidity.Backend.MemoryOps.InterstageGrowth

/-! Distinct first source/destination and second target make both generalized
recapture branches discriminate hp.src from hp.dst. -/
namespace Solidity.Backend.MemoryOps.InterstageDistinctControls
private abbrev B := BoolChildRef
private abbrev P : RefTy := .fixed (.ref B) 2
private abbrev H : HTy := [B, B, B]
private def src : HRef H B := ⟨0, rfl⟩
private def dst : HRef H B := ⟨1, rfl⟩
private def target : HRef H B := ⟨2, rfl⟩
private def hp : Heap H := (⟨[true, false, true], by decide⟩,
  ⟨[false, false, false, false], by decide⟩, ⟨[false, false, false], by decide⟩, ())
private theorem hs : SliceBounds (hp.len src .dyn) 0 2 := by
  constructor
  · decide
  · simp only [Heap.len, MObj.elems_dyn]; decide
private theorem hd : 1 + (2 - 0) ≤ hp.len dst .dyn := by simp only [Heap.len, MObj.elems_dyn]; decide
private def mid := captureOverwrite hp src .dyn dst .dyn 0 2 1 hs hd
private theorem hf : checkedCaptureOverwrite hp src .dyn dst .dyn 0 2 1 = some mid :=
  checkedCaptureOverwrite_some hp src .dyn dst .dyn 0 2 1 hs hd
private theorem bound : SliceBounds (mid.len dst .dyn) 0 3 := by
  constructor
  · decide
  · change 3 ≤ (captureOverwrite hp src .dyn dst .dyn 0 2 1 hs hd).len dst .dyn
    rw [captureOverwrite_all_len]
    simp only [Heap.len, MObj.elems_dyn]; decide
private theorem room : 0 + (3 - 0) ≤ mid.len target .dyn := by
  change 0 + (3 - 0) ≤ (captureOverwrite hp src .dyn dst .dyn 0 2 1 hs hd).len target .dyn
  rw [captureOverwrite_all_len]
  simp only [Heap.len, MObj.elems_dyn]; decide
private def obj : MObj H P := ⟨[dst, target], rfl⟩
private def e := List.prefix_append H [P]
private def out := captureAfterAlloc mid obj dst .dyn target .dyn 0 3 0 bound room
private theorem mid_dst : MObj.elems .dyn (mid.get dst) = [false, true, false, false] := by
  simp only [mid, captureOverwrite, overwriteSlice_elems, sliceElems, MObj.elems_dyn]; rfl
private theorem mid_target : MObj.elems .dyn (mid.get target) = [false, false, false] := by
  rw [checkedCaptureOverwrite_frame hp src .dyn dst .dyn 0 2 1 mid hf target (by decide)]
  simp only [MObj.elems_dyn]; rfl

/-- All object roles are distinct, first success is real, and allocation occurs
on that first result before the actual second checked operation. -/
theorem actual_chain : src.id ≠ dst.id ∧ dst.id ≠ target.id ∧ src.id ≠ target.id ∧
    checkedCaptureOverwrite hp src .dyn dst .dyn 0 2 1 = some mid ∧
    checkedCaptureOverwrite (mid.alloc obj).1 (dst.wk e) .dyn (target.wk e) .dyn 0 3 0 = some out ∧
    MObj.elems .dyn (out.get (target.wk e)) = [false, true, false] := by
  refine ⟨by decide, by decide, by decide, hf, captureAfterAlloc_checked mid obj dst .dyn target .dyn 0 3 0 bound room, ?_⟩
  have hk : Heap.Keeps e (captureOverwrite mid dst .dyn target .dyn 0 3 0 bound room) out :=
    captureAfterAlloc_keeps mid obj dst .dyn target .dyn 0 3 0 bound room
  rw [hk target, MObj.elems_wk]
  simp only [captureOverwrite, overwriteSlice_elems, sliceElems, mid_dst, mid_target]
  rfl

/-- Outside first destination reads original dst=false, inside reads original
src=true. Substituting the other object in either branch would fail this test. -/
theorem both_branches : (MObj.elems .dyn (out.get (target.wk e)))[0]? = some false ∧
    (MObj.elems .dyn (out.get (target.wk e)))[1]? = some true := by
  constructor
  · simpa only [MObj.elems_dyn] using captureAfterAlloc_read_cases hp src .dyn dst .dyn 0 2 1 mid hf
      obj target .dyn 0 3 0 bound room 0 (by decide)
  · simpa only [MObj.elems_dyn] using captureAfterAlloc_read_cases hp src .dyn dst .dyn 0 2 1 mid hf
      obj target .dyn 0 3 0 bound room 1 (by decide)
private def zero : PrimTy.uint.Denote := ⟨0, by decide⟩
private def one : PrimTy.uint.Denote := ⟨1, by decide⟩
/-- Fresh fields preserve old target identity while the actual target changes. -/
theorem fresh_fields_and_read : (mid.alloc obj).2.id = 3 ∧
    (MObj.elems .fixed (out.get (mid.alloc obj).2)).map HRef.id = [1, 2] ∧
    out.index (mid.alloc obj).2 .fixed one = some (target.wk e) ∧
    out.index (target.wk e) .dyn one = some true := by
  refine ⟨rfl, ?_, ?_, both_branches.2⟩
  · simp only [out, captureAfterAlloc_fresh, MObj.elems_wk, List.map_map, MObj.elems_fixed]; rfl
  · simpa only [MObj.elems_fixed] using captureAfterAlloc_fresh_index mid obj dst .dyn target .dyn 0 3 0 bound room .fixed one

/-- info: 'Solidity.Backend.MemoryOps.InterstageDistinctControls.actual_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_chain
/-- info: 'Solidity.Backend.MemoryOps.InterstageDistinctControls.both_branches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms both_branches
/-- info: 'Solidity.Backend.MemoryOps.InterstageDistinctControls.fresh_fields_and_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_fields_and_read
end Solidity.Backend.MemoryOps.InterstageDistinctControls
