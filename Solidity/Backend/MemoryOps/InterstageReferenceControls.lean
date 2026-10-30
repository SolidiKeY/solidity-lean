import Solidity.Backend.MemoryOps.InterstageGrowth

/-! Fixed/reference-valued snapshots with allocation between opposite overlap
directions. Fresh fields keep the old parent's ID while that parent changes. -/
namespace Solidity.Backend.MemoryOps.InterstageReferenceControls
private abbrev B := BoolChildRef
private abbrev P : RefTy := .fixed (.ref B) 4
private abbrev Q : RefTy := .fixed (.ref P) 2
private abbrev H : HTy := [B, B, P]
private def first : HRef H B := ⟨0, rfl⟩
private def second : HRef H B := ⟨1, rfl⟩
private def parent : HRef H P := ⟨2, rfl⟩
private def hp : Heap H := (⟨[true], by decide⟩, ⟨[false], by decide⟩,
  ⟨[first, second, first, second], rfl⟩, ())
private theorem hs : SliceBounds (hp.len parent .fixed) 0 3 := by
  constructor
  · decide
  · simp only [Heap.len, MObj.elems_fixed]; decide
private theorem hd : 1 + (3 - 0) ≤ hp.len parent .fixed := by simp only [Heap.len, MObj.elems_fixed]; decide
private def mid := captureOverwrite hp parent .fixed parent .fixed 0 3 1 hs hd
private theorem hf : checkedCaptureOverwrite hp parent .fixed parent .fixed 0 3 1 = some mid :=
  checkedCaptureOverwrite_some hp parent .fixed parent .fixed 0 3 1 hs hd
private theorem ml : mid.len parent .fixed = 4 := by
  change (captureOverwrite hp parent .fixed parent .fixed 0 3 1 hs hd).len parent .fixed = 4
  rw [captureOverwrite_all_len]
  simp only [Heap.len, MObj.elems_fixed]; rfl
private theorem bound : SliceBounds (mid.len parent .fixed) 1 4 := ⟨by decide, by rw [ml]; exact Nat.le_refl _⟩
private theorem room : 0 + (4 - 1) ≤ mid.len parent .fixed := by rw [ml]; decide
private def obj : MObj H Q := ⟨[parent, parent], rfl⟩
private def e := List.prefix_append H [Q]
private def old := parent.wk e
private def fresh := (mid.alloc obj).2
private def out := captureAfterAlloc mid obj parent .fixed parent .fixed 1 4 0 bound room
private theorem second_success : checkedCaptureOverwrite (mid.alloc obj).1 old .fixed old .fixed 1 4 0 = some out :=
  captureAfterAlloc_checked mid obj parent .fixed parent .fixed 1 4 0 bound room
private theorem iv : MObj.elems .fixed (hp.get parent) = [first, second, first, second] := by
  simp only [MObj.elems_fixed]; rfl
private theorem mv : MObj.elems .fixed (mid.get parent) = [first, first, second, first] := by
  simp only [mid, captureOverwrite, overwriteSlice_elems, sliceElems, MObj.elems_fixed]; rfl
private theorem ov : MObj.elems .fixed (out.get old) =
    [first.wk e, second.wk e, first.wk e, first.wk e] := by
  have hk : Heap.Keeps e (captureOverwrite mid parent .fixed parent .fixed 1 4 0 bound room) out :=
    captureAfterAlloc_keeps mid obj parent .fixed parent .fixed 1 4 0 bound room
  change MObj.elems .fixed (out.get (parent.wk e)) = _
  rw [hk parent, MObj.elems_wk]
  simp only [captureOverwrite, overwriteSlice_elems, sliceElems, mv]
  rfl

/-- Actual first output and actual allocated second output have opposite
snapshot-overlap observations, not source payloads frozen before both stages. -/
theorem actual_chain :
    checkedCaptureOverwrite hp parent .fixed parent .fixed 0 3 1 = some mid ∧
    checkedCaptureOverwrite (mid.alloc obj).1 old .fixed old .fixed 1 4 0 = some out ∧
    (MObj.elems .fixed (mid.get parent)).map HRef.id = [0, 0, 1, 0] ∧
    (MObj.elems .fixed (out.get old)).map HRef.id = [0, 1, 0, 0] := by
  refine ⟨hf, second_success, ?_, ?_⟩
  · rw [mv]; rfl
  · rw [ov]; rfl

/-- The general allocation read-case law is inhabited with reference elements. -/
theorem recapture_read : (MObj.elems .fixed (out.get old))[1]? = some (second.wk e) := by
  simpa only [MObj.elems_fixed] using captureAfterAlloc_read_cases hp parent .fixed parent .fixed 0 3 1 mid hf
    obj parent .fixed 1 4 0 bound room 1 (by decide)
private def zero : PrimTy.uint.Denote := ⟨0, by decide⟩
private def one : PrimTy.uint.Denote := ⟨1, by decide⟩
/-- Exact fresh identity and repeated old-parent fields, with actual typed read. -/
theorem fresh_fields : fresh.id = 3 ∧ old.id = 2 ∧ old.id ≠ fresh.id ∧
    (MObj.elems .fixed (out.get fresh)).map HRef.id = [2, 2] ∧
    out.index fresh .fixed zero = some old := by
  refine ⟨rfl, rfl, old_ne_fresh mid obj parent, ?_, ?_⟩
  · simp only [out, fresh, captureAfterAlloc_fresh, MObj.elems_wk, List.map_map, MObj.elems_fixed]; rfl
  · simpa only [MObj.elems_fixed] using
      captureAfterAlloc_fresh_index mid obj parent .fixed parent .fixed 1 4 0 bound room .fixed zero

/-- Fresh structural fields are constant while the referenced old parent data
changes: deep content liveness is not a consequence of framing. -/
theorem changed_old_parent : out.index old .fixed one = some (second.wk e) ∧
    (mid.alloc obj).1.index old .fixed one = some (first.wk e) ∧
    out.get old ≠ (mid.alloc obj).1.get old := by
  refine ⟨recapture_read, ?_, ?_⟩
  · simp only [Heap.index, old, Heap.keeps_alloc mid obj parent, MObj.elems_wk, List.getElem?_map]
    rw [mv]; rfl
  · intro h
    have he := congrArg (fun x : MObj (H ++ [Q]) P => (MObj.elems .fixed x).map HRef.id) h
    dsimp only at he
    rw [ov] at he
    have hm : MObj.elems .fixed ((mid.alloc obj).1.get old) =
        [first.wk e, first.wk e, second.wk e, first.wk e] := by
      simp only [old, Heap.keeps_alloc mid obj parent, MObj.elems_wk]
      rw [mv]; rfl
    rw [hm] at he
    change [0, 1, 0, 0] = [0, 0, 1, 0] at he
    cases he

/-- Primitive child contents survive both reference-parent operations. -/
theorem leaf_frames : out.get (first.wk e) = MObj.wk e B (hp.get first) ∧
    out.get (second.wk e) = MObj.wk e B (hp.get second) := by
  have hk : Heap.Keeps e (captureOverwrite mid parent .fixed parent .fixed 1 4 0 bound room) out :=
    captureAfterAlloc_keeps mid obj parent .fixed parent .fixed 1 4 0 bound room
  constructor
  · rw [hk first]
    rw [checkedCaptureOverwrite_frame mid parent .fixed parent .fixed 1 4 0 _
      (checkedCaptureOverwrite_some mid parent .fixed parent .fixed 1 4 0 bound room) first (by decide),
      checkedCaptureOverwrite_frame hp parent .fixed parent .fixed 0 3 1 mid hf first (by decide)]
  · rw [hk second]
    rw [checkedCaptureOverwrite_frame mid parent .fixed parent .fixed 1 4 0 _
      (checkedCaptureOverwrite_some mid parent .fixed parent .fixed 1 4 0 bound room) second (by decide),
      checkedCaptureOverwrite_frame hp parent .fixed parent .fixed 0 3 1 mid hf second (by decide)]

private def wrong := overwriteSlice (mid.alloc obj).1 old .fixed 0
  ((sliceElems hp parent .fixed 1 4).map (MVal.wk e (.ref B)))
  (by
    simp only [old, List.length_map]
    rw [Heap.Keeps.len (Heap.keeps_alloc mid obj) parent .fixed, ml]
    simp only [sliceElems, MObj.elems_fixed]
    decide)
/-- Freezing before the first copy gives different references, despite exact
fresh fields being framed in either execution. -/
theorem original_snapshot_negative : out ≠ wrong := by
  intro h
  have he := congrArg (fun x : Heap (H ++ [Q]) => (MObj.elems .fixed (x.get old)).map HRef.id) h
  dsimp only at he
  rw [ov] at he
  have hw : MObj.elems .fixed (wrong.get old) =
      [second.wk e, first.wk e, second.wk e, first.wk e] := by
    rw [wrong, overwriteSlice_elems]
    simp only [old, Heap.keeps_alloc mid obj parent, MObj.elems_wk, sliceElems, mv, iv]
    rfl
  rw [hw] at he
  change [0, 1, 0, 0] = [1, 0, 1, 0] at he
  cases he

/-- Stage-two failures are independent and use the actual intermediate length. -/
theorem stage_two_failures :
    checkedCaptureOverwrite (mid.alloc obj).1 old .fixed old .fixed 3 1 0 = none ∧
    checkedCaptureOverwrite (mid.alloc obj).1 old .fixed old .fixed 3 5 0 = none ∧
    checkedCaptureOverwrite (mid.alloc obj).1 old .fixed old .fixed 0 2 3 = none := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    apply (captureAfterAlloc_none_iff mid obj parent .fixed parent .fixed _ _ _).mpr
    rw [ml]
    decide

/-- info: 'Solidity.Backend.MemoryOps.InterstageReferenceControls.actual_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_chain
/-- info: 'Solidity.Backend.MemoryOps.InterstageReferenceControls.recapture_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms recapture_read
/-- info: 'Solidity.Backend.MemoryOps.InterstageReferenceControls.fresh_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fresh_fields
/-- info: 'Solidity.Backend.MemoryOps.InterstageReferenceControls.changed_old_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms changed_old_parent
/-- info: 'Solidity.Backend.MemoryOps.InterstageReferenceControls.leaf_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms leaf_frames
/-- info: 'Solidity.Backend.MemoryOps.InterstageReferenceControls.original_snapshot_negative' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms original_snapshot_negative
/-- info: 'Solidity.Backend.MemoryOps.InterstageReferenceControls.stage_two_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stage_two_failures
end Solidity.Backend.MemoryOps.InterstageReferenceControls
