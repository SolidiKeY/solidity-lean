import Solidity.Backend.MemoryOps.InterstageBuilders

/-! Fixed/reference-valued snapshots with allocation between opposite overlap
directions. Fresh copied fields retain their new child IDs while the old parent changes. -/
namespace Solidity.Backend.MemoryOps.InterstageBuilderRefControls
private abbrev B := BoolChildRef
private abbrev P : RefTy := .fixed (.ref B) 4
private abbrev Q : RefTy := .fixed (.ref B) 2
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
private def tree : SVal (.ref Q) := .fixed
  (.cons (.array (.cons (.prim true) .nil) .nil (by decide))
    (.cons (.array (.cons (.prim false) .nil) .nil (by decide)) .nil))
private def grown := tree.copyStToM mid rfl
private def e := grown.ext
private theorem kg : Heap.Keeps e mid grown.heap := SVal.keeps_copyStToM tree rfl mid
private def old := parent.wk e
private def fresh := grown.val
private def out := captureAfterCopy mid tree rfl parent .fixed parent .fixed 1 4 0 bound room
private theorem second_success : checkedCaptureOverwrite grown.heap old .fixed old .fixed 1 4 0 = some out :=
  captureAfterCopy_checked mid tree rfl parent .fixed parent .fixed 1 4 0 bound room
private theorem iv : MObj.elems .fixed (hp.get parent) = [first, second, first, second] := by
  simp only [MObj.elems_fixed]; rfl
private theorem mv : MObj.elems .fixed (mid.get parent) = [first, first, second, first] := by
  simp only [mid, captureOverwrite, overwriteSlice_elems, sliceElems, MObj.elems_fixed]; rfl
private theorem ov : MObj.elems .fixed (out.get old) =
    [first.wk e, second.wk e, first.wk e, first.wk e] := by
  have hk : Heap.Keeps e (captureOverwrite mid parent .fixed parent .fixed 1 4 0 bound room) out :=
    captureAfterCopy_keeps mid tree rfl parent .fixed parent .fixed 1 4 0 bound room
  change MObj.elems .fixed (out.get (parent.wk e)) = _
  rw [hk parent, MObj.elems_wk]
  simp only [captureOverwrite, overwriteSlice_elems, sliceElems, mv]
  rfl

/-- Actual first output and actual allocated second output have opposite
snapshot-overlap observations, not source payloads frozen before both stages. -/
theorem actual_chain :
    checkedCaptureOverwrite hp parent .fixed parent .fixed 0 3 1 = some mid ∧
    checkedCaptureOverwrite grown.heap old .fixed old .fixed 1 4 0 = some out ∧
    (MObj.elems .fixed (mid.get parent)).map HRef.id = [0, 0, 1, 0] ∧
    (MObj.elems .fixed (out.get old)).map HRef.id = [0, 1, 0, 0] := by
  refine ⟨hf, second_success, ?_, ?_⟩
  · rw [mv]; rfl
  · rw [ov]; rfl

/-- The general allocation read-case law is inhabited with reference elements. -/
theorem recapture_read : (MObj.elems .fixed (out.get old))[1]? = some (second.wk e) := by
  simpa only [MObj.elems_fixed] using copy_interstage_read_cases hp parent .fixed parent .fixed 0 3 1 mid hf
    tree rfl parent .fixed 1 4 0 bound room 1 (by decide)
private def zero : PrimTy.uint.Denote := ⟨0, by decide⟩
private def one : PrimTy.uint.Denote := ⟨1, by decide⟩
/-- A real nested storage copy adds three objects; the root is framed. -/
theorem fresh_fields : grown.H' = [B,B,P,B,B,Q] ∧ fresh.id = 5 ∧ old.id = 2 ∧
    old.id ≠ fresh.id ∧ out.get fresh = grown.heap.get fresh := by
  have hc := captureAfterCopy_fresh mid tree rfl parent .fixed parent .fixed 1 4 0 bound room
  refine ⟨?_,?_,rfl,hc.2.1,hc.2.2⟩
  all_goals
    simp only [fresh, grown, tree, SVal.copyStToM_fixed, SVal.copyStToM_array,
      SVal.copyStToM_prim, SVec.copyStToM_cons, SVec.copyStToM_nil]
    rfl

/-- The old parent data changes through second recapture; root framing is a
separate fact about the newly copied tree, not old-child aliasing. -/
theorem changed_old_parent : out.index old .fixed one = some (second.wk e) ∧
    grown.heap.index old .fixed one = some (first.wk e) ∧
    out.get old ≠ grown.heap.get old := by
  refine ⟨recapture_read, ?_, ?_⟩
  · simp only [Heap.index, old, kg parent, MObj.elems_wk, List.getElem?_map]
    rw [mv]; rfl
  · intro h
    have he := congrArg (fun x : MObj (grown.H') P => (MObj.elems .fixed x).map HRef.id) h
    dsimp only at he
    rw [ov] at he
    have hm : MObj.elems .fixed (grown.heap.get old) =
        [first.wk e, first.wk e, second.wk e, first.wk e] := by
      simp only [old, kg parent, MObj.elems_wk]
      rw [mv]; rfl
    rw [hm] at he
    change [0, 1, 0, 0] = [0, 0, 1, 0] at he
    cases he

/-- Primitive child contents survive both reference-parent operations. -/
theorem leaf_frames : out.get (first.wk e) = MObj.wk e B (hp.get first) ∧
    out.get (second.wk e) = MObj.wk e B (hp.get second) := by
  have hk : Heap.Keeps e (captureOverwrite mid parent .fixed parent .fixed 1 4 0 bound room) out :=
    captureAfterCopy_keeps mid tree rfl parent .fixed parent .fixed 1 4 0 bound room
  constructor
  · rw [hk first]
    rw [checkedCaptureOverwrite_frame mid parent .fixed parent .fixed 1 4 0 _
      (checkedCaptureOverwrite_some mid parent .fixed parent .fixed 1 4 0 bound room) first (by decide),
      checkedCaptureOverwrite_frame hp parent .fixed parent .fixed 0 3 1 mid hf first (by decide)]
  · rw [hk second]
    rw [checkedCaptureOverwrite_frame mid parent .fixed parent .fixed 1 4 0 _
      (checkedCaptureOverwrite_some mid parent .fixed parent .fixed 1 4 0 bound room) second (by decide),
      checkedCaptureOverwrite_frame hp parent .fixed parent .fixed 0 3 1 mid hf second (by decide)]

private def wrong := overwriteSlice grown.heap old .fixed 0
  ((sliceElems hp parent .fixed 1 4).map (MVal.wk e (.ref B)))
  (by
    simp only [old, List.length_map]
    rw [Heap.Keeps.len (kg) parent .fixed, ml]
    simp only [sliceElems, MObj.elems_fixed]
    decide)
/-- Freezing before the first copy gives different references, despite exact
fresh fields being framed in either execution. -/
theorem original_snapshot_negative : out ≠ wrong := by
  intro h
  have he := congrArg (fun x : Heap (grown.H') => (MObj.elems .fixed (x.get old)).map HRef.id) h
  dsimp only at he
  rw [ov] at he
  have hw : MObj.elems .fixed (wrong.get old) =
      [second.wk e, first.wk e, second.wk e, first.wk e] := by
    rw [wrong, overwriteSlice_elems]
    simp only [old, kg parent, MObj.elems_wk, sliceElems, mv, iv]
    rfl
  rw [hw] at he
  change [0, 1, 0, 0] = [1, 0, 1, 0] at he
  cases he

/-- Stage-two failures are independent and use the actual intermediate length. -/
theorem stage_two_failures :
    checkedCaptureOverwrite grown.heap old .fixed old .fixed 3 1 0 = none ∧
    checkedCaptureOverwrite grown.heap old .fixed old .fixed 3 5 0 = none ∧
    checkedCaptureOverwrite grown.heap old .fixed old .fixed 0 2 3 = none := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    apply (copy_interstage_none_iff mid tree rfl parent .fixed parent .fixed _ _ _).mpr
    rw [ml]
    decide

/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderRefControls.actual_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_chain
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderRefControls.recapture_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms recapture_read
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderRefControls.fresh_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fresh_fields
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderRefControls.changed_old_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms changed_old_parent
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderRefControls.leaf_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms leaf_frames
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderRefControls.original_snapshot_negative' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms original_snapshot_negative
/-- info: 'Solidity.Backend.MemoryOps.InterstageBuilderRefControls.stage_two_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stage_two_failures
end Solidity.Backend.MemoryOps.InterstageBuilderRefControls
