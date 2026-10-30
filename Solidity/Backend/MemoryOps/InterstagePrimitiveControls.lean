import Solidity.Backend.MemoryOps.InterstageGrowth

/-! Real first snapshot, allocation on its changed output, then recapture.
A fresh reference parent is structurally framed while its old child changes. -/
namespace Solidity.Backend.MemoryOps.InterstagePrimitiveControls
private abbrev B : RefTy := .array (.prim .bool)
private abbrev P : RefTy := .fixed (.ref B) 2
private abbrev H : HTy := [B]
private def r : HRef H B := ⟨0, rfl⟩
private def hp : Heap H := (⟨[true, false, false, true, false, false], by decide⟩, ())
private theorem hs : SliceBounds (hp.len r .dyn) 0 2 := by
  constructor
  · decide
  · simp only [Heap.len, MObj.elems_dyn]; decide
private theorem hd : 2 + (2 - 0) ≤ hp.len r .dyn := by simp only [Heap.len, MObj.elems_dyn]; decide
private def mid := captureOverwrite hp r .dyn r .dyn 0 2 2 hs hd
private theorem first_success : checkedCaptureOverwrite hp r .dyn r .dyn 0 2 2 = some mid :=
  checkedCaptureOverwrite_some hp r .dyn r .dyn 0 2 2 hs hd
private theorem mid_len : mid.len r .dyn = 6 := by
  change (captureOverwrite hp r .dyn r .dyn 0 2 2 hs hd).len r .dyn = 6
  rw [captureOverwrite_all_len]
  simp only [Heap.len, MObj.elems_dyn]
  rfl
private theorem bound (u v : Nat) (h : u ≤ v) (k : v ≤ 6) : SliceBounds (mid.len r .dyn) u v :=
  ⟨h, by rw [mid_len]; exact k⟩
private theorem room (u v f : Nat) (h : f + (v - u) ≤ 6) : f + (v - u) ≤ mid.len r .dyn := by
  rw [mid_len]; exact h
private def obj : MObj H P := ⟨[r, r], rfl⟩
private def e := List.prefix_append H [P]
private def old := r.wk e
private def fresh := (mid.alloc obj).2
private def out := captureAfterAlloc mid obj r .dyn r .dyn 2 4 4
  (bound _ _ (by decide) (by decide)) (room _ _ _ (by decide))
private theorem second_success : checkedCaptureOverwrite (mid.alloc obj).1 old .dyn old .dyn 2 4 4 = some out :=
  captureAfterAlloc_checked mid obj r .dyn r .dyn 2 4 4 _ _

private theorem initial_values : MObj.elems .dyn (hp.get r) = [true, false, false, true, false, false] := by
  simp only [MObj.elems_dyn]; rfl
private theorem mid_values : MObj.elems .dyn (mid.get r) = [true, false, true, false, false, false] := by
  simp only [mid, captureOverwrite, overwriteSlice_elems, sliceElems, initial_values]; rfl
private theorem allocated_old : (mid.alloc obj).1.get old = MObj.wk e B (mid.get r) :=
  Heap.keeps_alloc mid obj r

/-- The operation chain explicitly allocates on the actual changed first output. -/
theorem actual_chain :
    checkedCaptureOverwrite hp r .dyn r .dyn 0 2 2 = some mid ∧
    checkedCaptureOverwrite (mid.alloc obj).1 old .dyn old .dyn 2 4 4 = some out ∧
    MObj.elems .dyn (mid.get r) = [true, false, true, false, false, false] ∧
    MObj.elems .dyn (out.get old) = [true, false, true, false, true, false] := by
  refine ⟨first_success, second_success, ?_, ?_⟩
  · exact mid_values
  · have hk : Heap.Keeps e (captureOverwrite mid r .dyn r .dyn 2 4 4
        (bound _ _ (by decide) (by decide)) (room _ _ _ (by decide))) out :=
      captureAfterAlloc_keeps mid obj r .dyn r .dyn 2 4 4 _ _
    change MObj.elems .dyn (out.get (r.wk e)) = _
    rw [hk r, MObj.elems_wk]
    simp only [captureOverwrite, overwriteSlice_elems, sliceElems, mid_values]
    rfl

/-- The allocation-linked read law observes the changed first source, not hp[2]. -/
theorem recapture_read : (MObj.elems .dyn (out.get old))[4]? = some true := by
  simpa only [MObj.elems_dyn] using captureAfterAlloc_read_cases hp r .dyn r .dyn 0 2 2 mid first_success
    obj r .dyn 2 4 4 (bound _ _ (by decide) (by decide)) (room _ _ _ (by decide)) 0 (by decide)
private def zero : PrimTy.uint.Denote := ⟨0, by decide⟩
private def four : PrimTy.uint.Denote := ⟨4, by decide⟩
/-- Fresh identity and own fields are exact, including two repeated old aliases. -/
theorem fresh_fields : fresh.id = 1 ∧ old.id = 0 ∧ old.id ≠ fresh.id ∧
    (MObj.elems .fixed (out.get fresh)).map HRef.id = [0, 0] ∧
    out.index fresh .fixed zero = some old := by
  refine ⟨rfl, rfl, old_ne_fresh mid obj r, ?_, ?_⟩
  · simp only [out, fresh, captureAfterAlloc_fresh, MObj.elems_wk, List.map_map, MObj.elems_fixed]
    rfl
  · simpa only [MObj.elems_fixed] using captureAfterAlloc_fresh_index mid obj r .dyn r .dyn 2 4 4
      (bound _ _ (by decide) (by decide)) (room _ _ _ (by decide)) .fixed zero

/-- The old child referenced by unchanged fresh fields has actually changed. -/
theorem deep_content_negative : out.index old .dyn four = some true ∧
    (mid.alloc obj).1.index old .dyn four = some false ∧
    out.get old ≠ (mid.alloc obj).1.get old := by
  refine ⟨recapture_read, ?_, ?_⟩
  · simp only [Heap.index, old, Heap.keeps_alloc mid obj r, MObj.elems_wk, List.getElem?_map]
    rw [actual_chain.2.2.1]
    rfl
  · intro h
    have he := congrArg (fun o => (MObj.elems .dyn o)[4]?) h
    dsimp only at he
    rw [recapture_read] at he
    have hb : (MObj.elems .dyn ((mid.alloc obj).1.get old))[4]? = some false := by
      simp only [old, Heap.keeps_alloc mid obj r, MObj.elems_wk, List.getElem?_map]
      rw [actual_chain.2.2.1]
      rfl
    rw [hb] at he
    cases he

private def wrong := overwriteSlice (mid.alloc obj).1 old .dyn 4
  ((sliceElems hp r .dyn 2 4).map (MVal.wk e (.prim .bool)))
  (by
    simp only [old, List.length_map]
    rw [Heap.Keeps.len (Heap.keeps_alloc mid obj) r .dyn]
    rw [mid_len]
    simp only [sliceElems, initial_values]
    decide)
/-- A payload frozen from initial hp produces the wrong final values. -/
theorem original_snapshot_negative :
    MObj.elems .dyn (wrong.get old) = [true, false, true, false, false, true] ∧ out ≠ wrong := by
  have hw : MObj.elems .dyn (wrong.get old) = [true, false, true, false, false, true] := by
    rw [wrong, overwriteSlice_elems, allocated_old, MObj.elems_wk]
    simp only [sliceElems, initial_values, mid_values]
    rfl
  refine ⟨hw, ?_⟩
  intro h
  have he := congrArg (fun hp => MObj.elems .dyn (hp.get old)) h
  dsimp only at he
  rw [actual_chain.2.2.2, hw] at he
  cases he

/-- Independent stage-two reversed/source-only/destination-only failures use
mid's real length; the first successful snapshot remains recorded above. -/
theorem stage_two_failures :
    checkedCaptureOverwrite (mid.alloc obj).1 old .dyn old .dyn 3 1 0 = none ∧
    checkedCaptureOverwrite (mid.alloc obj).1 old .dyn old .dyn 5 7 0 = none ∧
    checkedCaptureOverwrite (mid.alloc obj).1 old .dyn old .dyn 0 2 5 = none := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    apply (captureAfterAlloc_none_iff mid obj r .dyn r .dyn _ _ _).mpr
    rw [mid_len]
    decide

/-- Empty copies at touching exact endpoints leave the allocated mid unchanged. -/
theorem empty_end : checkedCaptureOverwrite (mid.alloc obj).1 old .dyn old .dyn 6 6 6 = some (mid.alloc obj).1 := by
  apply checkedCaptureOverwrite_empty
  all_goals change 6 ≤ (mid.alloc obj).1.len (r.wk e) .dyn
  all_goals rw [Heap.Keeps.len (Heap.keeps_alloc mid obj) r .dyn, mid_len]
  all_goals decide

private def zeroHeap : Heap H := (⟨[], by decide⟩, ())
/-- A real empty first result is allocated before a real empty second result;
the supplied reference object still has two valid old empty-child identities. -/
theorem zero_length_chain :
    checkedCaptureOverwrite zeroHeap r .dyn r .dyn 0 0 0 = some zeroHeap ∧
    checkedCaptureOverwrite (zeroHeap.alloc obj).1 old .dyn old .dyn 0 0 0 = some (zeroHeap.alloc obj).1 ∧
    (MObj.elems .fixed ((zeroHeap.alloc obj).1.get (zeroHeap.alloc obj).2)).map HRef.id = [0, 0] := by
  refine ⟨checkedCaptureOverwrite_empty zeroHeap r .dyn r .dyn 0 0 (Nat.zero_le _) (Nat.zero_le _), ?_, ?_⟩
  · exact checkedCaptureOverwrite_empty (zeroHeap.alloc obj).1 old .dyn old .dyn 0 0 (Nat.zero_le _) (Nat.zero_le _)
  · rw [Heap.get_alloc, MObj.elems_wk, List.map_map]
    simp only [MObj.elems_fixed]; rfl

/-- Supplying the actual mid object to Heap.alloc records changed first-output
data in the fresh object, independently of the subsequent old-object write. -/
theorem supplied_mid_object :
    let o := mid.get r
    let h := captureAfterAlloc mid o r .dyn r .dyn 2 4 4
      (bound _ _ (by decide) (by decide)) (room _ _ _ (by decide))
    MObj.elems .dyn (h.get (mid.alloc o).2) = [true, false, true, false, false, false] := by
  dsimp only
  rw [captureAfterAlloc_fresh, MObj.elems_wk, mid_values]
  rfl
/-- info: 'Solidity.Backend.MemoryOps.InterstagePrimitiveControls.zero_length_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms zero_length_chain
/-- info: 'Solidity.Backend.MemoryOps.InterstagePrimitiveControls.supplied_mid_object' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms supplied_mid_object

/-- info: 'Solidity.Backend.MemoryOps.InterstagePrimitiveControls.actual_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_chain
/-- info: 'Solidity.Backend.MemoryOps.InterstagePrimitiveControls.recapture_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms recapture_read
/-- info: 'Solidity.Backend.MemoryOps.InterstagePrimitiveControls.fresh_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fresh_fields
/-- info: 'Solidity.Backend.MemoryOps.InterstagePrimitiveControls.deep_content_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms deep_content_negative
/-- info: 'Solidity.Backend.MemoryOps.InterstagePrimitiveControls.original_snapshot_negative' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms original_snapshot_negative
/-- info: 'Solidity.Backend.MemoryOps.InterstagePrimitiveControls.stage_two_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stage_two_failures
/-- info: 'Solidity.Backend.MemoryOps.InterstagePrimitiveControls.empty_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_end
end Solidity.Backend.MemoryOps.InterstagePrimitiveControls
