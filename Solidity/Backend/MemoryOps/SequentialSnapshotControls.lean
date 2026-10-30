import Solidity.Backend.MemoryOps.SequentialTransport

/-! Actual dynamic heap recapture and checked first/second failure observations.
Separated destinations alone do not make source-dependent copies commute. -/
namespace Solidity.Backend.MemoryOps.SequentialControls
private abbrev B : RefTy := .array (.prim .bool)
private abbrev H : HTy := [B]
private def r : HRef H B := ⟨0, rfl⟩
private def hp : Heap H := (⟨[true, false, false, true, false, false], by decide⟩, ())
private theorem hs : SliceBounds (hp.len r .dyn) 0 2 := by
  constructor
  · decide
  · simp only [Heap.len, MObj.elems_dyn]; decide
private theorem hd : 2 + (2 - 0) ≤ hp.len r .dyn := by simp only [Heap.len, MObj.elems_dyn]; decide
private theorem hu : SliceBounds (hp.len r .dyn) 2 4 := by
  constructor
  · decide
  · simp only [Heap.len, MObj.elems_dyn]; decide
private theorem he : 4 + (4 - 2) ≤ hp.len r .dyn := by simp only [Heap.len, MObj.elems_dyn]; decide
private def mid := captureOverwrite hp r .dyn r .dyn 0 2 2 hs hd
private def out := captureTwice hp r .dyn 0 2 2 hs hd 2 4 4 hu he
private def rev := captureTwice hp r .dyn 2 4 4 hu he 0 2 2 hs hd
private def frozen := overwriteIntervals hp r .dyn 2 (sliceElems hp r .dyn 0 2)
  (by rw [sliceElems_length hp r .dyn hs]; exact hd) 4 (sliceElems hp r .dyn 2 4)
  (by rw [sliceElems_length hp r .dyn hu]; exact he)
private theorem success : checkedCaptureSequence hp r .dyn r .dyn 0 2 2 r .dyn r .dyn 2 4 4 = some out :=
  captureTwice_checked hp r .dyn 0 2 2 hs hd 2 4 4 hu he

/-- Two touching but separated destinations; the second source is precisely
where the first copy wrote. Actual recapture differs from both-original inputs. -/
theorem recapture_effect :
    IntervalsApart 2 2 4 2 ∧
    (MObj.elems .dyn (out.get r)) = [true, false, true, false, true, false] ∧
    (MObj.elems .dyn (frozen.get r)) = [true, false, true, false, false, true] ∧
    (MObj.elems .dyn (rev.get r)) = [true, false, true, false, false, true] := by
  refine ⟨.inr (.inr (.inl (by decide))), ?_, ?_, ?_⟩
  all_goals simp only [out, rev, frozen, captureTwice, captureOverwrite, overwriteIntervals,
    overwriteSlice_elems, sliceElems, MObj.elems_dyn]
  all_goals rfl

/-- A concrete counterexample to freezing source payloads or commuting arbitrary
snapshots from destination separation alone. -/
theorem recapture_negative : out ≠ frozen ∧ out ≠ rev := by
  constructor
  all_goals
    intro h
    have ho := congrArg (fun h : Heap H => MObj.elems .dyn (h.get r)) h
    simp only [recapture_effect.2.1, recapture_effect.2.2.1, recapture_effect.2.2.2] at ho
    cases ho

/-- The ordered read formula selects the first source when the second source
is inside its destination. -/
theorem read_case_application :
    (MObj.elems .dyn (out.get r))[4]? = some true ∧
    (MObj.elems .dyn (out.get r))[5]? = some false := by
  constructor
  · simpa only [MObj.elems_dyn] using captureTwice_inside hp r .dyn 0 2 2 hs hd 2 4 4 hu he 0 (by decide)
  · simpa only [MObj.elems_dyn] using captureTwice_inside hp r .dyn 0 2 2 hs hd 2 4 4 hu he 1 (by decide)

private theorem mixedSource : SliceBounds (hp.len r .dyn) 1 4 := by
  constructor
  · decide
  · simp only [Heap.len, MObj.elems_dyn]; decide
private theorem mixedRoom : 3 + (4 - 1) ≤ hp.len r .dyn := by
  simp only [Heap.len, MObj.elems_dyn]; decide
private def mixedOut := captureTwice hp r .dyn 0 2 2 hs hd 1 4 3 mixedSource mixedRoom
/-- Exercise outside both writes, retained first-only destination, and second
captures from outside/inside the first destination, respectively. -/
theorem all_read_branches :
    (MObj.elems .dyn (mixedOut.get r))[0]? = some true ∧
    (MObj.elems .dyn (mixedOut.get r))[2]? = some true ∧
    (MObj.elems .dyn (mixedOut.get r))[3]? = some false ∧
    (MObj.elems .dyn (mixedOut.get r))[4]? = some true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [MObj.elems_dyn] using captureTwice_read_cases hp r .dyn 0 2 2 hs hd 1 4 3 mixedSource mixedRoom 0
  · simpa only [MObj.elems_dyn] using captureTwice_read_cases hp r .dyn 0 2 2 hs hd 1 4 3 mixedSource mixedRoom 2
  · simpa only [MObj.elems_dyn] using captureTwice_read_cases hp r .dyn 0 2 2 hs hd 1 4 3 mixedSource mixedRoom 3
  · simpa only [MObj.elems_dyn] using captureTwice_read_cases hp r .dyn 0 2 2 hs hd 1 4 3 mixedSource mixedRoom 4
/-- info: 'Solidity.Backend.MemoryOps.SequentialControls.all_read_branches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms all_read_branches

/-- Actual checked success, not merely a conditional observation lemma. -/
theorem checked_success : checkedCaptureSequence hp r .dyn r .dyn 0 2 2 r .dyn r .dyn 2 4 4 = some out := success

/-- Each stage independently rejects reversed, source-only and destination-only
overrun cases, while the other operation's bounds remain valid. -/
theorem isolated_checked_failures :
    checkedCaptureSequence hp r .dyn r .dyn 3 1 0 r .dyn r .dyn 0 1 0 = none ∧
    checkedCaptureSequence hp r .dyn r .dyn 5 7 0 r .dyn r .dyn 0 1 0 = none ∧
    checkedCaptureSequence hp r .dyn r .dyn 0 2 5 r .dyn r .dyn 0 1 0 = none ∧
    checkedCaptureSequence hp r .dyn r .dyn 0 2 2 r .dyn r .dyn 3 1 0 = none ∧
    checkedCaptureSequence hp r .dyn r .dyn 0 2 2 r .dyn r .dyn 5 7 0 = none ∧
    checkedCaptureSequence hp r .dyn r .dyn 0 2 2 r .dyn r .dyn 0 2 5 = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply (checkedCaptureSequence_none_iff hp r .dyn r .dyn _ _ _ r .dyn r .dyn _ _ _).mpr
    simp only [Heap.len, MObj.elems_dyn]
    decide

/-- On second-stage failure the first operation really succeeded; this records
intermediate Option results and asserts no rollback or Source halt semantics. -/
theorem second_failure_intermediate :
    checkedCaptureOverwrite hp r .dyn r .dyn 0 2 2 = some mid ∧
    checkedCaptureOverwrite mid r .dyn r .dyn 5 7 0 = none := by
  refine ⟨checkedCaptureOverwrite_some hp r .dyn r .dyn 0 2 2 hs hd, ?_⟩
  apply (checkedCaptureOverwrite_none_iff mid r .dyn r .dyn 5 7 0).mpr
  simp only [mid, captureOverwrite_all_len]
  simp only [Heap.len, MObj.elems_dyn]
  decide

private def obj : MObj H B := ⟨[false], by decide⟩
/-- Published allocation supplies the growth premise for both real captures. -/
theorem allocator_sequence : ∃ out',
    checkedCaptureSequence (hp.alloc obj).1 (r.wk (List.prefix_append H [B])) .dyn
      (r.wk (List.prefix_append H [B])) .dyn 0 2 2 (r.wk (List.prefix_append H [B])) .dyn
      (r.wk (List.prefix_append H [B])) .dyn 2 4 4 = some out' ∧
      Heap.Keeps (List.prefix_append H [B]) out out' :=
  checkedCaptureSequence_keeps _ (Heap.keeps_alloc hp obj) r .dyn r .dyn 0 2 2 r .dyn r .dyn 2 4 4 out success

/-- Empty copies at exact endpoints are still identities on a nonempty heap. -/
theorem empty_end : checkedCaptureSequence hp r .dyn r .dyn 6 6 6 r .dyn r .dyn 6 6 6 = some hp := by
  unfold checkedCaptureSequence
  rw [checkedCaptureOverwrite_empty hp r .dyn r .dyn 6 6
    (by simp only [Heap.len, MObj.elems_dyn]; decide)
    (by simp only [Heap.len, MObj.elems_dyn]; decide)]
  exact checkedCaptureOverwrite_empty hp r .dyn r .dyn 6 6
    (by simp only [Heap.len, MObj.elems_dyn]; decide)
    (by simp only [Heap.len, MObj.elems_dyn]; decide)

private theorem dc0 : 0 + [false, false].length ≤ hp.len r .dyn := by
  simp only [Heap.len, MObj.elems_dyn]; decide
private theorem dc2 : 2 + [true, true].length ≤ hp.len r .dyn := by
  simp only [Heap.len, MObj.elems_dyn]; decide
/-- Dynamic same-array touching captured intervals also have a concrete changed
heap and instantiate the commutation theorem independently of reference arrays. -/
theorem dynamic_intervals :
    overwriteIntervals hp r .dyn 0 [false, false] dc0 2 [true, true] dc2 =
      overwriteIntervals hp r .dyn 2 [true, true] dc2 0 [false, false] dc0 ∧
    MObj.elems .dyn ((overwriteIntervals hp r .dyn 0 [false, false] dc0 2 [true, true] dc2).get r) =
      [false, false, true, true, false, false] := by
  refine ⟨overwriteIntervals_comm hp r .dyn 0 _ _ 2 _ _ (.inr (.inr (.inl (by decide)))), ?_⟩
  simp only [overwriteIntervals, overwriteSlice_elems, MObj.elems_dyn]
  rfl
private def emptyHeap : Heap H := (⟨[], by decide⟩, ())
/-- Zero-length dynamic objects support two empty operations; an invalid empty
source endpoint fails independently in either stage. -/
theorem zero_length_sequence :
    checkedCaptureSequence emptyHeap r .dyn r .dyn 0 0 0 r .dyn r .dyn 0 0 0 = some emptyHeap ∧
    checkedCaptureSequence emptyHeap r .dyn r .dyn 1 1 0 r .dyn r .dyn 0 0 0 = none ∧
    checkedCaptureSequence emptyHeap r .dyn r .dyn 0 0 0 r .dyn r .dyn 1 1 0 = none := by
  refine ⟨?_, ?_, ?_⟩
  · unfold checkedCaptureSequence
    rw [checkedCaptureOverwrite_empty emptyHeap r .dyn r .dyn 0 0 (Nat.zero_le _) (Nat.zero_le _)]
    exact checkedCaptureOverwrite_empty emptyHeap r .dyn r .dyn 0 0 (Nat.zero_le _) (Nat.zero_le _)
  all_goals
    apply (checkedCaptureSequence_none_iff emptyHeap r .dyn r .dyn _ _ _ r .dyn r .dyn _ _ _).mpr
    simp only [Heap.len, MObj.elems_dyn]
    decide
/-- info: 'Solidity.Backend.MemoryOps.SequentialControls.dynamic_intervals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms dynamic_intervals
/-- info: 'Solidity.Backend.MemoryOps.SequentialControls.zero_length_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms zero_length_sequence

/-- info: 'Solidity.Backend.MemoryOps.SequentialControls.recapture_effect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recapture_effect
/-- info: 'Solidity.Backend.MemoryOps.SequentialControls.recapture_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recapture_negative
/-- info: 'Solidity.Backend.MemoryOps.SequentialControls.read_case_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms read_case_application
/-- info: 'Solidity.Backend.MemoryOps.SequentialControls.checked_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checked_success
/-- info: 'Solidity.Backend.MemoryOps.SequentialControls.isolated_checked_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms isolated_checked_failures
/-- info: 'Solidity.Backend.MemoryOps.SequentialControls.second_failure_intermediate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms second_failure_intermediate
/-- info: 'Solidity.Backend.MemoryOps.SequentialControls.allocator_sequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms allocator_sequence
/-- info: 'Solidity.Backend.MemoryOps.SequentialControls.empty_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_end
end Solidity.Backend.MemoryOps.SequentialControls
