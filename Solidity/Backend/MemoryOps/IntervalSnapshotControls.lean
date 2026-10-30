import Solidity.Backend.MemoryOps.SequentialTransport
import Solidity.Backend.MemoryOps.CalldataChildControls

/-! Same-array fixed reference writes, both overlap directions, touching/empty
intervals, real typed observations and reuse of an existing child certificate. -/
namespace Solidity.Backend.MemoryOps.IntervalControls
private abbrev B := BoolChildRef
private abbrev P : RefTy := .fixed (.ref B) 4
private abbrev H : HTy := [B, B, P]
private def first : HRef H B := ⟨0, rfl⟩
private def second : HRef H B := ⟨1, rfl⟩
private def parent : HRef H P := ⟨2, rfl⟩
private def hp : Heap H := (⟨[true], by decide⟩, ⟨[false], by decide⟩,
  ⟨[first, second, first, second], rfl⟩, ())
private theorem cap (d : Nat) (xs : List (HRef H B)) (h : d + xs.length ≤ 4) :
    d + xs.length ≤ hp.len parent .fixed := by
  simp only [Heap.len, MObj.elems_fixed]
  change d + xs.length ≤ 4
  exact h
private def out := overwriteIntervals hp parent .fixed 0 [second] (cap _ _ (by decide))
  3 [first] (cap _ _ (by decide))
private def rev := overwriteIntervals hp parent .fixed 3 [first] (cap _ _ (by decide))
  0 [second] (cap _ _ (by decide))
private theorem apart : IntervalsApart 0 [second].length 3 [first].length :=
  .inr (.inr (.inl (by decide)))

/-- Two nonempty same-object reference writes commute with actual changed slots. -/
theorem same_object_comm : out = rev :=
  overwriteIntervals_comm hp parent .fixed 0 [second] (cap _ _ (by decide))
    3 [first] (cap _ _ (by decide)) apart

theorem changed_references :
    (MObj.elems .fixed (out.get parent)).map HRef.id = [1, 1, 0, 0] ∧
    out.get first = hp.get first ∧ out.get second = hp.get second := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [out, overwriteIntervals, overwriteSlice_elems, MObj.elems_fixed]
    rfl
  · exact overwriteIntervals_frame hp parent .fixed 0 [second] (cap _ _ (by decide))
      3 [first] (cap _ _ (by decide)) first (by decide)
  · exact overwriteIntervals_frame hp parent .fixed 0 [second] (cap _ _ (by decide))
      3 [first] (cap _ _ (by decide)) second (by decide)

/-- Touching nonempty intervals are separated; an empty interval may be inside
another interval, and an empty write at the exact end is identity. -/
theorem touching_empty :
    overwriteIntervals hp parent .fixed 0 [second, second] (cap _ _ (by decide))
      2 [first, first] (cap _ _ (by decide)) =
    overwriteIntervals hp parent .fixed 2 [first, first] (cap _ _ (by decide))
      0 [second, second] (cap _ _ (by decide)) ∧
    overwriteIntervals hp parent .fixed 1 [] (cap _ _ (by decide))
      0 [second, first] (cap _ _ (by decide)) =
    overwriteIntervals hp parent .fixed 0 [second, first] (cap _ _ (by decide))
      1 [] (cap _ _ (by decide)) ∧
    overwriteSlice hp parent .fixed 4 [] (cap _ _ (by decide)) = hp :=
  ⟨overwriteIntervals_comm hp parent .fixed 0 _ _ 2 _ _ (.inr (.inr (.inl (by decide)))),
    overwriteIntervals_comm hp parent .fixed 1 _ _ 0 _ _ (.inl rfl),
    overwriteSlice_empty hp parent .fixed 4 _⟩

private theorem bound (s t : Nat) (ho : s ≤ t) (ht : t ≤ 4) : SliceBounds (hp.len parent .fixed) s t := by
  refine ⟨ho, ?_⟩
  simp only [Heap.len, MObj.elems_fixed]
  change t ≤ 4
  exact ht
private theorem room (d s t : Nat) (h : d + (t - s) ≤ 4) : d + (t - s) ≤ hp.len parent .fixed := by
  simp only [Heap.len, MObj.elems_fixed]
  change d + (t - s) ≤ 4
  exact h
private def overlap := captureTwice hp parent .fixed 0 3 1 (bound _ _ (by decide) (by decide))
  (room _ _ _ (by decide)) 1 4 0 (bound _ _ (by decide) (by decide)) (room _ _ _ (by decide))

/-- Right-overlap then left-overlap recapture actual reference values; children
stay intact and the checked sequence succeeds on its real intermediate heap. -/
theorem both_overlaps :
    (MObj.elems .fixed (overlap.get parent)).map HRef.id = [0, 1, 0, 0] ∧
    overlap.get first = hp.get first ∧ overlap.get second = hp.get second ∧
    checkedCaptureSequence hp parent .fixed parent .fixed 0 3 1 parent .fixed parent .fixed 1 4 0 = some overlap := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [overlap, captureTwice, captureOverwrite, overwriteSlice_elems, sliceElems, MObj.elems_fixed]
    rfl
  · exact captureTwice_frame hp parent .fixed 0 3 1 _ _ 1 4 0 _ _ first (by decide)
  · exact captureTwice_frame hp parent .fixed 0 3 1 _ _ 1 4 0 _ _ second (by decide)
  · exact captureTwice_checked hp parent .fixed 0 3 1 _ _ 1 4 0 _ _

/-- Mutually noninterfering source intervals make true sequential commutation
inhabited; both one-element reference copies change the parent. -/
theorem noninterfering_sequence :
    captureTwice hp parent .fixed 0 1 1 (bound _ _ (by decide) (by decide)) (room _ _ _ (by decide))
      2 3 3 (bound _ _ (by decide) (by decide)) (room _ _ _ (by decide)) =
    captureTwice hp parent .fixed 2 3 3 (bound _ _ (by decide) (by decide)) (room _ _ _ (by decide))
      0 1 1 (bound _ _ (by decide) (by decide)) (room _ _ _ (by decide)) :=
  captureTwice_comm hp parent .fixed 0 1 1 _ _ 2 3 3 _ _
    (.inr (.inr (.inl (by decide)))) (.inr (.inr (.inr (by decide)))) (.inr (.inr (.inl (by decide))))

/-- The different-object source law is exercised with a different element type. -/
theorem other_source :
    sliceElems (captureOverwrite hp parent .fixed parent .fixed 0 3 1
      (bound _ _ (by decide) (by decide)) (room _ _ _ (by decide))) first .dyn 0 1 =
      sliceElems hp first .dyn 0 1 :=
  captureOverwrite_source_other hp parent .fixed parent .fixed 0 3 1 _ _ first .dyn 0 1 (by decide)

private abbrev Γ : Ctx := [.mem P]
private def state : State StandardExample Γ :=
  {storage := Storage.init StandardExample, H := H, heap := hp, env := (some parent, ())}
private def zero : Val StandardExample Γ .uint := .simple (.lit 0 (by decide))
private def path : MPath StandardExample Γ (.prim .bool) :=
  .loc (.index .dyn (.loc (.index .fixed (.var .here rfl) zero)) zero)
/-- Published MPath observations agree for the two actual write orders. -/
theorem typed_path_order : path.mvalT {state with heap := out} = path.mvalT {state with heap := rev} :=
  overwriteIntervals_path state parent .fixed 0 [second] (cap _ _ (by decide))
    3 [first] (cap _ _ (by decide)) apart path
private def indexZero : PrimTy.uint.Denote := ⟨0, by decide⟩
/-- The redirected parent and its leaf have actual successful typed reads. -/
theorem actual_nested_read : out.index parent .fixed indexZero = some second ∧
    out.index second .dyn indexZero = some false := by
  constructor
  · simp only [Heap.index, out, overwriteIntervals, overwriteSlice_elems, MObj.elems_fixed]
    rfl
  · have he := changed_references.2.2
    simp only [Heap.index, he, MObj.elems_dyn]
    rfl

/-- Reuse the prior proved child/source certificate. No new immutable source
entries are invented; the same represented child survives two changed slots. -/
theorem existing_child_integration :
    ∃ (D : Source.Layout) (H : HTy) (c : Source.Calldata D) (address : Nat → Nat)
      (hp hq : Heap H) (s : Source.Data D BoolChildTy) (r : HRef H BoolChildRef)
      (dst : HRef H (.array (.ref BoolChildRef))) (value : HRef H BoolChildRef)
      (ha : 0 + [value].length ≤ hp.len dst .dyn) (hb : 2 + [value].length ≤ hp.len dst .dyn),
      hq = overwriteIntervals hp dst .dyn 0 [value] ha 2 [value] hb ∧
      BoolChildRepr c address hp s r ∧ BoolChildRepr c address hq s r ∧
      (MObj.elems .dyn (hp.get dst)).map HRef.id = [1, 0, 1] ∧
      (MObj.elems .dyn (hq.get dst)).map HRef.id = [0, 0, 0] := by
  have hr := ChildControls.changed_shared.2.2
  have hf := hr.overwriteIntervals ⟨2, rfl⟩ .dyn 0 [⟨0, rfl⟩] (by decide +kernel)
    2 [⟨0, rfl⟩] (by decide +kernel) (by decide)
  refine ⟨_, _, _, _, _, _, _, _, ⟨2, rfl⟩, ⟨0, rfl⟩,
    (by decide +kernel), (by decide +kernel), rfl, hr, hf, ChildControls.changed_shared.2.1, ?_⟩
  simp only [overwriteIntervals, overwriteSlice_elems, ← replaceSlice_map]
  decide +kernel

/-- Overlap remains a supported operation but cannot generally commute. -/
theorem overlapping_writes_negative :
    overwriteIntervals hp parent .fixed 0 [second] (cap _ _ (by decide))
      0 [first] (cap _ _ (by decide)) ≠
    overwriteIntervals hp parent .fixed 0 [first] (cap _ _ (by decide))
      0 [second] (cap _ _ (by decide)) := by
  intro h
  have he := congrArg (fun h : Heap H => (MObj.elems .fixed (h.get parent)).map HRef.id) h
  simp only [overwriteIntervals, overwriteSlice_elems, MObj.elems_fixed] at he
  change [0, 1, 0, 1] = [1, 1, 0, 1] at he
  cases he
/-- info: 'Solidity.Backend.MemoryOps.IntervalControls.overlapping_writes_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overlapping_writes_negative

/-- info: 'Solidity.Backend.MemoryOps.IntervalControls.same_object_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms same_object_comm
/-- info: 'Solidity.Backend.MemoryOps.IntervalControls.changed_references' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms changed_references
/-- info: 'Solidity.Backend.MemoryOps.IntervalControls.touching_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms touching_empty
/-- info: 'Solidity.Backend.MemoryOps.IntervalControls.both_overlaps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms both_overlaps
/-- info: 'Solidity.Backend.MemoryOps.IntervalControls.noninterfering_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms noninterfering_sequence
/-- info: 'Solidity.Backend.MemoryOps.IntervalControls.other_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms other_source
/-- info: 'Solidity.Backend.MemoryOps.IntervalControls.typed_path_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms typed_path_order
/-- info: 'Solidity.Backend.MemoryOps.IntervalControls.actual_nested_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_nested_read
/-- info: 'Solidity.Backend.MemoryOps.IntervalControls.existing_child_integration' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms existing_child_integration
end Solidity.Backend.MemoryOps.IntervalControls
