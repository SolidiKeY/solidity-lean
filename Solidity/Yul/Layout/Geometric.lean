import Solidity.Yul.Layout.Geometry

/-!
# The geometry meets the pinned placements and codecs

`geometric` is the direct check that `geometry` transcribes the right-hand
sides of `Shrink.LayoutView.Geometric`. It mentions only the geometry, so it
holds for every allocator.
-/
namespace Solidity.Yul.Layout

open Solidity.Goals
open Solidity.Yul.Views

private theorem toWord_val (w : Roadmap.Word) : Shrink.toWord w.val = w :=
  Fin.ext (Nat.mod_eq_of_lt w.isLt)

private theorem slotField_field (f : Field) : slotField f.width f.offset = some f := by
  unfold slotField
  rw [dif_pos ⟨f.positive, f.fits⟩]

private theorem slotted_ne {r : Shrink.Region} (h : r.slotted) : r ≠ .memory := by
  intro e
  subst e
  exact h

/-- Members that are all scalars are consecutive words, none indirect. -/
private theorem scalar_members (fs : List Shrink.Layout) (i : Nat)
    (all : ∀ f ∈ fs, ∃ w, f = .scalar w) (hi : i < fs.length) :
    memberOffset fs i = 32 * i ∧ (fs[i]?.map indirect).getD 0 = 0 := by
  induction fs generalizing i with
  | nil => cases hi
  | cons f fs ih =>
    obtain ⟨w, rfl⟩ := all _ (List.mem_cons_self ..)
    cases i with
    | zero => exact ⟨rfl, rfl⟩
    | succ i =>
      have step := ih i (fun g hg => all g (List.mem_cons_of_mem _ hg))
        (Nat.lt_of_succ_lt_succ hi)
      refine ⟨?_, ?_⟩
      · simp only [memberOffset, memSize, step.1]
        omega
      · simpa only [List.getElem?_cons_succ] using step.2

/-- **The transcription check**: `geometry` has the pinned scalar codecs and
the pinned length, data, key, element and member placements. -/
theorem geometric
    (a : Shrink.Params → Shrink.Layout → Shrink.Tree → Shrink.Phys → Option (Nat × Shrink.Phys)) :
    (Shrink.LayoutView.mk geometry a).Geometric where
  scalar P r f slot m hr := by
    have h := slotted_ne hr
    refine ⟨?_, ?_, ?_⟩
    · simp only [geometry, if_neg h, slotField_field, Option.map_some, toWord_val]
    · intro v
      simp only [geometry, if_neg h, slotField_field, Option.bind_some, toWord_val, dif_pos v.isLt]
    · intro c
      simp only [geometry, if_neg h, slotField_field, toWord_val]
  memoryScalar P w a m _ _ := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [geometry, if_true]
    · intro v _
      simp only [geometry, if_true]
    · intro c
      simp only [geometry, if_true]
  length P r w n m := by
    by_cases h : r = .memory
    · subst h
      simp only [geometry, if_true, and_self, implies_true]
    · simp only [geometry, if_neg h, and_self, implies_true]
  data P r w m := by
    by_cases h : r = .memory
    · subst h
      simp only [geometry, dataLoc, if_true]
    · simp only [geometry, dataLoc, if_neg h]
  key P r w k _ := rfl
  elem P r w base i _ _ := by
    by_cases h : r = .memory
    · subst h
      simp only [geometry, if_true, memSize, indirect]
    · simp only [geometry, if_neg h]
  elemAggregate P r e base i hr scalar := by
    have h := slotted_ne hr
    cases e with
    | scalar w => exact absurd rfl (scalar w)
    | _ => simp only [geometry, if_neg h]
  field P r fs base i hi := by
    refine ⟨fun hr => ?_, fun hr all => ?_⟩
    · simp only [geometry, if_neg (slotted_ne hr)]
    · have step := scalar_members fs i all hi
      simp only [geometry, if_true, step.1, step.2]

end Solidity.Yul.Layout
