import Solidity.Yul.Views.ComputedSnapshotReads
import Solidity.Yul.Views.DynamicFrameLaws

namespace Solidity.Yul.Views

/-- Only slots touched by the write or either actual inventory can change
complement interpretation. Duplicates are harmless; no arbitrary domain cap. -/
def ownershipSupport {D L} (old next : List (ScalarPath D L)) (written : Roadmap.Word) : List Roadmap.Word :=
  written :: old.map ScalarPath.slot ++ next.map ScalarPath.slot

def ownershipUpdates (tr : Bool) (a : Roadmap.Address) (slots : List Roadmap.Word) (m : SlotView) :=
  slots.map (fun q => (complementKey tr a q,m q))

theorem residualRun_values {Own : ResidualOwnership} (r : ResidualJournal Own)
    (keys : List (ResidualKey Own)) (values : ResidualKey Own → Roadmap.Word) (q : ResidualKey Own) :
    (residualRun r (keys.map (fun k => (k,values k)))).cells q = if q ∈ keys then values q else r.cells q := by
  induction keys generalizing r with
  | nil => rfl
  | cons k keys ih =>
    rw [List.map_cons,residualRun,ih]
    by_cases tail : q ∈ keys
    · simp only [tail,List.mem_cons,or_true,if_true]
    · simp only [tail,List.mem_cons,or_false,if_false]
      by_cases same : q = k
      · subst q
        rw [if_pos rfl]
        exact residualSave_get _ _ _
      · rw [if_neg same]
        exact residualSave_other _ _ _ _ same

theorem ownershipUpdates_slice (r : ResidualJournal complementCarrierOwnership)
    (tr : Bool) (a : Roadmap.Address) (slots : List Roadmap.Word) (m : SlotView) (q : Roadmap.Word) :
    (residualRun r (ownershipUpdates tr a slots m)).cells (complementKey tr a q) =
      if q ∈ slots then m q else r.cells (complementKey tr a q) := by
  have mapped : ownershipUpdates tr a slots m =
      (slots.map (complementKey tr a)).map (fun k => (k,m k.slot)) := by rw [List.map_map]; rfl
  rw [mapped,residualRun_values]
  have member : complementKey tr a q ∈ slots.map (complementKey tr a) ↔ q ∈ slots := by
    constructor
    · intro h
      obtain ⟨k,km,same⟩ := List.mem_map.mp h
      have equal : k = q := congrArg ResidualKey.slot same
      exact equal ▸ km
    · intro h; exact List.mem_map.mpr ⟨q,h,rfl⟩
  simp only [member]
  rfl

theorem packedMask_unowned_slot {D L} (cs : List (ScalarPath D L)) (m : SlotView) (q : Roadmap.Word)
    (outside : ∀ c ∈ cs, c.slot ≠ q) : packedMask cs m q = m q := by
  apply word_eq_of_lowBytes
  intro i
  apply packedMask_residual
  cases flag : packedOwnsByte cs q i
  · rfl
  · obtain ⟨c,member,same,_⟩ := (packedOwnsByte_iff _ _ _).mp flag
    exact False.elim (outside c member same)

/-- The complete OLD physical map comes from actual typed encoding over the
old journal slice. No final map equality/transport law is assumed. -/
theorem ownership_transport_slice {D L} (old next : List (ScalarPath D L))
    (store : Source.Storage D L) (r : ResidualJournal complementCarrierOwnership)
    (tr : Bool) (a : Roadmap.Address) (raw : SlotView)
    (encoded : finiteEncode old store (fun q => r.cells (complementKey tr a q)) = some raw)
    (written value : Roadmap.Word) :
    (fun q => (residualRun r (ownershipUpdates tr a (ownershipSupport old next written)
      (packedMask next (saveSlot raw written value)))).cells (complementKey tr a q)) =
      packedMask next (saveSlot raw written value) := by
  funext q
  rw [ownershipUpdates_slice]
  split
  · rfl
  · rename_i outside
    have notWritten : q ≠ written := fun same => outside (List.mem_cons.mpr (Or.inl same))
    have notOld : ∀ c ∈ old, c.slot ≠ q := by
      intro c member same
      apply outside
      apply List.mem_cons.mpr
      exact Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨c,member,same⟩))
    have notNext : ∀ c ∈ next, c.slot ≠ q := by
      intro c member same
      apply outside
      apply List.mem_cons.mpr
      exact Or.inr (List.mem_append_right _ (List.mem_map.mpr ⟨c,member,same⟩))
    rw [packedMask_unowned_slot next _ q notNext,find_saveSlot_other _ _ _ _ notWritten]
    exact (finiteEncode_unowned_slot old store _ raw encoded q notOld).symm

end Solidity.Yul.Views
