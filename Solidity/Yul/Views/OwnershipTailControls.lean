import Solidity.Yul.Views.OwnershipSequenceControls

namespace Solidity.Yul.Views.Controls

theorem ot_shrink_y_inventory : otShrinkY.next = dynComputed.snapshotInventory dynTestFixed otRaw00 :=
  congrArg (dynComputed.snapshotInventory dynTestFixed) ot_shrink_y_next

theorem ot_grow_y_inventory : otGrowY.next = dynComputed.snapshotInventory dynTestFixed otRaw31 :=
  congrArg (dynComputed.snapshotInventory dynTestFixed) ot_grow_y_next

theorem ot_dead_read (q : Roadmap.Word)
    (outside : q ∉ (dynComputed.snapshotInventory dynTestFixed otRaw00).map ScalarPath.slot) :
    otShrinkY.step.2.cells (complementKey false account q) = otRaw00 q := by
  have absent : ∀ c ∈ otShrinkY.next, c.slot ≠ q := by
    intro c member same
    have found : c.slot ∈ otShrinkY.next.map ScalarPath.slot := List.mem_map.mpr ⟨c,member,rfl⟩
    rw [ot_shrink_y_inventory,same] at found
    exact outside found
  exact (otShrinkY.dead_word rfl q absent).trans (congrFun ot_shrink_y_next q)

theorem ot_empty_inventory_slots : (dynComputed.snapshotInventory dynTestFixed otRaw00).map ScalarPath.slot = [42,42,43,44,45,46] := rfl

theorem ot_dropped_words_are_residual :
    otShrinkY.step.2.cells (complementKey false account 1000) = 12 ∧
    otShrinkY.step.2.cells (complementKey false account 1001) = dynMax ∧
    otShrinkY.step.2.cells (complementKey false account 1002) = 77 ∧
    otShrinkY.step.2.cells (complementKey false account 2000) = 33 :=
  ⟨ot_dead_read 1000 (by rw [ot_empty_inventory_slots]; decide),ot_dead_read 1001 (by rw [ot_empty_inventory_slots]; decide),ot_dead_read 1002 (by rw [ot_empty_inventory_slots]; decide),ot_dead_read 2000 (by rw [ot_empty_inventory_slots]; decide)⟩

theorem ot_regrown_tail_source_read : ∃ v,
    (Source.readCell (E := dynEnv) packedStepFrame ⟨dynName "xs",[.index 2]⟩).run otGrowY.step.1.2 = (.ok v,otGrowY.step.1.2) ∧
    (dynX.element dynTestFixed account 2).codec.encode v = (dynX.element dynTestFixed account 2).field.findWord 77 := by
  have member : dynX.element dynTestFixed account 2 ∈ otGrowY.next := by
    rw [ot_grow_y_inventory]
    have member := dynComputed.snapshot_element_member dynTestFixed otRaw31 dynXTrace 2 (by decide)
    rw [(dynComputed.traceHeader dynXTrace).proof_irrel dynX] at member
    exact member
  obtain ⟨v,read,encoded⟩ := otGrowY.readCell rfl (dynX.element dynTestFixed account 2) member
  refine ⟨v,read,?_⟩
  rw [ot_grow_y_next] at encoded
  exact encoded.trans (congrArg (dynX.element dynTestFixed account 2).field.findWord (show otRaw31 (dynX.element dynTestFixed account 2).slot = 77 from rfl))

theorem ot_regrown_unknown_tail_not_zero :
    (otRaw31 1002 : Roadmap.Word) ≠ 0 := by decide

theorem ot_regrown_max_word : otRaw31 1001 = dynMax := rfl

theorem ot_regrown_both_headers : otRaw31 43 = 3 ∧ otRaw31 45 = 1 := ⟨rfl,rfl⟩

theorem ot_padding_and_unknown_preserved : otRaw31 44 = dynRaw44 ∧ otRaw31 47 = 77 := ⟨rfl,rfl⟩

theorem ot_source_index_success :
    (Source.indexLoc (E := dynEnv) packedStepFrame dynX.reference 2).run otGrowY.step.1.2 =
    (.ok (.stor ⟨dynName "xs",[.index 2]⟩),otGrowY.step.1.2) :=
  dynX.indexLoc packedStepFrame _ 3 ot_lengths_31.1 2

theorem ot_source_panic32 :
    (Source.indexLoc (E := dynEnv) packedStepFrame dynX.reference 3).run otGrowY.step.1.2 =
    (.error (.revert (Source.panicData .index)),otGrowY.step.1.2) :=
  dynX.indexLoc packedStepFrame _ 3 ot_lengths_31.1 3

end Solidity.Yul.Views.Controls
