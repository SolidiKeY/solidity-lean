import Solidity.Yul.Views.NestedDeclarationReset

namespace Solidity.Yul.Views

theorem packed_other_slot_complement {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (t : Bool) (a : Roadmap.Address) (q : Roadmap.Word)
    (different : q ≠ p.request.slot) :
    (applyPackedSlot s p).residual.cells (complementKey t a q) = s.residual.cells (complementKey t a q) :=
  packed_other_complement _ _ _ (fun same => different (congrArg ResidualKey.slot same))

theorem packed_persistent_written_complement {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (tr : p.request.transient = false) :
    (applyPackedSlot s p).residual.cells (complementKey false p.request.address p.request.slot) =
      packedMask (ps p.request.address) (fun _ => p.request.raw) p.request.slot := by
  have key : complementKey false p.request.address p.request.slot = p.residualUpdate.1 := by
    change complementKey false _ _ = complementKey p.request.transient _ _
    rw [tr]
  calc
    _ = (applyPackedSlot s p).residual.cells p.residualUpdate.1 :=
      congrArg (applyPackedSlot s p).residual.cells key
    _ = p.residualUpdate.2 := residualSave_get _ _ _
    _ = _ := by
      unfold PackedSlotPlan.residualUpdate packedCarrierOwns packedMask
      simp only [complementKey,tr,Bool.false_eq_true,if_false]

end Solidity.Yul.Views

namespace Solidity.Yul.Views.Controls

theorem nested_actual_residual_snapshot :
    (fun q => nestedCallerCore.residual.cells (complementKey false account q)) = nestedStore.2 := by
  have req4 : nestedPlan4.request = ⟨false,account,4,nestedRaw4⟩ := preparePackedSlot_request _ _ (Option.get_mem nested_slot4_ready)
  have req5 : nestedPlan5.request = ⟨false,account,5,nestedRaw5⟩ := preparePackedSlot_request _ _ (Option.get_mem nested_slot5_ready)
  have req6 : nestedPlan6.request = ⟨false,account,6,nestedRaw6⟩ := preparePackedSlot_request _ _ (Option.get_mem nested_slot6_ready)
  have set4 := packed_persistent_written_complement nestedInitialCore nestedPlan4 (by rw [req4])
  have set5 := packed_persistent_written_complement (applyPackedSlot nestedInitialCore nestedPlan4) nestedPlan5 (by rw [req5])
  have set6 := packed_persistent_written_complement (applyPackedSlot (applyPackedSlot nestedInitialCore nestedPlan4) nestedPlan5) nestedPlan6 (by rw [req6])
  simp only [req4] at set4
  simp only [req5] at set5
  simp only [req6] at set6
  funext q
  rw [nested_actual_source_sequence.1]
  simp only [runPackedSlots]
  change _ = packedMask nestedDeclCert.registrations nestedSnapshot q
  by_cases q4 : q = 4
  · subst q
    rw [packed_other_slot_complement _ nestedPlan6 false account 4 (by rw [req6]; decide),
      packed_other_slot_complement _ nestedPlan5 false account 4 (by rw [req5]; decide),set4]
    rfl
  · by_cases q5 : q = 5
    · subst q
      rw [packed_other_slot_complement _ nestedPlan6 false account 5 (by rw [req6]; decide),set5]
      rfl
    · by_cases q6 : q = 6
      · subst q
        rw [set6]
        rfl
      · rw [packed_other_slot_complement _ nestedPlan6 false account q (by rw [req6]; exact q6),
          packed_other_slot_complement _ nestedPlan5 false account q (by rw [req5]; exact q5),
          packed_other_slot_complement _ nestedPlan4 false account q (by rw [req4]; exact q4)]
        unfold nestedInitialCore nestedDeclResidual initialPackedComplement
        change complementWord (packedOwnsByte nestedDeclCert.registrations q) (nestedInitialRaw q) =
          complementWord (packedOwnsByte nestedDeclCert.registrations q) (nestedSnapshot q)
        simp only [nestedSnapshot,if_neg q4,if_neg q5,if_neg q6]

theorem nested_actual_whole_physical_snapshot :
    finiteEncode nestedDeclCert.registrations (nestedFrame6.1.2.2.ex.world.accounts account).storage
      (fun q => nestedCallerCore.residual.cells (complementKey false account q)) = some nestedSnapshot := by
  rw [nested_actual_residual_snapshot]
  exact nested_actual_source_full_reencoding

theorem nested_all_transient_defaults_checked : scalarZeroDefaultCheck (nestedDeclRegistry account) = true := by decide

theorem nested_all_transient_raw_reset (q : Roadmap.Word) :
    reencodeTransientSlot nestedDeclRegistry (companionEndTx nestedChildCore) account q = some 0 := by
  apply packedEndTx_transient
  intro c member
  exact scalarZeroDefaultCheck_sound _ nested_all_transient_defaults_checked c ((selectedSlotPaths_mem _ _ c).mp member).1

end Solidity.Yul.Views.Controls
