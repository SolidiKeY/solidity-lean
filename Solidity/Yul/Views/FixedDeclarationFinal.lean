import Solidity.Yul.Views.FixedDeclarationReads

namespace Solidity.Yul.Views.Controls

theorem recursive_actual_residual_snapshot :
    (fun q => recursiveCallerCore.residual.cells (complementKey false account q)) = recursiveStore.2 := by
  have req8 : recursivePlan8.request = ⟨false,account,8,recursiveRaw8⟩ := preparePackedSlot_request _ _ (Option.get_mem recursive_ready8)
  have set8 := packed_persistent_written_complement recursiveInitialCore recursivePlan8 (by rw [req8])
  simp only [req8] at set8
  change (applyPackedSlot recursiveInitialCore recursivePlan8).residual.cells (complementKey false account 8) =
    packedMask recursiveChecked.registrations recursiveSnapshot 8 at set8
  have req9 : recursivePlan9.request = ⟨false,account,9,recursiveRaw9⟩ := preparePackedSlot_request _ _ (Option.get_mem recursive_ready9)
  have set9 := packed_persistent_written_complement (⟨recursiveFrame8.1.2.2.ex,recursiveFrame8.2⟩ : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership) recursivePlan9 (by rw [req9])
  simp only [req9] at set9
  change (applyPackedSlot (applyPackedSlot recursiveInitialCore recursivePlan8) recursivePlan9).residual.cells (complementKey false account 9) =
    packedMask recursiveChecked.registrations recursiveSnapshot 9 at set9
  have req10 : recursivePlan10.request = ⟨false,account,10,recursiveRaw10⟩ := preparePackedSlot_request _ _ (Option.get_mem recursive_ready10)
  have set10 := packed_persistent_written_complement (⟨recursiveFrame9.1.2.2.ex,recursiveFrame9.2⟩ : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership) recursivePlan10 (by rw [req10])
  simp only [req10] at set10
  change (applyPackedSlot (applyPackedSlot (applyPackedSlot recursiveInitialCore recursivePlan8) recursivePlan9) recursivePlan10).residual.cells (complementKey false account 10) =
    packedMask recursiveChecked.registrations recursiveSnapshot 10 at set10
  have req11 : recursivePlan11.request = ⟨false,account,11,recursiveRaw11⟩ := preparePackedSlot_request _ _ (Option.get_mem recursive_ready11)
  have set11 := packed_persistent_written_complement (⟨recursiveFrame10.1.2.2.ex,recursiveFrame10.2⟩ : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership) recursivePlan11 (by rw [req11])
  simp only [req11] at set11
  change (applyPackedSlot (applyPackedSlot (applyPackedSlot (applyPackedSlot recursiveInitialCore recursivePlan8) recursivePlan9) recursivePlan10) recursivePlan11).residual.cells (complementKey false account 11) =
    packedMask recursiveChecked.registrations recursiveSnapshot 11 at set11
  have req12 : recursivePlan12.request = ⟨false,account,12,recursiveRaw12⟩ := preparePackedSlot_request _ _ (Option.get_mem recursive_ready12)
  have set12 := packed_persistent_written_complement (⟨recursiveFrame11.1.2.2.ex,recursiveFrame11.2⟩ : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership) recursivePlan12 (by rw [req12])
  simp only [req12] at set12
  change (applyPackedSlot (applyPackedSlot (applyPackedSlot (applyPackedSlot (applyPackedSlot recursiveInitialCore recursivePlan8) recursivePlan9) recursivePlan10) recursivePlan11) recursivePlan12).residual.cells (complementKey false account 12) =
    packedMask recursiveChecked.registrations recursiveSnapshot 12 at set12
  have req13 : recursivePlan13.request = ⟨false,account,13,recursiveRaw13⟩ := preparePackedSlot_request _ _ (Option.get_mem recursive_ready13)
  have set13 := packed_persistent_written_complement (⟨recursiveFrame12.1.2.2.ex,recursiveFrame12.2⟩ : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership) recursivePlan13 (by rw [req13])
  simp only [req13] at set13
  change (applyPackedSlot (applyPackedSlot (applyPackedSlot (applyPackedSlot (applyPackedSlot (applyPackedSlot recursiveInitialCore recursivePlan8) recursivePlan9) recursivePlan10) recursivePlan11) recursivePlan12) recursivePlan13).residual.cells (complementKey false account 13) =
    packedMask recursiveChecked.registrations recursiveSnapshot 13 at set13
  funext q
  rw [recursive_actual_sequence]
  simp only [runPackedSlots]
  change _ = packedMask recursiveChecked.registrations recursiveSnapshot q
  by_cases q8 : q = 8
  · subst q
    rw [packed_other_slot_complement _ recursivePlan13 false account 8 (by rw [req13]; decide),
      packed_other_slot_complement _ recursivePlan12 false account 8 (by rw [req12]; decide),
      packed_other_slot_complement _ recursivePlan11 false account 8 (by rw [req11]; decide),
      packed_other_slot_complement _ recursivePlan10 false account 8 (by rw [req10]; decide),
      packed_other_slot_complement _ recursivePlan9 false account 8 (by rw [req9]; decide),
      set8]
  ·
    by_cases q9 : q = 9
    · subst q
      rw [packed_other_slot_complement _ recursivePlan13 false account 9 (by rw [req13]; decide),
        packed_other_slot_complement _ recursivePlan12 false account 9 (by rw [req12]; decide),
        packed_other_slot_complement _ recursivePlan11 false account 9 (by rw [req11]; decide),
        packed_other_slot_complement _ recursivePlan10 false account 9 (by rw [req10]; decide),
        set9]
    ·
      by_cases q10 : q = 10
      · subst q
        rw [packed_other_slot_complement _ recursivePlan13 false account 10 (by rw [req13]; decide),
          packed_other_slot_complement _ recursivePlan12 false account 10 (by rw [req12]; decide),
          packed_other_slot_complement _ recursivePlan11 false account 10 (by rw [req11]; decide),
          set10]
      ·
        by_cases q11 : q = 11
        · subst q
          rw [packed_other_slot_complement _ recursivePlan13 false account 11 (by rw [req13]; decide),
            packed_other_slot_complement _ recursivePlan12 false account 11 (by rw [req12]; decide),
            set11]
        ·
          by_cases q12 : q = 12
          · subst q
            rw [packed_other_slot_complement _ recursivePlan13 false account 12 (by rw [req13]; decide),
              set12]
          ·
            by_cases q13 : q = 13
            · subst q
              rw [set13]
            ·
              rw [packed_other_slot_complement _ recursivePlan13 false account q (by rw [req13]; exact q13),
                packed_other_slot_complement _ recursivePlan12 false account q (by rw [req12]; exact q12),
                packed_other_slot_complement _ recursivePlan11 false account q (by rw [req11]; exact q11),
                packed_other_slot_complement _ recursivePlan10 false account q (by rw [req10]; exact q10),
                packed_other_slot_complement _ recursivePlan9 false account q (by rw [req9]; exact q9),
                packed_other_slot_complement _ recursivePlan8 false account q (by rw [req8]; exact q8)]
              unfold recursiveInitialCore recursiveResidual initialPackedComplement
              change complementWord (packedOwnsByte recursiveChecked.registrations q) (recursiveInitialRaw q) =
                complementWord (packedOwnsByte recursiveChecked.registrations q) (recursiveSnapshot q)
              simp only [recursiveSnapshot,if_neg q8,if_neg q9,if_neg q10,if_neg q11,if_neg q12,if_neg q13]

theorem recursive_actual_whole_physical_snapshot :
    finiteEncode recursiveChecked.registrations (recursiveFrame13.1.2.2.ex.world.accounts account).storage
      (fun q => recursiveCallerCore.residual.cells (complementKey false account q)) = some recursiveSnapshot := by
  rw [recursive_actual_residual_snapshot]
  exact recursive_actual_full_map_reencode

end Solidity.Yul.Views.Controls
