import Solidity.Yul.Views.InheritedDeclarationJournal

namespace Solidity.Yul.Views.Controls

theorem diamond_actual_residual_snapshot :
    (fun q => diamondCallerCore.residual.cells (complementKey false account q)) = diamondStore.2 := by
  have req0 : diamondPlan0.request = ⟨false,account,0,diamondRaw0⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready0)
  have set0 := packed_persistent_written_complement diamondInitialCore diamondPlan0 (by rw [req0])
  rw [← diamondCore0_step] at set0
  simp only [req0] at set0
  change diamondCore0.residual.cells (complementKey false account 0) = packedMask diamondChecked.registrations diamondSnapshot 0 at set0
  have req1 : diamondPlan1.request = ⟨false,account,1,diamondRaw1⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready1)
  have set1 := packed_persistent_written_complement diamondCore0 diamondPlan1 (by rw [req1])
  rw [← diamondCore1_step] at set1
  simp only [req1] at set1
  change diamondCore1.residual.cells (complementKey false account 1) = packedMask diamondChecked.registrations diamondSnapshot 1 at set1
  have req2 : diamondPlan2.request = ⟨false,account,2,diamondRaw2⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready2)
  have set2 := packed_persistent_written_complement diamondCore1 diamondPlan2 (by rw [req2])
  rw [← diamondCore2_step] at set2
  simp only [req2] at set2
  change diamondCore2.residual.cells (complementKey false account 2) = packedMask diamondChecked.registrations diamondSnapshot 2 at set2
  have req3 : diamondPlan3.request = ⟨false,account,3,diamondRaw3⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready3)
  have set3 := packed_persistent_written_complement diamondCore2 diamondPlan3 (by rw [req3])
  rw [← diamondCore3_step] at set3
  simp only [req3] at set3
  change diamondCore3.residual.cells (complementKey false account 3) = packedMask diamondChecked.registrations diamondSnapshot 3 at set3
  have req4 : diamondPlan4.request = ⟨false,account,4,diamondRaw4⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready4)
  have set4 := packed_persistent_written_complement diamondCore3 diamondPlan4 (by rw [req4])
  rw [← diamondCore4_step] at set4
  simp only [req4] at set4
  change diamondCore4.residual.cells (complementKey false account 4) = packedMask diamondChecked.registrations diamondSnapshot 4 at set4
  have req5 : diamondPlan5.request = ⟨false,account,5,diamondRaw5⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready5)
  have set5 := packed_persistent_written_complement diamondCore4 diamondPlan5 (by rw [req5])
  rw [← diamondCore5_step] at set5
  simp only [req5] at set5
  change diamondCore5.residual.cells (complementKey false account 5) = packedMask diamondChecked.registrations diamondSnapshot 5 at set5
  have req6 : diamondPlan6.request = ⟨false,account,6,diamondRaw6⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready6)
  have set6 := packed_persistent_written_complement diamondCore5 diamondPlan6 (by rw [req6])
  rw [← diamondCore6_step] at set6
  simp only [req6] at set6
  change diamondCore6.residual.cells (complementKey false account 6) = packedMask diamondChecked.registrations diamondSnapshot 6 at set6
  funext q
  change diamondCore6.residual.cells (complementKey false account q) = packedMask diamondChecked.registrations diamondSnapshot q
  by_cases q0 : q = 0
  · subst q
    rw [diamondCore6_step,
      packed_other_slot_complement _ diamondPlan6 false account 0 (by rw [req6]; decide),
      diamondCore5_step,
      packed_other_slot_complement _ diamondPlan5 false account 0 (by rw [req5]; decide),
      diamondCore4_step,
      packed_other_slot_complement _ diamondPlan4 false account 0 (by rw [req4]; decide),
      diamondCore3_step,
      packed_other_slot_complement _ diamondPlan3 false account 0 (by rw [req3]; decide),
      diamondCore2_step,
      packed_other_slot_complement _ diamondPlan2 false account 0 (by rw [req2]; decide),
      diamondCore1_step,
      packed_other_slot_complement _ diamondPlan1 false account 0 (by rw [req1]; decide),
      set0]
  ·
    by_cases q1 : q = 1
    · subst q
      rw [diamondCore6_step,
        packed_other_slot_complement _ diamondPlan6 false account 1 (by rw [req6]; decide),
        diamondCore5_step,
        packed_other_slot_complement _ diamondPlan5 false account 1 (by rw [req5]; decide),
        diamondCore4_step,
        packed_other_slot_complement _ diamondPlan4 false account 1 (by rw [req4]; decide),
        diamondCore3_step,
        packed_other_slot_complement _ diamondPlan3 false account 1 (by rw [req3]; decide),
        diamondCore2_step,
        packed_other_slot_complement _ diamondPlan2 false account 1 (by rw [req2]; decide),
        set1]
    ·
      by_cases q2 : q = 2
      · subst q
        rw [diamondCore6_step,
          packed_other_slot_complement _ diamondPlan6 false account 2 (by rw [req6]; decide),
          diamondCore5_step,
          packed_other_slot_complement _ diamondPlan5 false account 2 (by rw [req5]; decide),
          diamondCore4_step,
          packed_other_slot_complement _ diamondPlan4 false account 2 (by rw [req4]; decide),
          diamondCore3_step,
          packed_other_slot_complement _ diamondPlan3 false account 2 (by rw [req3]; decide),
          set2]
      ·
        by_cases q3 : q = 3
        · subst q
          rw [diamondCore6_step,
            packed_other_slot_complement _ diamondPlan6 false account 3 (by rw [req6]; decide),
            diamondCore5_step,
            packed_other_slot_complement _ diamondPlan5 false account 3 (by rw [req5]; decide),
            diamondCore4_step,
            packed_other_slot_complement _ diamondPlan4 false account 3 (by rw [req4]; decide),
            set3]
        ·
          by_cases q4 : q = 4
          · subst q
            rw [diamondCore6_step,
              packed_other_slot_complement _ diamondPlan6 false account 4 (by rw [req6]; decide),
              diamondCore5_step,
              packed_other_slot_complement _ diamondPlan5 false account 4 (by rw [req5]; decide),
              set4]
          ·
            by_cases q5 : q = 5
            · subst q
              rw [diamondCore6_step,
                packed_other_slot_complement _ diamondPlan6 false account 5 (by rw [req6]; decide),
                set5]
            ·
              by_cases q6 : q = 6
              · subst q
                rw [set6]
              ·
                rw [diamondCore6_step,
                  packed_other_slot_complement _ diamondPlan6 false account q (by rw [req6]; exact q6),
                  diamondCore5_step,
                  packed_other_slot_complement _ diamondPlan5 false account q (by rw [req5]; exact q5),
                  diamondCore4_step,
                  packed_other_slot_complement _ diamondPlan4 false account q (by rw [req4]; exact q4),
                  diamondCore3_step,
                  packed_other_slot_complement _ diamondPlan3 false account q (by rw [req3]; exact q3),
                  diamondCore2_step,
                  packed_other_slot_complement _ diamondPlan2 false account q (by rw [req2]; exact q2),
                  diamondCore1_step,
                  packed_other_slot_complement _ diamondPlan1 false account q (by rw [req1]; exact q1),
                  diamondCore0_step,
                  packed_other_slot_complement _ diamondPlan0 false account q (by rw [req0]; exact q0)]
                unfold diamondInitialCore diamondResidual initialPackedComplement
                change complementWord (packedOwnsByte diamondChecked.registrations q) (diamondInitialRaw q) =
                  complementWord (packedOwnsByte diamondChecked.registrations q) (diamondSnapshot q)
                simp only [diamondSnapshot,if_neg q0,if_neg q1,if_neg q2,if_neg q3,if_neg q4,if_neg q5,if_neg q6]

theorem diamond_actual_whole_physical_snapshot : finiteEncode diamondChecked.registrations
    (diamondFrame6.1.2.2.ex.world.accounts account).storage
    (fun q => diamondCallerCore.residual.cells (complementKey false account q)) = some diamondSnapshot := by
  rw [diamond_actual_residual_snapshot]
  exact diamond_actual_full_reencode

end Solidity.Yul.Views.Controls
