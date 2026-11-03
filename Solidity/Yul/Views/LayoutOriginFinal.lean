import Solidity.Yul.Views.LayoutOriginJournal

namespace Solidity.Yul.Views.Controls

theorem origin_actual_residual_snapshot :
    (fun q => originCallerCore.residual.cells (complementKey false account q)) = originStore.2 := by
  have req0 : originPlan0.request = ⟨false,account,42,originRaw0⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready0)
  have set0 := packed_persistent_written_complement originInitialCore originPlan0 (by rw [req0])
  rw [← originCore0_step] at set0
  simp only [req0] at set0
  change originCore0.residual.cells (complementKey false account 42) = packedMask originChecked.registrations originSnapshot 42 at set0
  have req1 : originPlan1.request = ⟨false,account,43,originRaw1⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready1)
  have set1 := packed_persistent_written_complement originCore0 originPlan1 (by rw [req1])
  rw [← originCore1_step] at set1
  simp only [req1] at set1
  change originCore1.residual.cells (complementKey false account 43) = packedMask originChecked.registrations originSnapshot 43 at set1
  have req2 : originPlan2.request = ⟨false,account,44,originRaw2⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready2)
  have set2 := packed_persistent_written_complement originCore1 originPlan2 (by rw [req2])
  rw [← originCore2_step] at set2
  simp only [req2] at set2
  change originCore2.residual.cells (complementKey false account 44) = packedMask originChecked.registrations originSnapshot 44 at set2
  have req3 : originPlan3.request = ⟨false,account,45,originRaw3⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready3)
  have set3 := packed_persistent_written_complement originCore2 originPlan3 (by rw [req3])
  rw [← originCore3_step] at set3
  simp only [req3] at set3
  change originCore3.residual.cells (complementKey false account 45) = packedMask originChecked.registrations originSnapshot 45 at set3
  have req4 : originPlan4.request = ⟨false,account,46,originRaw4⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready4)
  have set4 := packed_persistent_written_complement originCore3 originPlan4 (by rw [req4])
  rw [← originCore4_step] at set4
  simp only [req4] at set4
  change originCore4.residual.cells (complementKey false account 46) = packedMask originChecked.registrations originSnapshot 46 at set4
  have req5 : originPlan5.request = ⟨false,account,47,originRaw5⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready5)
  have set5 := packed_persistent_written_complement originCore4 originPlan5 (by rw [req5])
  rw [← originCore5_step] at set5
  simp only [req5] at set5
  change originCore5.residual.cells (complementKey false account 47) = packedMask originChecked.registrations originSnapshot 47 at set5
  have req6 : originPlan6.request = ⟨false,account,48,originRaw6⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready6)
  have set6 := packed_persistent_written_complement originCore5 originPlan6 (by rw [req6])
  rw [← originCore6_step] at set6
  simp only [req6] at set6
  change originCore6.residual.cells (complementKey false account 48) = packedMask originChecked.registrations originSnapshot 48 at set6
  funext q
  change originCore6.residual.cells (complementKey false account q) = packedMask originChecked.registrations originSnapshot q
  by_cases q0 : q = 42
  · subst q
    rw [originCore6_step,
      packed_other_slot_complement _ originPlan6 false account 42 (by rw [req6]; decide),
      originCore5_step,
      packed_other_slot_complement _ originPlan5 false account 42 (by rw [req5]; decide),
      originCore4_step,
      packed_other_slot_complement _ originPlan4 false account 42 (by rw [req4]; decide),
      originCore3_step,
      packed_other_slot_complement _ originPlan3 false account 42 (by rw [req3]; decide),
      originCore2_step,
      packed_other_slot_complement _ originPlan2 false account 42 (by rw [req2]; decide),
      originCore1_step,
      packed_other_slot_complement _ originPlan1 false account 42 (by rw [req1]; decide),
      set0]
  ·
    by_cases q1 : q = 43
    · subst q
      rw [originCore6_step,
        packed_other_slot_complement _ originPlan6 false account 43 (by rw [req6]; decide),
        originCore5_step,
        packed_other_slot_complement _ originPlan5 false account 43 (by rw [req5]; decide),
        originCore4_step,
        packed_other_slot_complement _ originPlan4 false account 43 (by rw [req4]; decide),
        originCore3_step,
        packed_other_slot_complement _ originPlan3 false account 43 (by rw [req3]; decide),
        originCore2_step,
        packed_other_slot_complement _ originPlan2 false account 43 (by rw [req2]; decide),
        set1]
    ·
      by_cases q2 : q = 44
      · subst q
        rw [originCore6_step,
          packed_other_slot_complement _ originPlan6 false account 44 (by rw [req6]; decide),
          originCore5_step,
          packed_other_slot_complement _ originPlan5 false account 44 (by rw [req5]; decide),
          originCore4_step,
          packed_other_slot_complement _ originPlan4 false account 44 (by rw [req4]; decide),
          originCore3_step,
          packed_other_slot_complement _ originPlan3 false account 44 (by rw [req3]; decide),
          set2]
      ·
        by_cases q3 : q = 45
        · subst q
          rw [originCore6_step,
            packed_other_slot_complement _ originPlan6 false account 45 (by rw [req6]; decide),
            originCore5_step,
            packed_other_slot_complement _ originPlan5 false account 45 (by rw [req5]; decide),
            originCore4_step,
            packed_other_slot_complement _ originPlan4 false account 45 (by rw [req4]; decide),
            set3]
        ·
          by_cases q4 : q = 46
          · subst q
            rw [originCore6_step,
              packed_other_slot_complement _ originPlan6 false account 46 (by rw [req6]; decide),
              originCore5_step,
              packed_other_slot_complement _ originPlan5 false account 46 (by rw [req5]; decide),
              set4]
          ·
            by_cases q5 : q = 47
            · subst q
              rw [originCore6_step,
                packed_other_slot_complement _ originPlan6 false account 47 (by rw [req6]; decide),
                set5]
            ·
              by_cases q6 : q = 48
              · subst q
                rw [set6]
              ·
                rw [originCore6_step,
                  packed_other_slot_complement _ originPlan6 false account q (by rw [req6]; exact q6),
                  originCore5_step,
                  packed_other_slot_complement _ originPlan5 false account q (by rw [req5]; exact q5),
                  originCore4_step,
                  packed_other_slot_complement _ originPlan4 false account q (by rw [req4]; exact q4),
                  originCore3_step,
                  packed_other_slot_complement _ originPlan3 false account q (by rw [req3]; exact q3),
                  originCore2_step,
                  packed_other_slot_complement _ originPlan2 false account q (by rw [req2]; exact q2),
                  originCore1_step,
                  packed_other_slot_complement _ originPlan1 false account q (by rw [req1]; exact q1),
                  originCore0_step,
                  packed_other_slot_complement _ originPlan0 false account q (by rw [req0]; exact q0)]
                unfold originInitialCore originResidual initialPackedComplement
                change complementWord (packedOwnsByte originChecked.registrations q) (originInitialRaw q) =
                  complementWord (packedOwnsByte originChecked.registrations q) (originSnapshot q)
                simp only [originSnapshot,if_neg q0,if_neg q1,if_neg q2,if_neg q3,if_neg q4,if_neg q5,if_neg q6]

theorem origin_actual_whole_physical_snapshot : finiteEncode originChecked.registrations
    (originFrame6.1.2.2.ex.world.accounts account).storage
    (fun q => originCallerCore.residual.cells (complementKey false account q)) = some originSnapshot := by
  rw [origin_actual_residual_snapshot]
  exact origin_actual_full_reencode

end Solidity.Yul.Views.Controls
