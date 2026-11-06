import Solidity.Yul.Views.RootDeclarationJournal

namespace Solidity.Yul.Views.Controls

theorem root_actual_residual_snapshot :
    (fun q => rootCallerCore.residual.cells (complementKey false account q)) = rootStore.2 := by
  have req0 : rootPlan0.request = ⟨false,account,0,rootRaw0⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready0)
  have set0 := packed_persistent_written_complement rootInitialCore rootPlan0 (by rw [req0])
  rw [← rootCore0_step] at set0
  simp only [req0] at set0
  change rootCore0.residual.cells (complementKey false account 0) = packedMask rootChecked.registrations rootSnapshot 0 at set0
  have req1 : rootPlan1.request = ⟨false,account,1,rootRaw1⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready1)
  have set1 := packed_persistent_written_complement rootCore0 rootPlan1 (by rw [req1])
  rw [← rootCore1_step] at set1
  simp only [req1] at set1
  change rootCore1.residual.cells (complementKey false account 1) = packedMask rootChecked.registrations rootSnapshot 1 at set1
  have req2 : rootPlan2.request = ⟨false,account,2,rootRaw2⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready2)
  have set2 := packed_persistent_written_complement rootCore1 rootPlan2 (by rw [req2])
  rw [← rootCore2_step] at set2
  simp only [req2] at set2
  change rootCore2.residual.cells (complementKey false account 2) = packedMask rootChecked.registrations rootSnapshot 2 at set2
  have req3 : rootPlan3.request = ⟨false,account,3,rootRaw3⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready3)
  have set3 := packed_persistent_written_complement rootCore2 rootPlan3 (by rw [req3])
  rw [← rootCore3_step] at set3
  simp only [req3] at set3
  change rootCore3.residual.cells (complementKey false account 3) = packedMask rootChecked.registrations rootSnapshot 3 at set3
  have req4 : rootPlan4.request = ⟨false,account,4,rootRaw4⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready4)
  have set4 := packed_persistent_written_complement rootCore3 rootPlan4 (by rw [req4])
  rw [← rootCore4_step] at set4
  simp only [req4] at set4
  change rootCore4.residual.cells (complementKey false account 4) = packedMask rootChecked.registrations rootSnapshot 4 at set4
  have req5 : rootPlan5.request = ⟨false,account,5,rootRaw5⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready5)
  have set5 := packed_persistent_written_complement rootCore4 rootPlan5 (by rw [req5])
  rw [← rootCore5_step] at set5
  simp only [req5] at set5
  change rootCore5.residual.cells (complementKey false account 5) = packedMask rootChecked.registrations rootSnapshot 5 at set5
  have req6 : rootPlan6.request = ⟨false,account,6,rootRaw6⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready6)
  have set6 := packed_persistent_written_complement rootCore5 rootPlan6 (by rw [req6])
  rw [← rootCore6_step] at set6
  simp only [req6] at set6
  change rootCore6.residual.cells (complementKey false account 6) = packedMask rootChecked.registrations rootSnapshot 6 at set6
  funext q
  change rootCore6.residual.cells (complementKey false account q) = packedMask rootChecked.registrations rootSnapshot q
  by_cases q0 : q = 0
  · subst q
    rw [rootCore6_step,
      packed_other_slot_complement _ rootPlan6 false account 0 (by rw [req6]; decide),
      rootCore5_step,
      packed_other_slot_complement _ rootPlan5 false account 0 (by rw [req5]; decide),
      rootCore4_step,
      packed_other_slot_complement _ rootPlan4 false account 0 (by rw [req4]; decide),
      rootCore3_step,
      packed_other_slot_complement _ rootPlan3 false account 0 (by rw [req3]; decide),
      rootCore2_step,
      packed_other_slot_complement _ rootPlan2 false account 0 (by rw [req2]; decide),
      rootCore1_step,
      packed_other_slot_complement _ rootPlan1 false account 0 (by rw [req1]; decide),
      set0]
  ·
    by_cases q1 : q = 1
    · subst q
      rw [rootCore6_step,
        packed_other_slot_complement _ rootPlan6 false account 1 (by rw [req6]; decide),
        rootCore5_step,
        packed_other_slot_complement _ rootPlan5 false account 1 (by rw [req5]; decide),
        rootCore4_step,
        packed_other_slot_complement _ rootPlan4 false account 1 (by rw [req4]; decide),
        rootCore3_step,
        packed_other_slot_complement _ rootPlan3 false account 1 (by rw [req3]; decide),
        rootCore2_step,
        packed_other_slot_complement _ rootPlan2 false account 1 (by rw [req2]; decide),
        set1]
    ·
      by_cases q2 : q = 2
      · subst q
        rw [rootCore6_step,
          packed_other_slot_complement _ rootPlan6 false account 2 (by rw [req6]; decide),
          rootCore5_step,
          packed_other_slot_complement _ rootPlan5 false account 2 (by rw [req5]; decide),
          rootCore4_step,
          packed_other_slot_complement _ rootPlan4 false account 2 (by rw [req4]; decide),
          rootCore3_step,
          packed_other_slot_complement _ rootPlan3 false account 2 (by rw [req3]; decide),
          set2]
      ·
        by_cases q3 : q = 3
        · subst q
          rw [rootCore6_step,
            packed_other_slot_complement _ rootPlan6 false account 3 (by rw [req6]; decide),
            rootCore5_step,
            packed_other_slot_complement _ rootPlan5 false account 3 (by rw [req5]; decide),
            rootCore4_step,
            packed_other_slot_complement _ rootPlan4 false account 3 (by rw [req4]; decide),
            set3]
        ·
          by_cases q4 : q = 4
          · subst q
            rw [rootCore6_step,
              packed_other_slot_complement _ rootPlan6 false account 4 (by rw [req6]; decide),
              rootCore5_step,
              packed_other_slot_complement _ rootPlan5 false account 4 (by rw [req5]; decide),
              set4]
          ·
            by_cases q5 : q = 5
            · subst q
              rw [rootCore6_step,
                packed_other_slot_complement _ rootPlan6 false account 5 (by rw [req6]; decide),
                set5]
            ·
              by_cases q6 : q = 6
              · subst q
                rw [set6]
              ·
                rw [rootCore6_step,
                  packed_other_slot_complement _ rootPlan6 false account q (by rw [req6]; exact q6),
                  rootCore5_step,
                  packed_other_slot_complement _ rootPlan5 false account q (by rw [req5]; exact q5),
                  rootCore4_step,
                  packed_other_slot_complement _ rootPlan4 false account q (by rw [req4]; exact q4),
                  rootCore3_step,
                  packed_other_slot_complement _ rootPlan3 false account q (by rw [req3]; exact q3),
                  rootCore2_step,
                  packed_other_slot_complement _ rootPlan2 false account q (by rw [req2]; exact q2),
                  rootCore1_step,
                  packed_other_slot_complement _ rootPlan1 false account q (by rw [req1]; exact q1),
                  rootCore0_step,
                  packed_other_slot_complement _ rootPlan0 false account q (by rw [req0]; exact q0)]
                unfold rootInitialCore rootResidual initialPackedComplement
                change complementWord (packedOwnsByte rootChecked.registrations q) (rootInitialRaw q) =
                  complementWord (packedOwnsByte rootChecked.registrations q) (rootSnapshot q)
                simp only [rootSnapshot,if_neg q0,if_neg q1,if_neg q2,if_neg q3,if_neg q4,if_neg q5,if_neg q6]

theorem root_actual_whole_physical_snapshot : finiteEncode rootChecked.registrations
    (rootFrame6.1.2.2.ex.world.accounts account).storage
    (fun q => rootCallerCore.residual.cells (complementKey false account q)) = some rootSnapshot := by
  rw [root_actual_residual_snapshot]
  exact root_actual_full_reencode

end Solidity.Yul.Views.Controls
