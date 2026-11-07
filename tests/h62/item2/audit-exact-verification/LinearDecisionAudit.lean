import Solidity.Calculus.LinearDecision
import tests.h62.item2.«audit-exact-verification».JointWitness

namespace Solidity.H62.ExactAudit.LinearDecision
open Solidity.Linear

-- Frozen source: Solidity/Calculus/LinearDecision.lean:53
#joint_inputs Lin_eval_split_inputs for Solidity.Linear.Lin.eval_split := [[2], 1, (fun _ => 3), by decide]
#print axioms Lin_eval_split_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:123
#joint_inputs AFml_holds_mkNot_inputs for Solidity.Linear.AFml.holds_mkNot := [(fun _ => 3), AFml.tt]
#print axioms AFml_holds_mkNot_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:128
#joint_inputs AFml_holds_mkAnd_inputs for Solidity.Linear.AFml.holds_mkAnd := [(fun _ => 3), AFml.tt, AFml.tt]
#print axioms AFml_holds_mkAnd_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:133
#joint_inputs AFml_holds_mkImp_inputs for Solidity.Linear.AFml.holds_mkImp := [(fun _ => 3), AFml.tt, AFml.tt]
#print axioms AFml_holds_mkImp_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:138
#joint_inputs AFml_mkNot_cases_inputs for Solidity.Linear.AFml.mkNot_cases := [AFml.tt]
#print axioms AFml_mkNot_cases_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:142
#joint_inputs AFml_mkAnd_cases_inputs for Solidity.Linear.AFml.mkAnd_cases := [AFml.tt, AFml.tt]
#print axioms AFml_mkAnd_cases_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:147
#joint_inputs AFml_mkImp_cases_inputs for Solidity.Linear.AFml.mkImp_cases := [AFml.tt, AFml.tt]
#print axioms AFml_mkImp_cases_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:166
#joint_inputs add_two_mul_eq_iff_inputs for Solidity.Linear.add_two_mul_eq_iff := [1, 2, 5]
#print axioms add_two_mul_eq_iff_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:171
#joint_inputs add_two_mul_le_iff_inputs for Solidity.Linear.add_two_mul_le_iff := [1, 2, 5]
#print axioms add_two_mul_le_iff_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:180
#joint_inputs AFml_holds_deriv_inputs for Solidity.Linear.AFml.holds_deriv := [1, (fun _ => 3), (AFml.eq [1] 3), by decide]
#print axioms AFml_holds_deriv_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:213
#joint_inputs Lin_eval_zero_inputs for Solidity.Linear.Lin.eval_zero := [[2], (fun _ => 0), by intro _ _; rfl]
#print axioms Lin_eval_zero_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:222
#joint_inputs AFml_holds_zero_inputs for Solidity.Linear.AFml.holds_zero := [(fun _ => 0), (AFml.eq [1] 0), by intro _ _; rfl]
#print axioms AFml_holds_zero_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:250
#joint_inputs vecs_zero_inputs for Solidity.Linear.vecs_zero := []
#print axioms vecs_zero_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:253
#joint_inputs vecs_succ_inputs for Solidity.Linear.vecs_succ := [1]
#print axioms vecs_succ_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:258
#joint_inputs mem_vecs_inputs for Solidity.Linear.mem_vecs := [1, [true], rfl]
#print axioms mem_vecs_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:267
#joint_inputs length_of_mem_vecs_inputs for Solidity.Linear.length_of_mem_vecs := [1, [true], by decide]
#print axioms length_of_mem_vecs_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:277
#joint_inputs length_lowBits_inputs for Solidity.Linear.length_lowBits := [1, (fun _ => 3)]
#print axioms length_lowBits_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:290
#joint_inputs lowBits_withBits_inputs for Solidity.Linear.lowBits_withBits := [[true], (fun _ => 3)]
#print axioms lowBits_withBits_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:300
#joint_inputs halve_withBits_inputs for Solidity.Linear.halve_withBits := [[true], (fun _ => 3)]
#print axioms halve_withBits_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:313
#joint_inputs AFml_deriv_valid_inputs for Solidity.Linear.AFml.deriv_valid := [AFml.tt, (fun _ => True.intro), [true], by decide, (fun _ => 0)]
#print axioms AFml_deriv_valid_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:329
#joint_inputs sumTo_eq_zero_inputs for Solidity.Linear.sumTo_eq_zero := [1, (fun _ => 0), rfl, 0, by decide]
#print axioms sumTo_eq_zero_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:339
#joint_inputs sumTo_halve_le_inputs for Solidity.Linear.sumTo_halve_le := [1, (fun _ => 3)]
#print axioms sumTo_halve_le_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:349
#joint_inputs sumTo_halve_lt_inputs for Solidity.Linear.sumTo_halve_lt := [1, (fun _ => 3), by decide]
#print axioms sumTo_halve_lt_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:367
#joint_inputs AFml_valid_of_closed_inputs for Solidity.Linear.AFml.valid_of_closed := [0, [AFml.tt], by intro G h; have e := List.mem_singleton.mp h; subst G; decide, by intro G h; have e := List.mem_singleton.mp h; subst G; rfl, by intro G h v _; have e := List.mem_singleton.mp h; subst G; exact List.mem_singleton.mpr rfl, AFml.tt, by exact List.mem_singleton.mpr rfl, (fun _ => 0)]
#print axioms AFml_valid_of_closed_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:396
#joint_inputs Lin_dotBits_le_inputs for Solidity.Linear.Lin.dotBits_le := [[2], [true]]
#print axioms Lin_dotBits_le_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:410
#joint_inputs mem_consts_inputs for Solidity.Linear.mem_consts := [2, 1, by decide, by decide]
#print axioms mem_consts_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:416
#joint_inputs bounds_of_mem_consts_inputs for Solidity.Linear.bounds_of_mem_consts := [2, 1, by decide]
#print axioms bounds_of_mem_consts_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:443
#joint_inputs length_flatMap_const_inputs for Solidity.Linear.length_flatMap_const := [Nat, Nat, (fun n => [n]), 1, [2], by intro _ _; rfl]
#print axioms length_flatMap_const_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:453
#joint_inputs AFml_length_universe_inputs for Solidity.Linear.AFml.length_universe := [(AFml.eq [1] 3)]
#print axioms AFml_length_universe_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:468
#joint_inputs AFml_self_mem_universe_inputs for Solidity.Linear.AFml.self_mem_universe := [(AFml.eq [1] 3)]
#print axioms AFml_self_mem_universe_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:482
#joint_inputs AFml_deriv_mem_universe_inputs for Solidity.Linear.AFml.deriv_mem_universe := [[true], AFml.tt, AFml.tt, by decide]
#print axioms AFml_deriv_mem_universe_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:547
#joint_inputs AFml_width_of_mem_universe_inputs for Solidity.Linear.AFml.width_of_mem_universe := [AFml.tt, AFml.tt, by decide]
#print axioms AFml_width_of_mem_universe_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:584
#joint_inputs length_le_of_nodup_inputs for Solidity.Linear.length_le_of_nodup := [Nat, inferInstance, [1], [1], by decide, by intro _ h; exact h]
#print axioms length_le_of_nodup_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:606
#joint_inputs mem_addNew_inputs for Solidity.Linear.mem_addNew := [[], AFml.tt, [], [AFml.tt]]
#print axioms mem_addNew_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:637
#joint_inputs nodup_addNew_inputs for Solidity.Linear.nodup_addNew := [[], [AFml.tt], [AFml.tt], by decide, by intro _ _ h; cases h]
#print axioms nodup_addNew_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:669
#joint_inputs explore_spec_inputs for Solidity.Linear.explore_spec := [[[]], (fun G => G = AFml.tt), by intro G h v _; cases h; rfl, 2, [AFml.tt], [AFml.tt], [AFml.tt], rfl, by intro G h; exact h, by intro G h hn; exact (hn h).elim, by intro G h; exact List.mem_singleton.mp h]
#print axioms explore_spec_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:711
#joint_inputs explore_isSome_inputs for Solidity.Linear.explore_isSome := [[[]], [AFml.tt], (fun G => G = AFml.tt), by intro G h v _; cases h; rfl, by intro G h; exact List.mem_singleton.mpr h, 2, [AFml.tt], [AFml.tt], by decide, by intro G h; exact h, by intro G h; exact List.mem_singleton.mp h, by decide]
#print axioms explore_isSome_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:758
#joint_inputs Lin_eval_trim_inputs for Solidity.Linear.Lin.eval_trim := [[2,0], (fun _ => 3)]
#print axioms Lin_eval_trim_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:774
#joint_inputs AFml_holds_mkEq_inputs for Solidity.Linear.AFml.holds_mkEq := [(fun _ => 3), [2], 6]
#print axioms AFml_holds_mkEq_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:788
#joint_inputs AFml_holds_mkLe_inputs for Solidity.Linear.AFml.holds_mkLe := [(fun _ => 3), [2], 6]
#print axioms AFml_holds_mkLe_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:808
#joint_inputs AFml_holds_simp_inputs for Solidity.Linear.AFml.holds_simp := [(fun _ => 3), (AFml.eq [1] 3)]
#print axioms AFml_holds_simp_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:826
#joint_inputs AFml_exploration_isSome_inputs for Solidity.Linear.AFml.exploration_isSome := [(AFml.eq [1] 3)]
#print axioms AFml_exploration_isSome_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:848
#joint_inputs AFml_search_iff_inputs for Solidity.Linear.AFml.search_iff := [(AFml.eq [1] 3)]
#print axioms AFml_search_iff_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:898
#joint_inputs Lin_gcdAll_dvd_inputs for Solidity.Linear.Lin.gcdAll_dvd := [[2], 2, by decide]
#print axioms Lin_gcdAll_dvd_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:905
#joint_inputs Lin_eval_divBy_inputs for Solidity.Linear.Lin.eval_divBy := [2, [2], by intro a h; have e := List.mem_singleton.mp h; subst a; decide, (fun _ => 3)]
#print axioms Lin_eval_divBy_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:914
#joint_inputs Lin_length_divBy_inputs for Solidity.Linear.Lin.length_divBy := [2, [2]]
#print axioms Lin_length_divBy_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:916
#joint_inputs Lin_eval_nonneg_inputs for Solidity.Linear.Lin.eval_nonneg := [[2], by intro a h; have e := List.mem_singleton.mp h; subst a; decide, (fun _ => 3)]
#print axioms Lin_eval_nonneg_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:925
#joint_inputs Lin_eval_nonpos_inputs for Solidity.Linear.Lin.eval_nonpos := [[-2], by intro a h; have e := List.mem_singleton.mp h; subst a; decide, (fun _ => 3)]
#print axioms Lin_eval_nonpos_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:934
#joint_inputs Lin_length_trim_le_inputs for Solidity.Linear.Lin.length_trim_le := [[2,0]]
#print axioms Lin_length_trim_le_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:944
#joint_inputs Lin_dvd_of_allDvd_inputs for Solidity.Linear.Lin.dvd_of_allDvd := [2, [2], by decide, 2, by decide]
#print axioms Lin_dvd_of_allDvd_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:973
#joint_inputs AFml_holds_atomEqBy_inputs for Solidity.Linear.AFml.holds_atomEqBy := [(fun _ => 3), 2, [2], 6]
#print axioms AFml_holds_atomEqBy_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1004
#joint_inputs AFml_holds_atomLeBy_inputs for Solidity.Linear.AFml.holds_atomLeBy := [(fun _ => 3), 2, [2], 6]
#print axioms AFml_holds_atomLeBy_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1025
#joint_inputs AFml_holds_atomEq_inputs for Solidity.Linear.AFml.holds_atomEq := [(fun _ => 3), [2], 6]
#print axioms AFml_holds_atomEq_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1032
#joint_inputs AFml_holds_atomLe_inputs for Solidity.Linear.AFml.holds_atomLe := [(fun _ => 3), [2], 6]
#print axioms AFml_holds_atomLe_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1039
#joint_inputs AFml_width_atomEqBy_inputs for Solidity.Linear.AFml.width_atomEqBy := [2, [2], 6]
#print axioms AFml_width_atomEqBy_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1047
#joint_inputs AFml_width_atomLeBy_inputs for Solidity.Linear.AFml.width_atomLeBy := [2, [2], 6]
#print axioms AFml_width_atomLeBy_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1057
#joint_inputs AFml_width_atomEq_inputs for Solidity.Linear.AFml.width_atomEq := [[2], 6]
#print axioms AFml_width_atomEq_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1063
#joint_inputs AFml_width_atomLe_inputs for Solidity.Linear.AFml.width_atomLe := [[2], 6]
#print axioms AFml_width_atomLe_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1097
#joint_inputs AFml_holds_nNot_inputs for Solidity.Linear.AFml.holds_nNot := [(fun _ => 3), AFml.tt]
#print axioms AFml_holds_nNot_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1100
#joint_inputs AFml_holds_nAnd_inputs for Solidity.Linear.AFml.holds_nAnd := [(fun _ => 3), AFml.tt, AFml.tt]
#print axioms AFml_holds_nAnd_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1103
#joint_inputs AFml_holds_nImp_inputs for Solidity.Linear.AFml.holds_nImp := [(fun _ => 3), AFml.tt, AFml.tt]
#print axioms AFml_holds_nImp_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1109
#joint_inputs AFml_width_nNot_inputs for Solidity.Linear.AFml.width_nNot := [AFml.tt]
#print axioms AFml_width_nNot_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1112
#joint_inputs AFml_width_nAnd_inputs for Solidity.Linear.AFml.width_nAnd := [AFml.tt, AFml.tt]
#print axioms AFml_width_nAnd_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1115
#joint_inputs AFml_width_nImp_inputs for Solidity.Linear.AFml.width_nImp := [AFml.tt, AFml.tt]
#print axioms AFml_width_nImp_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1131
#joint_inputs AFml_holds_norm_inputs for Solidity.Linear.AFml.holds_norm := [(fun _ => 3), (AFml.eq [1] 3)]
#print axioms AFml_holds_norm_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1139
#joint_inputs AFml_width_norm_inputs for Solidity.Linear.AFml.width_norm := [(AFml.eq [1] 3)]
#print axioms AFml_width_norm_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1178
#joint_inputs Lin_length_dbl_inputs for Solidity.Linear.Lin.length_dbl := [0, [2]]
#print axioms Lin_length_dbl_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1183
#joint_inputs shift_setAt_inputs for Solidity.Linear.shift_setAt := [(fun _ => 3), 0, 2]
#print axioms shift_setAt_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1186
#joint_inputs shift_setAt_zero_inputs for Solidity.Linear.shift_setAt_zero := [(fun _ => 3), 2]
#print axioms shift_setAt_zero_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1190
#joint_inputs Lin_eval_dbl_inputs for Solidity.Linear.Lin.eval_dbl := [0, [2], (fun _ => 3)]
#print axioms Lin_eval_dbl_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1217
#joint_inputs AFml_width_pderiv_inputs for Solidity.Linear.AFml.width_pderiv := [0, true, (AFml.eq [1] 3)]
#print axioms AFml_width_pderiv_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1225
#joint_inputs AFml_holds_pderiv_inputs for Solidity.Linear.AFml.holds_pderiv := [0, true, (fun _ => 3), (AFml.eq [1] 3)]
#print axioms AFml_holds_pderiv_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1250
#joint_inputs Lin_dbl_of_coef_zero_inputs for Solidity.Linear.Lin.dbl_of_coef_zero := [1, [2], rfl]
#print axioms Lin_dbl_of_coef_zero_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1270
#joint_inputs AFml_holds_pstep_inputs for Solidity.Linear.AFml.holds_pstep := [0, true, (fun _ => 3), (AFml.eq [1] 3)]
#print axioms AFml_holds_pstep_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1289
#joint_inputs AFml_width_pstep_inputs for Solidity.Linear.AFml.width_pstep := [0, true, (AFml.eq [1] 3)]
#print axioms AFml_width_pstep_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1316
#joint_inputs sumTo_congr_inputs for Solidity.Linear.sumTo_congr := [1, (fun _ => 3), (fun _ => 3), by intro _ _; rfl]
#print axioms sumTo_congr_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1329
#joint_inputs AFml_round_inputs for Solidity.Linear.AFml.round := [1, (fun p : AFml × Nat => p.1 = .tt), by intro G j h _ b; cases h; rfl, 1, 0, AFml.tt, rfl, by decide, rfl, (fun _ => 3)]
#print axioms AFml_round_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1372
#joint_inputs AFml_valid_of_rounds_inputs for Solidity.Linear.AFml.valid_of_rounds := [1, by decide, (fun p : AFml × Nat => p.1 = .tt), by intro G j h; cases h; decide, by intro G j h; cases h; rfl, by intro G j h _ b; cases h; rfl, AFml.tt, rfl, (fun _ => 3)]
#print axioms AFml_valid_of_rounds_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1475
#joint_inputs AFml_walkFrom_closed_inputs for Solidity.Linear.AFml.walkFrom_closed := [AFml.tt, (HSet.leaf.insert (AFml.stateHash (AFml.tt, 0)) (AFml.tt, 0)), rfl, (fun _ => 3)]
#print axioms AFml_walkFrom_closed_inputs

-- Frozen source: Solidity/Calculus/LinearDecision.lean:1523
#joint_inputs AFml_decide_iff_inputs for Solidity.Linear.AFml.decide_iff := [(AFml.eq [1] 3)]
#print axioms AFml_decide_iff_inputs

end Solidity.H62.ExactAudit.LinearDecision
