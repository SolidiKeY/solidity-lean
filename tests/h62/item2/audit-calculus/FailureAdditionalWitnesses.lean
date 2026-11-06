import Solidity.Backend.Failure.UnwindChecks
import Solidity.Backend.Failure.Composition
import tests.h62.item2.«audit-calculus».KernelCensus

/-! Additional joint witnesses from unchanged immediate/emitter/memory and
local checkpoint interfaces. Nonempty payloads, distinct snapshots, nonempty
stack tails and real disjoint/overlapping regions are retained. These local
rules do not assert Solidity world/call or gas adequacy. -/
namespace H62.AuditCalculus.FailureAdditional
open Solidity.Backend Solidity.Backend.Failure Solidity.Backend.Failure.Slice
open Solidity.Backend.Failure.Local

#joint_premises Solidity.Backend.Failure.digits_length as case_1_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_1_joint : case_1_premises := ⟨2, 257, True.intro⟩

#joint_premises Solidity.Backend.Failure.digits_fold as case_2_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_2_joint : case_2_premises := ⟨2, 257, 3, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.read_digits as case_3_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_3_joint : case_3_premises := ⟨2, 257, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.pushNat_immediate as case_4_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_4_joint : case_4_premises := ⟨257, True.intro⟩

#joint_premises Solidity.Backend.Failure.encode_pushNat as case_5_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_5_joint : case_5_premises := ⟨257, True.intro⟩

#joint_premises Solidity.Backend.Failure.writes_length as case_6_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_6_joint : case_6_premises := ⟨31, [0x2a, 0x2b], True.intro⟩

#joint_premises Solidity.Backend.Failure.writes_append as case_7_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_7_joint : case_7_premises := ⟨31, [0x2a], [0x2b], True.intro⟩

#joint_premises Solidity.Backend.Failure.writes_decompose as case_8_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_8_joint : case_8_premises := ⟨31, [0x2a], [0x2b], 0x2c, True.intro⟩

#joint_premises Solidity.Backend.Failure.emit_length as case_9_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_9_joint : case_9_premises := ⟨31, .returned [0x2a, 0x2b], True.intro⟩

#joint_premises Solidity.Backend.Failure.emit_empty as case_10_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_10_joint : case_10_premises := ⟨31, True.intro⟩

#joint_premises Solidity.Backend.Failure.emit_custom as case_11_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_11_joint : case_11_premises := ⟨31, [0x2a, 0x2b], True.intro⟩

#joint_premises Solidity.Backend.Failure.emit_returned as case_12_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_12_joint : case_12_premises := ⟨31, [0x2a, 0x2b], True.intro⟩

#joint_premises Solidity.Backend.Failure.panic_length as case_13_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_13_joint : case_13_premises := ⟨⟨17, by decide⟩, True.intro⟩

#joint_premises Solidity.Backend.Failure.reason_length as case_14_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_14_joint : case_14_premises := ⟨[0x4f, 0x4b], True.intro⟩

#joint_premises Solidity.Backend.Failure.Slice.putBytes_frame as case_15_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_15_joint : case_15_premises := ⟨markedMemory, 31, 30, [0x2a, 0x2b], Or.inl (by decide), True.intro⟩

#joint_premises Solidity.Backend.Failure.Slice.getBytes_putBytes as case_16_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_16_joint : case_16_premises := ⟨markedMemory, 31, [0x2a, 0x2b], True.intro⟩

#joint_premises Solidity.Backend.Failure.Slice.putBytes_append as case_17_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_17_joint : case_17_premises := ⟨markedMemory, 31, [0x2a], [0x2b], True.intro⟩

#joint_premises Solidity.Backend.Failure.Slice.getBytes_congr as case_18_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_18_joint : case_18_premises := by
  refine ⟨markedMemory, putBytes markedMemory 64 [0x55], 31, 2, ?_, True.intro⟩
  intro x lower upper
  exact (putBytes_frame markedMemory 64 x [0x55] (Or.inl (by omega))).symm

#joint_premises Solidity.Backend.Failure.Slice.getBytes_suffix_write as case_19_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_19_joint : case_19_premises := ⟨markedMemory, 31, 2, [0x55, 0x66], True.intro⟩

#joint_premises Solidity.Backend.Failure.run_two_writes as case_20_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_20_joint : case_20_premises := ⟨31, 64, [0x2a, 0x2b], [0x2c, 0x2d], [], markedMachine, by decide, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.disjoint_payloads as case_21_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_21_joint : case_21_premises := ⟨markedMemory, 31, 64, [0x2a, 0x2b], [0x2c, 0x2d], Or.inl (by decide), True.intro⟩

#joint_premises Solidity.Backend.Failure.concatenated_emitters as case_22_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_22_joint : case_22_premises := ⟨31, 31, .returned [0x2a, 0x2b], .custom [0x2c, 0x2d], markedMachine, by unfold Fits Input.bytes; decide, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.return_revert_execution_distinct as case_23_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_23_joint : case_23_premises := ⟨31, [0x2a, 0x2b], markedMachine, by unfold Fits; decide, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.Local.finish_rel as case_24_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_24_joint : case_24_premises := ⟨Fin 17, Fin 19, save root, .revert [0xde, 0xad], deep, True.intro⟩

#joint_premises Solidity.Backend.Failure.Local.CheckpointRel.functional as case_25_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_25_joint : case_25_premises := ⟨Fin 17, Fin 19, save middle, .revert [0xde, 0xad], deep, restore (save middle), restore (save middle), .revert [0xde, 0xad] deep, .revert [0xde, 0xad] deep, True.intro⟩

#joint_premises Solidity.Backend.Failure.Local.restore_save as case_26_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_26_joint : case_26_premises := ⟨Fin 17, Fin 19, middle, True.intro⟩

#joint_premises Solidity.Backend.Failure.Local.snapshot_projections as case_27_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_27_joint : case_27_premises := ⟨Fin 17, Fin 19, save middle, True.intro⟩

#joint_premises Solidity.Backend.Failure.Local.rollback_idempotent as case_28_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_28_joint : case_28_premises := ⟨Fin 17, Fin 19, save middle, deep, [0xde, 0xad], [0xbe, 0xef, 0, 0xff], True.intro⟩

#joint_premises Solidity.Backend.Failure.Local.outer_rollback as case_29_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_29_joint : case_29_premises := ⟨Fin 17, Fin 19, save root, save middle, deep, [0xde, 0xad], [0xbe, 0xef, 0, 0xff], True.intro⟩

#joint_premises Solidity.Backend.Failure.Local.success_keeps_inner_rollback as case_30_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_30_joint : case_30_premises := ⟨Fin 17, Fin 19, save root, save middle, deep, [0xde, 0xad], [0x2a, 0x2b], True.intro⟩

#joint_premises Solidity.Backend.Failure.Local.execute_emitter as case_31_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_31_joint : case_31_premises := ⟨Fin 17, Fin 19, save root, 31, .custom [0xde, 0xad], deep, by unfold Fits Input.bytes; decide, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.Local.execute_checkpoint as case_32_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_32_joint : case_32_premises := ⟨Fin 17, Fin 19, save root, 31, .returned [0x2a, 0x2b], deep, by unfold Fits Input.bytes; decide, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.Local.execute_failure as case_33_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_33_joint : case_33_premises := ⟨Fin 17, Fin 19, save middle, 31, [0xde, 0xad], deep, by unfold Fits; decide, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.Local.execute_return as case_34_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_34_joint : case_34_premises := ⟨Fin 17, Fin 19, save root, 64, [0xbe, 0xef, 0, 0xff], resume middle, by unfold Fits; decide, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.Local.nested_failure as case_35_premises
/-- All dependent inputs and hypotheses of the unchanged statement, jointly. -/
theorem case_35_joint : case_35_premises := ⟨Fin 17, Fin 19, save root, save middle, 31, 64, [0xde, 0xad], [0xbe, 0xef, 0, 0xff], resume, deep, by unfold Fits; decide, by unfold Fits; decide, by decide, by decide, True.intro⟩

#verify_joint Solidity.Backend.Failure.digits_length with case_1_joint
#verify_joint Solidity.Backend.Failure.digits_fold with case_2_joint
#verify_joint Solidity.Backend.Failure.read_digits with case_3_joint
#verify_joint Solidity.Backend.Failure.pushNat_immediate with case_4_joint
#verify_joint Solidity.Backend.Failure.encode_pushNat with case_5_joint
#verify_joint Solidity.Backend.Failure.writes_length with case_6_joint
#verify_joint Solidity.Backend.Failure.writes_append with case_7_joint
#verify_joint Solidity.Backend.Failure.writes_decompose with case_8_joint
#verify_joint Solidity.Backend.Failure.emit_length with case_9_joint
#verify_joint Solidity.Backend.Failure.emit_empty with case_10_joint
#verify_joint Solidity.Backend.Failure.emit_custom with case_11_joint
#verify_joint Solidity.Backend.Failure.emit_returned with case_12_joint
#verify_joint Solidity.Backend.Failure.panic_length with case_13_joint
#verify_joint Solidity.Backend.Failure.reason_length with case_14_joint
#verify_joint Solidity.Backend.Failure.Slice.putBytes_frame with case_15_joint
#verify_joint Solidity.Backend.Failure.Slice.getBytes_putBytes with case_16_joint
#verify_joint Solidity.Backend.Failure.Slice.putBytes_append with case_17_joint
#verify_joint Solidity.Backend.Failure.Slice.getBytes_congr with case_18_joint
#verify_joint Solidity.Backend.Failure.Slice.getBytes_suffix_write with case_19_joint
#verify_joint Solidity.Backend.Failure.run_two_writes with case_20_joint
#verify_joint Solidity.Backend.Failure.disjoint_payloads with case_21_joint
#verify_joint Solidity.Backend.Failure.concatenated_emitters with case_22_joint
#verify_joint Solidity.Backend.Failure.return_revert_execution_distinct with case_23_joint
#verify_joint Solidity.Backend.Failure.Local.finish_rel with case_24_joint
#verify_joint Solidity.Backend.Failure.Local.CheckpointRel.functional with case_25_joint
#verify_joint Solidity.Backend.Failure.Local.restore_save with case_26_joint
#verify_joint Solidity.Backend.Failure.Local.snapshot_projections with case_27_joint
#verify_joint Solidity.Backend.Failure.Local.rollback_idempotent with case_28_joint
#verify_joint Solidity.Backend.Failure.Local.outer_rollback with case_29_joint
#verify_joint Solidity.Backend.Failure.Local.success_keeps_inner_rollback with case_30_joint
#verify_joint Solidity.Backend.Failure.Local.execute_emitter with case_31_joint
#verify_joint Solidity.Backend.Failure.Local.execute_checkpoint with case_32_joint
#verify_joint Solidity.Backend.Failure.Local.execute_failure with case_33_joint
#verify_joint Solidity.Backend.Failure.Local.execute_return with case_34_joint
#verify_joint Solidity.Backend.Failure.Local.nested_failure with case_35_joint

end H62.AuditCalculus.FailureAdditional
