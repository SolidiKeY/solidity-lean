import Solidity.Yul.Views.RetainedUnaryProducers
import Solidity.Yul.Views.RetainedComparisonControls

/-! Unary boundary controls distinguish conversion failure from operator failure,
preserve reached alias writes and observe nested tuples before conversion. These
are intrinsic evaluator controls, not frontend admission or general rollback. -/
namespace Solidity.Yul.Views.Controls

theorem runary_tuple_error (G : Source.Glob agEnv) :
    (captureUnaryRun G packedStepFrame 8 .not (.tuple rcmpArgs) [] agShrink.2).1=
      (.error (.stuck "not a plain value"),agShrink.2) := rfl

theorem runary_tuple_retained (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈
      (captureUnaryRun G packedStepFrame 8 .not (.tuple rcmpArgs) [] agShrink.2).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact captureUnaryRun_return G packedStepFrame 7 .not _ [] agShrink.2 agShrink.2 rcmpTuple (rcmp_operand_actual G)

theorem runary_endpoint_misses_tuple (G : Source.Glob agEnv) :
    runtimeStoragePaths rcmpTuple∉
      ((captureRuntimeRun packedStepFrame []
        (Source.evalE G packedStepFrame 8 (.unary .not (.tuple rcmpArgs))) agShrink.2).2.map EntryReferenceScope.paths) := by
  first | (simp only;done) | decide | omega | rfl | skip
  change [agInner 0,agInner 0,agInner 0]∉[[agInner 0,agInner 0],[agInner 0,agInner 0]]
  decide

theorem runary_write_error (G : Source.Glob agEnv) :
    (captureUnaryRun G packedStepFrame 5 .not rpairWrite [] rpairState).1=
      (.error (.stuck "unary operand"),rpairAfter) := rfl

theorem runary_written_alias_retained (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rpairOther)∈
      (captureUnaryRun G packedStepFrame 5 .not rpairWrite [] rpairState).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact captureUnaryRun_return G packedStepFrame 4 .not _ [] rpairState rpairAfter (.val rpairOther) rfl

theorem runary_failure_keeps_write (G : Source.Glob agEnv) :
    (captureUnaryRun G packedStepFrame 5 .not rpairWrite [] rpairState).1.2.1≠rpairState.1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact rcmp_no_error_rollback

theorem runary_success (G : Source.Glob agEnv) :
    (captureUnaryRun G packedStepFrame 2 .not (.bool true) [] agShrink.2).1=
      (.ok (.val (.bool false)),agShrink.2) := rfl

theorem runary_timeout (G : Source.Glob agEnv) :
    (captureUnaryRun G packedStepFrame 0 .not (.bool true) [] agShrink.2).1=
      (.error .timeout,agShrink.2) := rfl
end Solidity.Yul.Views.Controls
