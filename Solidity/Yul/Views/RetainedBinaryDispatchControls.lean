import Solidity.Yul.Views.RetainedBinaryDispatch
import Solidity.Yul.Views.RetainedBinaryControls
import Solidity.Yul.Views.RetainedLogicalControls

/-! Unified producer controls preserve the actual logical/pair distinction,
including skipped writes, late halt, alias overwrite order and unequal horizons.
No Source frontend admission or recursive intermediate completeness is inferred. -/
namespace Solidity.Yul.Views.Controls

theorem rdispatch_skip (G : Source.Glob agEnv) :
    (captureBinaryRun G packedStepFrame 5 .and (.bool false) rlogicalWrite [] rlogicalState).1=
      (.ok (.val (.bool false)),rlogicalState) := rlogical_skip_write G

theorem rdispatch_write (G : Source.Glob agEnv) :
    (captureBinaryRun G packedStepFrame 5 .or (.bool false) rlogicalWrite [] rlogicalState).1=
      (.ok (.val (.bool true)),rlogicalAfter) := rlogical_execute_write G

theorem rdispatch_skipped_timeout (G : Source.Glob agEnv) :
    (captureBinaryRun G packedStepFrame 2 .and (.bool false) rlogicalLate [] rlogicalState).1=
      (.ok (.val (.bool false)),rlogicalState) := rlogical_skip_timeout G

theorem rdispatch_executed_timeout (G : Source.Glob agEnv) :
    (captureBinaryRun G packedStepFrame 2 .or (.bool false) rlogicalLate [] rlogicalState).1=
      (.error .timeout,rlogicalState) := rlogical_execute_timeout G

theorem rdispatch_pair_write_failure (G : Source.Glob agEnv) :
    (captureBinaryRun (rpairLegacy G) packedStepFrame 5 .add rpairWrite (.local .here) [] rpairState).1=
      (.error (.stuck "operands of a binary operation"),rpairAfter) := rbin_operand_write_then_failure G

theorem rdispatch_old_alias_kept (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈
      (captureBinaryRun (rpairLegacy G) packedStepFrame 5 .add rpairWrite (.local .here) [] rpairState).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureBinaryRun_first
  exact captureRuntimeRun_return packedStepFrame [] _ rpairState rpairState (.val rtAlias) rfl

theorem rdispatch_logical_horizon (G : Source.Glob agEnv) :
    (captureBinaryRun G packedStepFrame 2 .and (.bool false) (.bool true) [] rlogicalState).1=
      (.ok (.val (.bool false)),rlogicalState) := rfl

theorem rdispatch_pair_horizon (G : Source.Glob agEnv) :
    (captureBinaryRun G packedStepFrame 2 .add (.bool false) (.bool true) [] rlogicalState).1=
      (.error .timeout,rlogicalState) := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rdispatch_tuple_logical (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈
      (captureBinaryRun G packedStepFrame 8 .and (.tuple rcmpArgs) (.tuple rcmpArgs) [] agShrink.2).2 := rlogical_tuple_kept G

theorem rdispatch_tuple_pair (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈
      (captureBinaryRun G packedStepFrame 9 .add (.tuple rcmpArgs) (.tuple rcmpArgs) [] agShrink.2).2 := rbin_tuple_retained G
end Solidity.Yul.Views.Controls
