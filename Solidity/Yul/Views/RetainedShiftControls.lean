import Solidity.Yul.Views.RetainedShiftProducers
import Solidity.Yul.Views.RetainedComparisonControls

/-! Heterogeneous shift boundary controls distinguish amount constants from
shifted values and retain tuple/alias observations before actual failure.
These intrinsic evaluator controls do not assert frontend admission. -/
namespace Solidity.Yul.Views.Controls

def rshiftOne : Source.RExpr agEnv [agAliasTy,agAliasTy] (.rational (Source.Q.ofInt 1)) := .const (Source.Q.ofInt 1)
def rshiftThree : Source.RExpr agEnv [agAliasTy,agAliasTy] (.int rcU16) :=
  .conv (.const (Source.Q.ofInt 3)) (.inl (by decide))

theorem rshift_success (G : Source.Glob agEnv) :
    (captureShiftRun G packedStepFrame 5 .shl rshiftThree rshiftOne (by decide) [] agShrink.2).1=
      (.ok (.val (Source.intWrap rcU16 6)),agShrink.2) := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rshift_tuple_error (G : Source.Glob agEnv) :
    (captureShiftRun (rpairViaIR G) packedStepFrame 9 .shl (.tuple rcmpArgs) rshiftOne (by decide) [] agShrink.2).1=
      (.error (.stuck "not a plain value"),agShrink.2) := rfl

theorem rshift_tuple_retained (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈
      (captureShiftRun (rpairViaIR G) packedStepFrame 9 .shl (.tuple rcmpArgs) rshiftOne (by decide) [] agShrink.2).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureShiftRun_first
  exact captureRuntimeRun_return packedStepFrame [] _ agShrink.2 agShrink.2 rcmpTuple (rcmp_operand_actual (rpairViaIR G))

theorem rshift_write_failure (G : Source.Glob agEnv) :
    (captureShiftRun (rpairViaIR G) packedStepFrame 5 .shl rpairWrite rshiftOne (by decide) [] rpairState).1=
      (.error (.stuck "shift operand"),rpairAfter) := rfl

theorem rshift_written_alias_retained (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rpairOther)∈
      (captureShiftRun (rpairViaIR G) packedStepFrame 5 .shl rpairWrite rshiftOne (by decide) [] rpairState).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureShiftRun_first
  exact captureRuntimeRun_return packedStepFrame [] _ rpairState rpairAfter (.val rpairOther) rfl

theorem rshift_failure_keeps_write (G : Source.Glob agEnv) :
    (captureShiftRun (rpairViaIR G) packedStepFrame 5 .shl rpairWrite rshiftOne (by decide) [] rpairState).1.2.1≠rpairState.1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact rcmp_no_error_rollback

theorem rshift_wrong_amount_type : Source.STy.isAmount .bool ≠ true := by decide

theorem rshift_zero_horizon (G : Source.Glob agEnv) :
    (captureShiftRun G packedStepFrame 0 .shl rshiftThree rshiftOne (by decide) [] agShrink.2).1=
      (.error .timeout,agShrink.2) := rfl
end Solidity.Yul.Views.Controls
