import Solidity.Yul.Views.RetainedComparisonProducers
import Solidity.Yul.Views.RetainedPairControls

/-! Actual evaluator conversion and comparison failures retain produced
operand observations and reached writes. Tuple comparison is a typed evaluator
boundary control, not a claim of Solidity frontend admission. Equal final
errors do not justify erasing values observed before getV/cmpVal. -/
namespace Solidity.Yul.Views.Controls

def rcmpArgs : Source.RArgs agEnv [agAliasTy,agAliasTy] [agAliasTy,.tuple [agAliasTy,agAliasTy]] :=
  .cons (.local .here) (.cons (.tuple (.cons (.local .here) (.cons (.local (.there .here)) .nil))) .nil)
def rcmpTuple : Source.RVal agEnv.layout (.tuple [agAliasTy,.tuple [agAliasTy,agAliasTy]]) :=
  .tuple (.cons (.val rtAlias) (.cons (.tuple (.cons (.val rtAlias) (.cons (.val rtAlias) .nil))) .nil))

theorem rcmp_operand_actual (G : Source.Glob agEnv) :
    (Source.evalE G packedStepFrame 7 (.tuple rcmpArgs)).run agShrink.2=(.ok rcmpTuple,agShrink.2) := rfl

theorem rcmp_getV_failure (G : Source.Glob agEnv) :
    (Source.evalE G packedStepFrame 9 (.compare .eq (.tuple rcmpArgs) (.tuple rcmpArgs))).run agShrink.2=
      (.error (.stuck "not a plain value"),agShrink.2) := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rcmp_capture_failure (G : Source.Glob agEnv) :
    (captureComparisonRun G packedStepFrame 9 .eq (.tuple rcmpArgs) (.tuple rcmpArgs) [] agShrink.2).1=
      (.error (.stuck "not a plain value"),agShrink.2) := by
  first | omega | decide | skip
  rw [captureComparisonRun_source]
  exact rcmp_getV_failure G

theorem rcmp_tuple_retained (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈
      (captureComparisonRun G packedStepFrame 9 .eq (.tuple rcmpArgs) (.tuple rcmpArgs) [] agShrink.2).2 := by
  first | omega | decide | skip
  apply captureComparisonRun_first
  cases pipeline : G.pipeline <;>
    simp only [] <;>
    exact captureRuntimeRun_return packedStepFrame [] _ agShrink.2 agShrink.2 rcmpTuple (rcmp_operand_actual G)

/-- Endpoint-only observation has no runtime return scope after getV fails. -/
theorem rcmp_endpoint_misses_tuple (G : Source.Glob agEnv) :
    runtimeStoragePaths rcmpTuple∉
      ((captureRuntimeRun packedStepFrame []
        (Source.evalE G packedStepFrame 9 (.compare .eq (.tuple rcmpArgs) (.tuple rcmpArgs))) agShrink.2).2.map EntryReferenceScope.paths) := by
  first | omega | decide | skip
  unfold captureRuntimeRun
  rw [rcmp_getV_failure]
  change [agInner 0,agInner 0,agInner 0]∉[[agInner 0,agInner 0],[agInner 0,agInner 0]]
  decide

theorem rcmp_operand_write_then_failure (G : Source.Glob agEnv) :
    (captureComparisonRun (rpairLegacy G) packedStepFrame 5 .eq rpairWrite (.local .here) [] rpairState).1=
      (.error (.stuck "values without order"),rpairAfter) := rfl

theorem rcmp_old_value_kept (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈
      (captureComparisonRun (rpairLegacy G) packedStepFrame 5 .eq rpairWrite (.local .here) [] rpairState).2 := by
  first | omega | decide | skip
  apply captureComparisonRun_first
  exact captureRuntimeRun_return packedStepFrame [] _ rpairState rpairState (.val rtAlias) rfl

theorem rcmp_no_error_rollback : rpairAfter.1≠rpairState.1 := by
  first | omega | decide | skip
  intro same
  have first := congrArg (fun locals=>runtimeStoragePaths (.val (locals.get .here))) same
  exact (by decide : [agInner 1]≠[agInner 0]) first

theorem rcmp_success (G : Source.Glob agEnv) :
    (captureComparisonRun G packedStepFrame 4 .eq (.bool true) (.bool false) [] agShrink.2).1=
      (.ok (.val (.bool false)),agShrink.2) := by
  first | omega | decide | skip
  rw [captureComparisonRun_source]
  cases pipeline : G.pipeline <;> simp only [Source.evalE,Source.evalPair,pipeline] <;> rfl
end Solidity.Yul.Views.Controls
