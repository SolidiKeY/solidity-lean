import Solidity.Yul.Views.RetainedBinaryProducers
import Solidity.Yul.Views.RetainedComparisonControls

/-! Binary pair controls preserve tuple observations and local-write prefixes
through actual conversion/operator failure. Nonlogical branch certificates are
explicit; no short-circuit, frontend admission or recursive coverage is claimed. -/
namespace Solidity.Yul.Views.Controls
theorem rbin_getV_failure (G : Source.Glob agEnv) :
    (Source.evalE G packedStepFrame 9 (.binary .add (.tuple rcmpArgs) (.tuple rcmpArgs))).run agShrink.2=
      (.error (.stuck "not a plain value"),agShrink.2) := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases G with
  | mk prog pipeline fixed balance hasCode callee timestamp => cases pipeline <;> rfl

theorem rbin_capture_failure (G : Source.Glob agEnv) :
    (captureBinaryPairRun G packedStepFrame 9 .add (.tuple rcmpArgs) (.tuple rcmpArgs) [] agShrink.2).1=
      (.error (.stuck "not a plain value"),agShrink.2) := by
  first | omega | decide | skip
  rw [captureBinaryPairRun_source G packedStepFrame 9 .add _ _ [] agShrink.2 (by decide)]
  exact rbin_getV_failure G

theorem rbin_tuple_retained (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈
      (captureBinaryPairRun G packedStepFrame 9 .add (.tuple rcmpArgs) (.tuple rcmpArgs) [] agShrink.2).2 := by
  first | omega | decide | skip
  apply captureBinaryPairRun_first
  cases pipeline : G.pipeline <;>
    simp only [] <;>
    exact captureRuntimeRun_return packedStepFrame [] _ agShrink.2 agShrink.2 rcmpTuple (rcmp_operand_actual G)

/-- Endpoint-only observation has no runtime return scope after getV fails. -/
theorem rbin_endpoint_misses_tuple (G : Source.Glob agEnv) :
    runtimeStoragePaths rcmpTuple∉
      ((captureRuntimeRun packedStepFrame []
        (Source.evalE G packedStepFrame 9 (.binary .add (.tuple rcmpArgs) (.tuple rcmpArgs))) agShrink.2).2.map EntryReferenceScope.paths) := by
  first | omega | decide | skip
  unfold captureRuntimeRun
  rw [rbin_getV_failure]
  change [agInner 0,agInner 0,agInner 0]∉[[agInner 0,agInner 0],[agInner 0,agInner 0]]
  decide

theorem rbin_operand_write_then_failure (G : Source.Glob agEnv) :
    (captureBinaryPairRun (rpairLegacy G) packedStepFrame 5 .add rpairWrite (.local .here) [] rpairState).1=
      (.error (.stuck "operands of a binary operation"),rpairAfter) := rfl

theorem rbin_old_value_kept (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈
      (captureBinaryPairRun (rpairLegacy G) packedStepFrame 5 .add rpairWrite (.local .here) [] rpairState).2 := by
  first | omega | decide | skip
  apply captureBinaryPairRun_first
  exact captureRuntimeRun_return packedStepFrame [] _ rpairState rpairState (.val rtAlias) rfl

theorem rbin_no_error_rollback : rpairAfter.1≠rpairState.1 := by
  first | omega | decide | skip
  intro same
  have first := congrArg (fun locals=>runtimeStoragePaths (.val (locals.get .here))) same
  exact (by decide : [agInner 1]≠[agInner 0]) first


theorem rbin_bool_error (G : Source.Glob agEnv) :
    (captureBinaryPairRun G packedStepFrame 4 .add (.bool true) (.bool false) [] agShrink.2).1=
      (.error (.stuck "not a boolean operation"),agShrink.2) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [captureBinaryPairRun_source G packedStepFrame 4 .add _ _ [] agShrink.2 (by decide)]
  cases pipeline : G.pipeline <;> simp only [Source.evalE,Source.evalPair,pipeline] <;> rfl

theorem rbin_and_not_pair : (decide (Source.BinOp.and = .and) || decide (Source.BinOp.and = .or)) ≠ false := by decide

theorem rbin_timeout (G : Source.Glob agEnv) :
    (captureBinaryPairRun G packedStepFrame 0 .add (.bool true) (.bool false) [] agShrink.2).1=
      (.error .timeout,agShrink.2) := rfl
end Solidity.Yul.Views.Controls
