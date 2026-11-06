import Solidity.Yul.Views.RetainedConversionProducers
import Solidity.Yul.Views.RetainedComparisonControls

/-! Inhabited conversion controls preserve nested runtime tuples, incoming
aliases and reached local writes. These are intrinsic Source executions;
conversion capture does not prove reachability or physical heap adequacy. -/
namespace Solidity.Yul.Views.Controls

theorem rconv_tuple_actual (G : Source.Glob agEnv) :
    (captureConversionRun G packedStepFrame 8 (.tuple rcmpArgs) (.inr rfl) [] agShrink.2).1=
      (.ok rcmpTuple,agShrink.2) := rfl

theorem rconv_tuple_retained (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcmpTuple∈
      (captureConversionRun G packedStepFrame 8 (.tuple rcmpArgs) (.inr rfl) [] agShrink.2).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact captureConversionRun_return G packedStepFrame 7 _ (.inr rfl) [] agShrink.2 agShrink.2 rcmpTuple (rcmp_operand_actual G)

theorem rconv_alias_write (G : Source.Glob agEnv) :
    (captureConversionRun G packedStepFrame 5 rpairWrite (.inr rfl) [] rpairState).1=
      (.ok (.val rpairOther),rpairAfter) := rfl

theorem rconv_written_alias_retained (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rpairOther)∈
      (captureConversionRun G packedStepFrame 5 rpairWrite (.inr rfl) [] rpairState).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact captureConversionRun_return G packedStepFrame 4 _ (.inr rfl) [] rpairState rpairAfter (.val rpairOther) rfl

theorem rconv_wrong_original_state (G : Source.Glob agEnv) :
    (captureConversionRun G packedStepFrame 5 rpairWrite (.inr rfl) [] rpairState).1.2.1≠rpairState.1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact rcmp_no_error_rollback

theorem rconv_timeout (G : Source.Glob agEnv) :
    (captureConversionRun G packedStepFrame 0 rpairWrite (.inr rfl) [] rpairState).1=
      (.error .timeout,rpairState) := rfl

theorem rconv_explicit_bool (G : Source.Glob agEnv) :
    (captureExplicitConversionRun (τ:=.bool) G packedStepFrame 2 (.bool true) (by decide) [] agShrink.2).1=
      (.ok (.val (.bool true)),agShrink.2) := rfl

theorem rconv_explicit_timeout (G : Source.Glob agEnv) :
    (captureExplicitConversionRun (τ:=.bool) G packedStepFrame 0 (.bool true) (by decide) [] agShrink.2).1=
      (.error .timeout,agShrink.2) := rfl
end Solidity.Yul.Views.Controls
