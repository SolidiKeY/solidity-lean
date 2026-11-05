import Solidity.Yul.Views.RetainedPairProducers
import Solidity.Yul.Views.RetainedTupleControls

/-! Actual pipeline operand order changes which pre-overwrite reference is
observed. A successful earlier operand survives a later timeout even when the
pair returns no value. Scope observations are not RefOK or historical formation
proofs, and arbitrary recursive operand intermediates remain outside capture. -/
namespace Solidity.Yul.Views.Controls

def rpairOther : Source.Val agEnv.layout agAliasTy := .storRef (by rfl) (agInner 1)
def rpairState : Source.EMState agEnv [agAliasTy,agAliasTy] :=
  (.cons rtAlias (.cons rpairOther .nil),agShrink.2.2)
def rpairAfter : Source.EMState agEnv [agAliasTy,agAliasTy] :=
  (.cons rpairOther (.cons rpairOther .nil),agShrink.2.2)
def rpairLegacy (G : Source.Glob agEnv) : Source.Glob agEnv := {G with pipeline:=.legacy}
def rpairViaIR (G : Source.Glob agEnv) : Source.Glob agEnv := {G with pipeline:=.viaIR}
def rpairWrite : Source.RExpr agEnv [agAliasTy,agAliasTy] agAliasTy := .assign (.local .here) (.local (.there .here))

theorem rpair_legacy_actual (G : Source.Glob agEnv) :
    (Source.evalPair (rpairLegacy G) packedStepFrame 4 rpairWrite (.local .here)).run rpairState=
      (.ok (.val rpairOther,.val rtAlias),rpairAfter) := rfl

theorem rpair_viaIR_actual (G : Source.Glob agEnv) :
    (Source.evalPair (rpairViaIR G) packedStepFrame 4 rpairWrite (.local .here)).run rpairState=
      (.ok (.val rpairOther,.val rpairOther),rpairAfter) := rfl

theorem rpair_capture_legacy (G : Source.Glob agEnv) :
    (capturePairRun (rpairLegacy G) packedStepFrame 4 rpairWrite (.local .here) [] rpairState).1=
      (.ok (.val rpairOther,.val rtAlias),rpairAfter) := rfl

theorem rpair_old_value_retained (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈
      (capturePairRun (rpairLegacy G) packedStepFrame 4 rpairWrite (.local .here) [] rpairState).2 := by
  first | omega | decide | skip
  apply capturePairRun_first
  exact captureRuntimeRun_return packedStepFrame [] _ rpairState rpairState (.val rtAlias) rfl

theorem rpair_pipeline_difference : (.val rtAlias : Source.RVal agEnv.layout agAliasTy)≠.val rpairOther := by
  first | omega | decide | skip
  intro same
  have paths := congrArg runtimeStoragePaths same
  exact (by decide : [agInner 0]≠[agInner 1]) paths

def rpairLate : Source.RExpr agEnv [agAliasTy,agAliasTy] agAliasTy :=
  .cond (.bool true) (.local .here) (.local (.there .here))

theorem rpair_legacy_late_halt (G : Source.Glob agEnv) :
    (capturePairRun (rpairLegacy G) packedStepFrame 2 rpairLate (.local .here) [] rpairState).1=
      (.error .timeout,rpairState) := rfl

theorem rpair_viaIR_early_halt (G : Source.Glob agEnv) :
    (capturePairRun (rpairViaIR G) packedStepFrame 2 rpairLate (.local .here) [] rpairState).1=
      (.error .timeout,rpairState) := rfl

theorem rpair_successful_first_kept (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈
      (capturePairRun (rpairLegacy G) packedStepFrame 2 rpairLate (.local .here) [] rpairState).2 := by
  first | omega | decide | skip
  apply capturePairRun_first
  exact captureRuntimeRun_return packedStepFrame [] _ rpairState rpairState (.val rtAlias) rfl

/-- Equal final errors do not imply equal produced-value observations. -/
theorem rpair_same_error_different_capture (G : Source.Glob agEnv) :
    [agInner 0]∈((capturePairRun (rpairLegacy G) packedStepFrame 2 rpairLate (.local .here) [] rpairState).2.map EntryReferenceScope.paths) ∧
    [agInner 0]∉((capturePairRun (rpairViaIR G) packedStepFrame 2 rpairLate (.local .here) [] rpairState).2.map EntryReferenceScope.paths) := by
  first | (simp only;done) | decide | omega | rfl | skip
  constructor
  · exact List.mem_map.mpr ⟨runtimeScope packedStepFrame (.val rtAlias),rpair_successful_first_kept G,rfl⟩
  · change [agInner 0]∉[[agInner 0,agInner 1],[agInner 0,agInner 1]]
    decide
end Solidity.Yul.Views.Controls
