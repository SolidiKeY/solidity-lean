import Solidity.Yul.Views.RetainedAliasReadControls

namespace Solidity.Yul.Views.Controls

def rhMakeAlias : Source.EM agEnv [] (Source.Val agEnv.layout agAliasTy) := do
  let _ ← Source.indexLoc packedStepFrame (Source.Val.storRef (τ := .array .storage (.struct .storage agNode) none) (by rfl) rhLayout.path) 0
  let _ ← Source.indexLoc packedStepFrame (Source.Val.storRef (τ := .array .storage (.struct .storage agNode) none) (by rfl) rhLayout.path) 0
  Source.readLoc packedStepFrame (.stor (agInner 0))

def rhObserveCaller : Source.EM agEnv [agAliasTy,agAliasTy] Nat := do
  Source.writeLen packedStepFrame rhLayout.path 0
  let _ ← Source.EM.sub (Source.Locals.nil (D := agEnv.layout)) (Source.applyOp packedStepFrame rhPlan.sourceOp)
  let alias ← Source.readLoc packedStepFrame (.local .here)
  Source.lengthOf packedStepFrame alias

def rhClosedCaller : Source.EM agEnv [] (Nat × Source.Locals agEnv.layout [agAliasTy,agAliasTy]) := do
  let alias ← rhMakeAlias
  Source.EM.sub (.cons alias (.cons alias .nil)) rhObserveCaller

/-- Reference VALUES used to initialize the caller locals now come from the
actual prior index+member read, rather than assumed initial alias locals. -/
theorem rh_make_alias_trace : RetainedSourceTrace rhLayout rhMakeAlias agApplied.2 []
    (.ok (Source.Val.storRef (by rfl) (agInner 0)),agApplied.2) rhHistory := by
  apply RetainedSourceTrace.bindOK (RetainedSourceTrace.index packedStepFrame agApplied.2 [] 0 rfl rh_formed)
  apply RetainedSourceTrace.bindOK (RetainedSourceTrace.index packedStepFrame agApplied.2 [rhEvent] 0 rfl rh_formed)
  exact RetainedSourceTrace.readLoc packedStepFrame agApplied.2 rhHistory (.stor (agInner 0))

def rhAfterCall : Source.EMState agEnv [agAliasTy,agAliasTy] := (agAliases.1,rhPlan.step.1.2.2)
theorem rh_after_call_eq : rhAfterCall=rhPlan.step.1.2 := Prod.ext rh_actual_source_locals.symm rfl

theorem rh_observe_trace : RetainedSourceTrace rhLayout rhObserveCaller agAliases rhHistory (.ok 3,rhAfterCall) rhHistory := by
  apply RetainedSourceTrace.bindOK (RetainedSourceTrace.writeLen packedStepFrame agAliases rhHistory rhLayout.path 0)
  apply RetainedSourceTrace.bindOK rh_raw_sub_chronological
  apply RetainedSourceTrace.bindOK (RetainedSourceTrace.readLoc packedStepFrame rhAfterCall rhHistory (Source.Loc.local .here))
  have trace := RetainedSourceTrace.lengthOf (layout := rhLayout) packedStepFrame rhAfterCall rhHistory
    (Source.Val.storRef (τ := agAliasTy) (by rfl) (agInner 0))
  have length : (Source.lengthOf packedStepFrame (Source.Val.storRef (τ := agAliasTy) (by rfl) (agInner 0))).run rhAfterCall=(.ok 3,rhAfterCall) := by
    change (Source.readLen packedStepFrame (agInner 0)).run rhAfterCall=(.ok 3,rhAfterCall)
    rw [rh_after_call_eq]
    exact rh_inner_length3
  rw [length] at trace
  exact trace

theorem rh_closed_trace : RetainedSourceTrace rhLayout rhClosedCaller agApplied.2 []
    (.ok (3,agAliases.1),(Source.Locals.nil,rhAfterCall.2)) rhHistory := by
  apply RetainedSourceTrace.bindOK rh_make_alias_trace
  exact RetainedSourceTrace.subOK Source.Locals.nil rh_observe_trace

theorem rh_closed_source_run : rhClosedCaller.run agApplied.2=(.ok (3,agAliases.1),(Source.Locals.nil,rhAfterCall.2)) := rh_closed_trace.actual_run

end Solidity.Yul.Views.Controls
