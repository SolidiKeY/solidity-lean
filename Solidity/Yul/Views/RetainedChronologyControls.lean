import Solidity.Yul.Views.RetainedSourceTrace
import Solidity.Yul.Views.RetainedOwnershipRefresh
import Solidity.Yul.Views.RetainedStorageControls

namespace Solidity.Yul.Views.Controls

def rhFormAndShrink : Source.EM agEnv [] Unit := do
  let _ ← Source.indexLoc packedStepFrame (Source.Val.storRef (τ := .array .storage (.struct .storage agNode) none) (by rfl) rhLayout.path) 0
  let _ ← Source.indexLoc packedStepFrame (Source.Val.storRef (τ := .array .storage (.struct .storage agNode) none) (by rfl) rhLayout.path) 0
  Source.writeLen packedStepFrame rhLayout.path 0

def rhCalleeShrink : Source.EMState agEnv [] := ⟨.nil,agShrink.2.2⟩

/-- Both events now arise chronologically in ONE actual computation, not just
from their standalone existential witnesses. No producer-wide capture claim. -/
theorem rh_chronological : RetainedSourceTrace rhLayout rhFormAndShrink agApplied.2 [] (.ok (),rhCalleeShrink) rhHistory := by
  apply RetainedSourceTrace.bindOK (RetainedSourceTrace.index packedStepFrame agApplied.2 [] 0 rfl rh_formed)
  apply RetainedSourceTrace.bindOK (RetainedSourceTrace.index packedStepFrame agApplied.2 [rhEvent] 0 rfl rh_formed)
  exact RetainedSourceTrace.writeLen packedStepFrame agApplied.2 rhHistory rhLayout.path 0

theorem rh_suspended_caller_trace : RetainedSourceTrace rhLayout (Source.EM.sub (Source.Locals.nil (D := agEnv.layout)) rhFormAndShrink)
    agAliases [] (.ok ((),Source.Locals.nil),agShrink.2) rhHistory := RetainedSourceTrace.subOK agAliases.1 rh_chronological

theorem rh_suspended_caller_actual : (Source.EM.sub (Source.Locals.nil (D := agEnv.layout)) rhFormAndShrink).run agAliases =
    (.ok ((),Source.Locals.nil),agShrink.2) := rh_suspended_caller_trace.actual_run

def rhCalleePlan := rhPlan.relocalize (Source.Locals.nil (D := agEnv.layout))

theorem rh_raw_chronological : RetainedSourceTrace rhLayout (Source.applyOp packedStepFrame rhPlan.sourceOp)
    (Source.Locals.nil,agShrink.2.2) rhHistory (.ok (),(Source.Locals.nil,rhPlan.step.1.2.2)) rhHistory := by
  have trace := RetainedSourceTrace.rawWrite (layout := rhLayout) agFixed rhHistory 101 3
    (Source.Locals.nil,agShrink.2.2) rhResidual rfl rhCalleePlan
  rw [rhCalleePlan.nonstatic rfl] at trace
  rw [rhPlan.nonstatic rfl]
  exact trace

theorem rh_raw_sub_chronological : RetainedSourceTrace rhLayout
    (Source.EM.sub (Source.Locals.nil (D := agEnv.layout)) (Source.applyOp packedStepFrame rhPlan.sourceOp))
    agShrink.2 rhHistory (.ok ((),Source.Locals.nil),(agAliases.1,rhPlan.step.1.2.2)) rhHistory :=
  RetainedSourceTrace.subOK agAliases.1 rh_raw_chronological

/-- Re-erasing history loses the visited dormant child; this distinguishes a
current-locals-only or current-live-only implementation. -/
theorem rh_erased_history : retainedVisitIndices ([] : RetainedIndexHistory rhLayout) 0=[] ∧
    retainedVisitIndices rhHistory 0=[0] := ⟨rfl,rfl⟩

end Solidity.Yul.Views.Controls
