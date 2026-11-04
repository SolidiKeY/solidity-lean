import Solidity.Yul.Views.RetainedConditionalProducers
import Solidity.Yul.Views.RetainedTupleControls

/-! Actual selected conditional branches return nested tuples of dormant
storage refs. Swapped branches retain order, and an unselected branch that
would timeout is not evaluated. These controls do not infer historical index
formation or capture intermediates inside arbitrary branch expressions. -/
namespace Solidity.Yul.Views.Controls

def rcpOther : Source.Val agEnv.layout agAliasTy := .storRef (by rfl) (agInner 1)
def rcpState : Source.EMState agEnv [agAliasTy,agAliasTy] :=
  (.cons rtAlias (.cons rcpOther .nil),agShrink.2.2)
def rcpRightArgs : Source.RArgs agEnv [agAliasTy,agAliasTy] [agAliasTy,.tuple [agAliasTy]] :=
  .cons (.local (.there .here)) (.cons (.tuple (.cons (.local .here) .nil)) .nil)
def rcpLeft : Source.RVal agEnv.layout (.tuple [agAliasTy,.tuple [agAliasTy]]) :=
  .tuple (.cons (.val rtAlias) (.cons (.tuple (.cons (.val rcpOther) .nil)) .nil))
def rcpRight : Source.RVal agEnv.layout (.tuple [agAliasTy,.tuple [agAliasTy]]) :=
  .tuple (.cons (.val rcpOther) (.cons (.tuple (.cons (.val rtAlias) .nil)) .nil))

theorem rcp_actual_true (G : Source.Glob agEnv) :
    (Source.evalE G packedStepFrame 8 (.cond (.bool true) (.tuple rtArgs) (.tuple rcpRightArgs))).run rcpState=
      (.ok rcpLeft,rcpState) := rfl
theorem rcp_actual_false (G : Source.Glob agEnv) :
    (Source.evalE G packedStepFrame 8 (.cond (.bool false) (.tuple rtArgs) (.tuple rcpRightArgs))).run rcpState=
      (.ok rcpRight,rcpState) := rfl

theorem rcp_selected_nested (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame rcpRight∈
      (captureConditionalRun G packedStepFrame 8 (.bool false) (.tuple rtArgs) (.tuple rcpRightArgs) [] rcpState).2 := by
  first | omega | decide | skip
  exact captureConditionalRun_selected G packedStepFrame 7 (.bool false) (.tuple rtArgs) (.tuple rcpRightArgs)
    [] rcpState rcpState rcpState false rcpRight rfl rfl

theorem rcp_both_paths (G : Source.Glob agEnv) :
    ∃ scope∈(captureConditionalRun G packedStepFrame 8 (.bool false) (.tuple rtArgs) (.tuple rcpRightArgs) [] rcpState).2,
      scope.account=packedStepFrame.this ∧ agInner 1∈scope.paths ∧ agInner 0∈scope.paths := by
  first | omega | decide | skip
  exact ⟨runtimeScope packedStepFrame rcpRight,rcp_selected_nested G,rfl,List.mem_cons_self,
    List.mem_cons_of_mem _ List.mem_cons_self⟩

theorem rcp_order_negative : rcpLeft≠rcpRight := by
  first | omega | decide | skip
  intro same
  have paths := congrArg runtimeStoragePaths same
  exact (by decide : [agInner 0,agInner 1]≠[agInner 1,agInner 0]) paths

def rcpDangerous : Source.RExpr agEnv [agAliasTy,agAliasTy] agAliasTy :=
  .cond (.bool true) (.local .here) (.local (.there .here))

theorem rcp_unselected_would_halt (G : Source.Glob agEnv) :
    (Source.evalE G packedStepFrame 1 rcpDangerous).run rcpState=(.error .timeout,rcpState) := rfl

theorem rcp_unselected_not_run (G : Source.Glob agEnv) :
    (captureConditionalRun G packedStepFrame 2 (.bool true) (.local .here) rcpDangerous [] rcpState).1=
      (.ok (.val rtAlias),rcpState) := rfl

theorem rcp_selected_halt (G : Source.Glob agEnv) :
    (captureConditionalRun G packedStepFrame 2 (.bool false) (.local .here) rcpDangerous [] rcpState).1=
      (.error .timeout,rcpState) := rfl

theorem rcp_halt_keeps_condition (G : Source.Glob agEnv) :
    entryLocalScope packedStepFrame rcpState.1∈
      (captureConditionalRun G packedStepFrame 2 (.bool false) (.local .here) rcpDangerous [] rcpState).2 := by
  first | omega | decide | skip
  apply captureConditionalRun_keeps_condition
  exact List.mem_append_left _ List.mem_cons_self

theorem rcp_dedup (G : Source.Glob agEnv) :
    capturedVisitIndices rhLayout []
      (captureConditionalRun G packedStepFrame 8 (.bool false) (.tuple rtArgs) (.tuple rcpRightArgs) [] rcpState).2 0=[0,1] := rfl
end Solidity.Yul.Views.Controls
