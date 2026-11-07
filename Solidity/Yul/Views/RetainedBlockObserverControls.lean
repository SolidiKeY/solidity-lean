import Solidity.Yul.Views.RetainedBlockObserver
import Solidity.Yul.Views.RetainedTupleCompositionControls

/-! Observed tuple producers survive actual block closure and early control.
The outer tail contains a declaration that would halt if reached; actual break,
continue and return skip it. Aliases also remain in locals, so these fixtures
make no exclusive-provenance or recursive-completeness assertion. -/
namespace Solidity.Yul.Views.Controls

def rboInner (control : Source.RStmt agEnv [] false ⟨true,false⟩
    [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) :
    Source.RItems agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy] :=
  .stmt (.expr (.tuple rtArgs)) (.stmt control .nil)

def rboTail : Source.RItems agEnv [] false ⟨true,false⟩
    [agAliasTy,agAliasTy] [agAliasTy,agAliasTy,agAliasTy] := .stmt (.declVar agAliasTy) .nil

def rboRest : Source.RItems agEnv [] false ⟨true,false⟩
    [agAliasTy,agAliasTy] [agAliasTy,agAliasTy,agAliasTy] :=
  .stmt (.expr (.tuple rtArgs)) rboTail

def rboInnerObserver (G : Source.Glob agEnv) (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) :=
  tupleItemsObserver G packedStepFrame 9 0 none rtArgs (.stmt control .nil)
    (R:=[]) (M:=false) (k:=⟨true,false⟩)

def rboObserver (G : Source.Glob agEnv) (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) :=
  statementThenObserver G packedStepFrame 10 0 none (.block (rboInner control)) rboRest
    (blockStatementObserver G packedStepFrame 9 0 none (rboInner control) (rboInnerObserver G control))
    (tupleItemsObserver G packedStepFrame 10 0 none rtArgs rboTail)

def rboCapture (G : Source.Glob agEnv) (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (prior : List (EntryReferenceScope agEnv)) :=
  (rboObserver G control).observe prior agShrink.2.1 rsOuter

theorem rbo_exact_source (G : Source.Glob agEnv) (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (prior : List (EntryReferenceScope agEnv)) :
    (rboCapture G control prior).1=
      (Source.execItems G packedStepFrame 11 0 none
        (.stmt (.block (rboInner control)) rboRest) agShrink.2.1).run rsOuter :=
  (rboObserver G control).source prior agShrink.2.1 rsOuter

theorem rbo_break (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rboCapture G .brk prior).1=(.ok (.brk agShrink.2.1),rsOuter) := by
  rfl

theorem rbo_continue (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rboCapture G .cont prior).1=(.ok (.cont agShrink.2.1),rsOuter) := by
  rfl

theorem rbo_return (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rboCapture G (.ret rfl) prior).1=(.ok (.ret agShrink.2.1),rsOuter) := by
  rfl

theorem rbo_captured_before_control (G : Source.Glob agEnv) (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy])
    (prior : List (EntryReferenceScope agEnv)) :
    runtimeScope packedStepFrame (.val rtAlias)∈(rboCapture G control prior).2 := by
  exact observeStatementThen_prefix G packedStepFrame 10 0 none (.block (rboInner control)) rboRest
    (blockStatementObserver G packedStepFrame 9 0 none (rboInner control) (rboInnerObserver G control))
    (tupleItemsObserver G packedStepFrame 10 0 none rtArgs rboTail) prior agShrink.2.1 rsOuter _
    (captureTupleItems_head G packedStepFrame 5 0 none (.local .here)
      (.cons (.tuple (.cons (.local (.there .here)) .nil)) .nil) (.stmt control .nil)
      prior agShrink.2.1 rsOuter _ (.val rtAlias) rfl)

/-- The same inherited-scope contract holds for arbitrary actual controls. -/
theorem rbo_prior (G : Source.Glob agEnv) (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy]) (prior : List (EntryReferenceScope agEnv))
    (scope) (member : scope∈prior) : scope∈(rboCapture G control prior).2 :=
  (rboObserver G control).prior prior agShrink.2.1 rsOuter scope member

/-- A normal block runs the real tail and preserves its declaration halt. -/
theorem rbo_normal_then_halt (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rboCapture G .skip prior).1=(.error (.stuck "no default value"),rsOuter) := by
  rfl

/-- A second block layer reuses the exact composed ItemsObserver. -/
def rboNested (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy])
    (prior : List (EntryReferenceScope agEnv)) :=
  (blockStatementObserver G packedStepFrame 11 0 none
    (.stmt (.block (rboInner control)) rboRest) (rboObserver G control)).observe prior agShrink.2.1 rsOuter

theorem rbo_nested_break (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rboNested G .brk prior).1=(.ok (.brk agShrink.2.1),rsOuter) := by
  rfl

theorem rbo_nested_halt (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rboNested G .skip prior).1=(.error (.stuck "no default value"),rsOuter) := by
  rfl

theorem rbo_nested_scopes (G : Source.Glob agEnv)
    (control : Source.RStmt agEnv [] false ⟨true,false⟩ [agAliasTy,agAliasTy] [agAliasTy,agAliasTy])
    (prior : List (EntryReferenceScope agEnv)) : (rboNested G control prior).2=(rboCapture G control prior).2 := rfl

/-- An actual successful declaration extends the inner context before close. -/
def rboExtendedBody : Source.RItems agEnv [] false Source.SCtx.body
    [agAliasTy,agAliasTy] [.bool,agAliasTy,agAliasTy] :=
  .stmt (.expr (.tuple rtArgs)) (.stmt (.declVar .bool) .nil)

def rboExtended (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :=
  (blockStatementObserver G packedStepFrame 9 0 none rboExtendedBody
    (tupleItemsObserver G packedStepFrame 9 0 none rtArgs (.stmt (.declVar .bool) .nil))).observe
    prior agShrink.2.1 rsOuter

theorem rbo_restores_context (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    (rboExtended G prior).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  rfl

end Solidity.Yul.Views.Controls
