import Solidity.Yul.Views.RetainedForLoopScopes
import Solidity.Yul.Views.RetainedForOptionalBodyControls

/-! Actual initialization adds a bool local. A tuple-producing break body reads
a shifted reference local, then actual loop restoration removes the bool while
retaining the observed reference. Aliases still exist in caller locals. -/
namespace Solidity.Yul.Views.Controls

def rflsLocals : Source.Locals agEnv.layout [.bool,agAliasTy,agAliasTy] := .cons (.bool false) agShrink.2.1

def rflsArgs : Source.RArgs agEnv [.bool,agAliasTy,agAliasTy] [agAliasTy] :=
  .cons (.local (.there .here)) .nil

def rflsItems : Source.RItems agEnv [] false ⟨true,false⟩ [.bool,agAliasTy,agAliasTy] [.bool,agAliasTy,agAliasTy] :=
  .stmt (.expr (.tuple rflsArgs)) (.stmt .brk .nil)

def rflsInit (G : Source.Glob agEnv) : StatementObserver G packedStepFrame 16 0 none
    (.declVar .bool (Γ:=[agAliasTy,agAliasTy]) (R:=[]) (M:=false) (k:=⟨true,false⟩)) where
  observe := fun prior l s => ((Source.execS G packedStepFrame 16 0 none (.declVar .bool (R:=[]) (M:=false) (k:=⟨true,false⟩)) l).run s,prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

def rflsBodies (G : Source.Glob agEnv) (n : Nat) :
    StatementObserver G packedStepFrame n 0 none (.block rflsItems) :=
  match n with
  | 0 => zeroStatementObserver G packedStepFrame 0 none (.block rflsItems)
  | n+1 => blockStatementObserver G packedStepFrame n 0 none rflsItems
      (tupleItemsObserver G packedStepFrame n 0 none rflsArgs (.stmt .brk .nil))

def rflsPosts (G : Source.Glob agEnv) (n : Nat) := tuplePostObserver G packedStepFrame n rflsArgs

def rflsObserver (G : Source.Glob agEnv) :=
  optionalForLoopStatementObserver G packedStepFrame 16 0 none (.declVar .bool) .none (.some (.tuple rflsArgs))
    (.block rflsItems) (rflsInit G) PUnit.unit (rflsPosts G) (rflsBodies G) (lp:=false)

theorem rfls_init_success (G : Source.Glob agEnv) :
    ((rflsInit G).observe [] agShrink.2.1 rsOuter).1=(.ok (.normal rflsLocals),rsOuter) := by
  rfl

theorem rfls_restore : rflsLocals.restore [agAliasTy,agAliasTy]=.ok agShrink.2.1 := by
  rfl

theorem rfls_source (G : Source.Glob agEnv) :
    ((rflsObserver G).observe [] agShrink.2.1 rsOuter).1=
      (Source.execS G packedStepFrame 17 0 none
        (.forLoop (l:=false) (u:=false) (.declVar .bool) .none (.some (.tuple rflsArgs)) (.block rflsItems))
          agShrink.2.1).run rsOuter :=
  (rflsObserver G).source [] agShrink.2.1 rsOuter

theorem rfls_exit_restores (G : Source.Glob agEnv) :
    ((rflsObserver G).observe [] agShrink.2.1 rsOuter).1=(.ok (.normal agShrink.2.1),rsOuter) := by
  rfl

theorem rfls_body_head (G : Source.Glob agEnv) :
    runtimeScope packedStepFrame (.val rtAlias)∈((rflsObserver G).observe [] agShrink.2.1 rsOuter).2 := by
  exact optionalForLoop_body_scopes G packedStepFrame 15 0 none (.declVar .bool) .none (.some (.tuple rflsArgs))
    (.block rflsItems) (rflsInit G) PUnit.unit (rflsPosts G) (rflsBodies G)
    [] agShrink.2.1 rflsLocals rflsLocals rsOuter rsOuter rsOuter (rfls_init_success G) rfl _
    (captureTupleItems_head G packedStepFrame 10 0 none (.local (.there .here)) .nil
      (.stmt (.brk (R:=[]) (M:=false) (u:=false)) .nil)
      [] rflsLocals rsOuter _ (.val rtAlias) rfl) (lp:=false)

end Solidity.Yul.Views.Controls
