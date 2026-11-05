import Solidity.Yul.Views.RetainedForLoopPost
import Solidity.Yul.Views.RetainedForLoopScopesControls

/-! Actual bool-local initialization reaches a shifted-reference tuple post,
from normal and continue bodies, before the next guard times out. Independent
prefix equations and capture membership establish post reachability. -/
namespace Solidity.Yul.Views.Controls

def rflpDeep : Nat → Source.RExpr agEnv [.bool,agAliasTy,agAliasTy] .bool
  | 0 => .bool true
  | n+1 => .cond (.bool true) (rflpDeep n) (.bool false)

def rflpGuards (G : Source.Glob agEnv) (n : Nat) : GuardObserver G packedStepFrame n (rflpDeep 14) where
  observe := fun prior l s => ((Source.EM.sub l (Source.evalE G packedStepFrame n (rflpDeep 14))).run s,prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

def rflpControl (flag : Bool) :
    Source.RStmt agEnv [] false ⟨true,false⟩ [.bool,agAliasTy,agAliasTy] [.bool,agAliasTy,agAliasTy] :=
  if flag then .cont else .skip

def rflpBodies (G : Source.Glob agEnv) (flag : Bool) (n : Nat) :
    StatementObserver G packedStepFrame n 0 none (rflpControl flag) where
  observe := fun prior l s => ((Source.execS G packedStepFrame n 0 none (rflpControl flag) l).run s,prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

def rflpObserver (G : Source.Glob agEnv) (flag : Bool) :=
  optionalForLoopStatementObserver G packedStepFrame 16 0 none (.declVar .bool)
    (.some (rflpDeep 14)) (.some (.tuple rflsArgs)) (rflpControl flag) (rflsInit G)
    (rflpGuards G) (rflsPosts G) (rflpBodies G flag) (lp:=false)

theorem rflp_guard_success (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rflpGuards G 15).observe prior rflsLocals rsOuter).1=(.ok (.val (.bool true),rflsLocals),rsOuter) := by
  rfl

theorem rflp_post_success (G : Source.Glob agEnv) (prior : List (EntryReferenceScope agEnv)) :
    ((rflsPosts G 15).observe prior rflsLocals rsOuter).1=(.ok rflsLocals,rsOuter) := by
  rfl

theorem rflp_source (G : Source.Glob agEnv) (flag : Bool) :
    ((rflpObserver G flag).observe [] agShrink.2.1 rsOuter).1=
      (Source.execS G packedStepFrame 17 0 none
        (.forLoop (l:=false) (u:=false) (.declVar .bool) (.some (rflpDeep 14)) (.some (.tuple rflsArgs))
          (rflpControl flag)) agShrink.2.1).run rsOuter :=
  (rflpObserver G flag).source [] agShrink.2.1 rsOuter

theorem rflp_late_timeout (G : Source.Glob agEnv) (flag : Bool) :
    ((rflpObserver G flag).observe [] agShrink.2.1 rsOuter).1=(.error .timeout,rsOuter) := by
  cases flag <;> rfl

theorem rflp_post_head (G : Source.Glob agEnv) (flag : Bool) :
    runtimeScope packedStepFrame (.val rtAlias)∈((rflpObserver G flag).observe [] agShrink.2.1 rsOuter).2 := by
  cases flag with
  | false =>
    exact optionalForLoop_normal_post_scopes G packedStepFrame 15 0 none (.declVar .bool)
      (.some (rflpDeep 14)) (.tuple rflsArgs) (rflpControl false) (rflsInit G) (rflpGuards G)
      (rflsPosts G) (rflpBodies G false) [] agShrink.2.1 rflsLocals rflsLocals rflsLocals rflsLocals
      rsOuter rsOuter rsOuter rsOuter (rfls_init_success G) rfl rfl rfl _
      (captureTuplePost_head G packedStepFrame 13 (.local (.there .here)) .nil
        [] rflsLocals rsOuter _ (.val rtAlias) rfl) (lp:=false)
  | true =>
    exact optionalForLoop_continue_post_scopes G packedStepFrame 15 0 none (.declVar .bool)
      (.some (rflpDeep 14)) (.tuple rflsArgs) (rflpControl true) (rflsInit G) (rflpGuards G)
      (rflsPosts G) (rflpBodies G true) [] agShrink.2.1 rflsLocals rflsLocals rflsLocals
      rsOuter rsOuter rsOuter rsOuter (rfls_init_success G) rfl rfl _
      (captureTuplePost_head G packedStepFrame 13 (.local (.there .here)) .nil
        [] rflsLocals rsOuter _ (.val rtAlias) rfl) (lp:=false)

end Solidity.Yul.Views.Controls
