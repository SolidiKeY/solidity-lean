import Solidity.Yul.Views.RetainedCompoundProducers
import Solidity.Yul.Views.RetainedLocationControls

/-! Actual dormant retained storage target controls for a single storage update,
static refusal and division panic, plus repeated local writes beside aliases. These Source executions are distinct
from residual/physical transport and compiler observations. -/
namespace Solidity.Yul.Views.Controls

def rcompound (G : Source.Glob agEnv) :=
  captureCompoundRun G packedStepFrame 5 .add rlTarget rlRhs (by decide) [] agShrink.2

theorem rcompound_result (G : Source.Glob agEnv) :
    (rcompound G).1.1=.ok (.val (Source.intWrap rcU16 154)) := rfl

theorem rcompound_read_after (G : Source.Glob agEnv) :
    (Source.readLoc packedStepFrame (.stor (Γ:=[agAliasTy,agAliasTy]) (τ:=.int rcU16) rlPath)).run (rcompound G).1.2=
      (.ok (Source.intWrap rcU16 154),(rcompound G).1.2) := rfl

theorem rcompound_target_kept (G : Source.Glob agEnv) :
    locationScope packedStepFrame (Source.Loc.stor (Γ:=[agAliasTy,agAliasTy]) (τ:=.int rcU16) rlPath)∈(rcompound G).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact captureCompoundRun_target G packedStepFrame 4 .add rlTarget rlRhs (by decide) [] agShrink.2 agShrink.2 agShrink.2
    (.val (Source.intWrap rcU16 77)) (.stor rlPath) rfl rfl

def rcompoundLocalState : Source.EMState agEnv [.int rcU16,agAliasTy,agAliasTy] :=
  (.cons (Source.intWrap rcU16 77) (.cons rtAlias (.cons rtAlias .nil)),agShrink.2.2)
def rcompoundLocal (G : Source.Glob agEnv) :=
  captureCompoundRun G packedStepFrame 3 .add (.local .here) (.local .here) (by decide) [] rcompoundLocalState

theorem rcompound_local_first (G : Source.Glob agEnv) :
    (rcompoundLocal G).1.1=.ok (.val (Source.intWrap rcU16 154)) := rfl

theorem rcompound_repeated_local (G : Source.Glob agEnv) :
    (captureCompoundRun G packedStepFrame 3 .add (.local .here) (.local .here) (by decide)
      (rcompoundLocal G).2 (rcompoundLocal G).1.2).1.1=
      .ok (.val (Source.intWrap rcU16 308)) := rfl

def rcompoundStatic : Source.Fr := {packedStepFrame with static:=true}

theorem rcompound_static_refusal (G : Source.Glob agEnv) :
    (captureCompoundRun G rcompoundStatic 5 .add rlTarget rlRhs (by decide) [] agShrink.2).1=
      (.error (.revert []),agShrink.2) := rfl

theorem rcompound_static_keeps_target (G : Source.Glob agEnv) :
    locationScope rcompoundStatic (Source.Loc.stor (Γ:=[agAliasTy,agAliasTy]) (τ:=.int rcU16) rlPath)∈
      (captureCompoundRun G rcompoundStatic 5 .add rlTarget rlRhs (by decide) [] agShrink.2).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact captureCompoundRun_target G rcompoundStatic 4 .add rlTarget rlRhs (by decide) [] agShrink.2 agShrink.2 agShrink.2
    (.val (Source.intWrap rcU16 77)) (.stor rlPath) rfl rfl

def rcompoundZero : Source.RExpr agEnv [agAliasTy,agAliasTy] (.int rcU16) :=
  .conv (.const (Source.Q.ofInt 0)) (.inl (by decide))

theorem rcompound_divzero (G : Source.Glob agEnv) :
    (captureCompoundRun G packedStepFrame 5 .div rlTarget rcompoundZero (by decide) [] agShrink.2).1=
      (.error (.revert (Source.panicData .divZero)),agShrink.2) := rfl

theorem rcompound_failed_postread (G : Source.Glob agEnv) :
    (Source.readLoc packedStepFrame (.stor (Γ:=[agAliasTy,agAliasTy]) (τ:=.int rcU16) rlPath)).run
      (captureCompoundRun G packedStepFrame 5 .div rlTarget rcompoundZero (by decide) [] agShrink.2).1.2=
      (.ok (Source.intWrap rcU16 77),agShrink.2) := rfl

theorem rcompound_wrong_unchanged (G : Source.Glob agEnv) :
    (rcompoundLocal G).1.2.1.get .here ≠ Source.intWrap rcU16 77 := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro same
  have numeric := congrArg (fun v : Source.Val agEnv.layout (.int rcU16) => match v with | .int x _ => x | _ => 0) same
  exact (by decide : (154 : Int)≠77) numeric
end Solidity.Yul.Views.Controls
