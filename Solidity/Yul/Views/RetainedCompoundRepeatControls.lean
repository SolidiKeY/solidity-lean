import Solidity.Yul.Views.RetainedArrayRead
import Solidity.Yul.Views.RetainedCompoundControls

/-! Repeated dormant-storage compound execution factored through actual target
and read runs. This closes the earlier budget-limited Source witness without
changing its308 result or the heartbeat budget. Physical transport is separate. -/
namespace Solidity.Yul.Views.Controls

theorem rcompound_repeat_target (G : Source.Glob agEnv) :
    (Source.evalLoc G packedStepFrame 4 rlTarget).run (rcompound G).1.2=
      (.ok (.stor rlPath),(rcompound G).1.2) := rfl

theorem rcompound_repeat_rhs (G : Source.Glob agEnv) :
    (Source.evalE G packedStepFrame 4 rlRhs).run (rcompound G).1.2=
      (.ok (.val (Source.intWrap rcU16 154)),(rcompound G).1.2) := by
  first | (simp only;done) | decide | omega | skip
  exact evalArray_readLoc_run G packedStepFrame 3 (.local .here) (by decide)
    (.const (Source.Q.ofInt 0)) (by decide) _ _ _ (.stor rlPath) (Source.intWrap rcU16 154)
    (rcompound_repeat_target G) (rcompound_read_after G)

theorem rcompound_repeated_storage (G : Source.Glob agEnv) :
    (captureCompoundRun G packedStepFrame 5 .add rlTarget rlRhs (by decide) (rcompound G).2 (rcompound G).1.2).1.1=
      .ok (.val (Source.intWrap rcU16 308)) := by
  first | (simp only;done) | decide | omega | skip
  unfold captureCompoundRun captureRuntimeRun
  simp only [rcompound_repeat_rhs]
  unfold captureLocationBindRun captureLocationRun captureRuntimeRun
  simp only [rcompound_repeat_target]
  rw [Source.Hoare.run_bind,rcompound_read_after]
  rfl
theorem rcompound_repeat_keeps_first_target (G : Source.Glob agEnv) :
    locationScope packedStepFrame (Source.Loc.stor (Γ:=[agAliasTy,agAliasTy]) (τ:=.int rcU16) rlPath)∈
      (captureCompoundRun G packedStepFrame 5 .add rlTarget rlRhs (by decide) (rcompound G).2 (rcompound G).1.2).2 := by
  first | (simp only;done) | decide | omega | skip
  apply captureCompoundRun_prefix
  exact rcompound_target_kept G

/-- A replay that loses the first update has the wrong observable result. -/
theorem rcompound_repeat_not_once (G : Source.Glob agEnv) :
    (captureCompoundRun G packedStepFrame 5 .add rlTarget rlRhs (by decide) (rcompound G).2 (rcompound G).1.2).1.1≠
      .ok (.val (Source.intWrap rcU16 154)) := by
  first | (simp only;done) | decide | omega | skip
  rw [rcompound_repeated_storage]
  intro same
  have numeric := congrArg (fun r : Except Source.Halt (Source.RVal agEnv.layout (.int rcU16)) =>
    match r with | .ok (.val (.int x _)) => x | _ => 0) same
  exact (by decide : (308 : Int)≠154) numeric
end Solidity.Yul.Views.Controls
