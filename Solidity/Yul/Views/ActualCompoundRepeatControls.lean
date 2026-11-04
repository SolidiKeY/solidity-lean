import Solidity.Yul.Views.RetainedCompoundRepeatControls
import Solidity.Yul.Views.ActualScalarFrameControls

/-! Complete reached-state linkage for the second actual dormant compound
expression. Existing frame/registry laws are transported through that equality,
not through equality of selected return values. This is an inhabited finite
Source witness, not arbitrary expression or changing-ownership adequacy. -/
namespace Solidity.Yul.Views.Controls

theorem ac_second_source (G : Source.Glob agEnv) :
    (captureCompoundRun G packedStepFrame 5 .add rlTarget rlRhs (by decide) (rcompound G).2 (rcompound G).1.2).1=
      (.ok (.val (Source.intWrap rcU16 308)),afSecond.1.2) := by
  first | (simp only;done) | decide | omega | skip
  unfold captureCompoundRun captureRuntimeRun
  simp only [rcompound_repeat_rhs]
  unfold captureLocationBindRun captureLocationRun captureRuntimeRun
  simp only [rcompound_repeat_target]
  rw [Source.Hoare.run_bind,rcompound_read_after]
  unfold afSecond actualScalarWrite
  rw [as_same_compound_store G]
  rfl

theorem ac_second_eval (G : Source.Glob agEnv) :
    (Source.evalE G packedStepFrame 5 (.compound .add rlTarget rlRhs (by decide))).run (rcompound G).1.2=
      (.ok (.val (Source.intWrap rcU16 308)),afSecond.1.2) := by
  first | (simp only;done) | decide | omega | skip
  rw [← captureCompoundRun_source G packedStepFrame 5 .add rlTarget rlRhs (by decide) (rcompound G).2]
  exact ac_second_source G
theorem ac_member : rhC3∈rhOld := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [rh_old_list]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem ac_first_view : finiteView rhOld (asWrite.1.2.2.ex.world.accounts account).storage asWrite.2 :=
  actualScalarWrite_registry_view packedStepFrame agShrink.2 rhOld rhC3 ac_member
    ((packedSeparationCheck_iff _).mp rh_separated) rhRaw0 rh_view _ rfl rfl

theorem ac_first_complement : packedMask rhOld asWrite.2=packedMask rhOld rhRaw0 :=
  actualScalarWrite_registry_complement packedStepFrame agShrink.2 rhOld rhC3 ac_member rhRaw0 _ rfl

theorem ac_second_reencode (G : Source.Glob agEnv) :
    finiteEncode rhOld
      ((((Source.evalE G packedStepFrame 5 (.compound .add rlTarget rlRhs (by decide))).run (rcompound G).1.2).2.2.ex.world.accounts account).storage)
      (fun q=>rhResidual.cells (complementKey false account q))=some afSecond.2 := by
  first | (simp only;done) | decide | omega | skip
  rw [ac_second_eval]
  apply actualScalarWrite_registry_reencode packedStepFrame asWrite.1.2 rhOld rhC3 ac_member
    ((packedSeparationCheck_iff _).mp rh_separated) asWrite.2 ac_first_view (Source.intWrap rcU16 308) rfl rfl rhResidual
  rw [ac_first_complement]
  rfl

theorem ac_first_eval_state (G : Source.Glob agEnv) :
    ((Source.evalE G packedStepFrame 5 (.compound .add rlTarget rlRhs (by decide))).run agShrink.2).2=asWrite.1.2 := by
  first | (simp only;done) | decide | omega | skip
  rw [← captureCompoundRun_source G packedStepFrame 5 .add rlTarget rlRhs (by decide) []]
  exact (as_same_compound_store G).symm

theorem ac_actual_child_commit_outer_rollback (G : Source.Glob agEnv) :
    let first := (Source.evalE G packedStepFrame 5 (.compound .add rlTarget rlRhs (by decide))).run agShrink.2
    let second := (Source.evalE G packedStepFrame 5 (.compound .add rlTarget rlRhs (by decide))).run first.2
    companionRollback afFrame
      (companionCommit (companionEnter ⟨first.2.2.ex,rhResidual⟩ packedStepFrame.this packedStepFrame.sender
        packedStepFrame.value packedStepFrame.cd packedStepFrame.static)
        ⟨second.2.2.ex,rhResidual⟩)=afBefore := by
  first | (simp only;done) | decide | omega | skip
  dsimp only
  rw [ac_first_eval_state]
  have second : (Source.evalE G packedStepFrame 5 (.compound .add rlTarget rlRhs (by decide))).run asWrite.1.2=
      (.ok (.val (Source.intWrap rcU16 308)),afSecond.1.2) := by
    rw [as_same_compound_store G]
    exact ac_second_eval G
  rw [second]
  exact af_child_commit_outer_rollback
end Solidity.Yul.Views.Controls
