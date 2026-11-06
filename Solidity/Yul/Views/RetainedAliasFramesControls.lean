import Solidity.Yul.Views.RetainedAliasFrames
import Solidity.Yul.Views.RetainedAliasSequenceControls

/-! Paired external-state rollback after two actual alias/storage programs.
These controls do not assert restoration of arbitrary caller locals or logs. -/
namespace Solidity.Yul.Views.Controls
open RetainedAliasOwnership RetainedAliasSequence RetainedAliasFrames

def rafChild (pipeline : Roadmap.Pipeline) :=
  companionRollback
    (companionEnter (raoPlan pipeline).after packedStepFrame.this packedStepFrame.sender
      packedStepFrame.value packedStepFrame.cd packedStepFrame.static)
    (paired (raoPlan pipeline) (rasSuccessPlan pipeline))

def rafOuter (pipeline : Roadmap.Pipeline) :=
  companionRollback
    (companionEnter (raoPlan pipeline).before packedStepFrame.this packedStepFrame.sender
      packedStepFrame.value packedStepFrame.cd packedStepFrame.static)
    (companionCommit
      (companionEnter (raoPlan pipeline).after packedStepFrame.this packedStepFrame.sender
        packedStepFrame.value packedStepFrame.cd packedStepFrame.static)
      (paired (raoPlan pipeline) (rasSuccessPlan pipeline)))

theorem raf_child (pipeline : Roadmap.Pipeline) : rafChild pipeline=(raoPlan pipeline).after :=
  child_rollback (raoPlan pipeline) (rasSuccessPlan pipeline) rfl rfl

theorem raf_outer (pipeline : Roadmap.Pipeline) : rafOuter pipeline=(raoPlan pipeline).before :=
  committed_outer_rollback (raoPlan pipeline) (rasSuccessPlan pipeline) rfl rfl

theorem raf_child_map (pipeline : Roadmap.Pipeline) :
    finiteEncode (raoPlan pipeline).next
      ((rafChild pipeline).source.world.accounts account).storage
      (fun slot => (rafChild pipeline).residual.cells (complementKey false account slot))=
        some (raoPlan pipeline).nextRaw :=
  child_reencode (raoPlan pipeline) (rasSuccessPlan pipeline) rfl rfl

theorem raf_outer_map (pipeline : Roadmap.Pipeline) :
    finiteEncode (raoPlan pipeline).old
      ((rafOuter pipeline).source.world.accounts account).storage
      (fun slot => (rafOuter pipeline).residual.cells (complementKey false account slot))=
        some (raoPlan pipeline).raw :=
  by
    rw [raf_outer]
    exact (raoPlan pipeline).encoded

/-- Child rollback retains the growth prefix's actual complementary word. -/
theorem raf_child_tail (pipeline : Roadmap.Pipeline) :
    (rafChild pipeline).residual.cells (complementKey false account 1000)=
      (⟨2^240,by decide⟩ : Roadmap.Word) := by
  first | (simp only;done) | skip
  rw [raf_child,←RetainedAliasOwnership.companion (raoPlan pipeline)]
  exact (rao_residual pipeline).1

/-- Outer rollback instead restores the previously residual packed tail. -/
theorem raf_outer_tail (pipeline : Roadmap.Pipeline) :
    (rafOuter pipeline).residual.cells (complementKey false account 1000)=
      (⟨77*2^32+2^240,by decide⟩ : Roadmap.Word) := by
  first | (simp only;done) | skip
  rw [raf_outer]
  change packedMask (raiPaths pipeline) rhRaw0 1000=_
  exact (rai_complement pipeline).2.2

/-- Replacing the parent prefix by the outer snapshot loses real ownership. -/
theorem raf_distinct (pipeline : Roadmap.Pipeline) : rafChild pipeline≠rafOuter pipeline := by
  first | (simp only;done) | skip
  intro lost
  have cell := congrArg (fun state => state.residual.cells (complementKey false account 1000)) lost
  dsimp only at cell
  rw [raf_child_tail,raf_outer_tail] at cell
  have different : (⟨2^240,by decide⟩ : Roadmap.Word)≠⟨77*2^32+2^240,by decide⟩ := by decide
  exact different cell
end Solidity.Yul.Views.Controls
