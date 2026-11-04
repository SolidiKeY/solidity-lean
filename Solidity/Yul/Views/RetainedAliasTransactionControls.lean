import Solidity.Yul.Views.RetainedAliasTransaction
import Solidity.Yul.Views.RetainedAliasSequenceControls

/-! The actual two-program Source result is finalized only after success.
A late static halt retains the earlier source undo prefix and residual map.
The examples use seeded kernel storage, not compiler constructor evidence. -/
namespace Solidity.Yul.Views.Controls
open RetainedAliasTransaction

theorem rat_map (pipeline : Roadmap.Pipeline) :
    finiteEncode (rasSuccessPlan pipeline).next
      ((execute (raoPlan pipeline) (rasSuccessPlan pipeline)).1.2.2.ex.world.accounts account).storage
      (fun slot => (execute (raoPlan pipeline) (rasSuccessPlan pipeline)).2.cells (complementKey false account slot))=
        some (rasSuccessPlan pipeline).nextRaw :=
  persistent (raoPlan pipeline) (rasSuccessPlan pipeline) rfl rfl

theorem rat_reset (pipeline : Roadmap.Pipeline) (address : Roadmap.Address) (slot : Roadmap.Word) :
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline)).1.2.2.ex.transient=Source.Transient.empty ∧
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline)).2.cells (complementKey true address slot)=0 ∧
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline)).1.2.2.ex.journal=[] ∧
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline)).2.journal=[] :=
  reset (raoPlan pipeline) (rasSuccessPlan pipeline) rfl rfl address slot

theorem rat_late_static (pipeline : Roadmap.Pipeline) :
    execute (raoPlan pipeline) (rasPlan pipeline)=
      ((.error (.revert []),rasState pipeline),(RetainedAliasOwnership.execute (raoPlan pipeline)).2) := by
  first | (simp only;done) | skip
  unfold execute
  rw [ras_late_static]

/-- Premature endTx on late halt would discard a genuine source undo prefix. -/
theorem rat_keeps_undo (pipeline : Roadmap.Pipeline) :
    (execute (raoPlan pipeline) (rasPlan pipeline)).1.2.2.ex.journal≠[] := by
  first | (simp only;done) | skip
  rw [rat_late_static]
  change (RetainedAliasOwnership.execute (raoPlan pipeline)).1.2.2.ex.journal≠[]
  rw [RetainedAliasOwnership.nonstatic (raoPlan pipeline) rfl]
  intro erased
  have length := congrArg List.length erased
  dsimp only at length
  rw [Source.ExecState.journal_apply] at length
  change _=0 at length
  omega

/-- Late failure retains the complete first map, not the second requested shrink. -/
theorem rat_prefix_map (pipeline : Roadmap.Pipeline) :
    finiteEncode (raoPlan pipeline).next
      ((execute (raoPlan pipeline) (rasPlan pipeline)).1.2.2.ex.world.accounts account).storage
      (fun slot => (execute (raoPlan pipeline) (rasPlan pipeline)).2.cells (complementKey false account slot))=
        some (raoPlan pipeline).nextRaw := by
  rw [rat_late_static]
  exact RetainedAliasOwnership.reencode (raoPlan pipeline) rfl

/-- Finalization updates only ex: locals and all other Source store fields persist. -/
theorem rat_administration (pipeline : Roadmap.Pipeline) :
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline)).1.2.1=
      (RetainedAliasOwnership.execute (rasSuccessPlan pipeline)).1.2.1 ∧
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline)).1.2.2.heap=
      (RetainedAliasOwnership.execute (rasSuccessPlan pipeline)).1.2.2.heap ∧
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline)).1.2.2.logs=
      (RetainedAliasOwnership.execute (rasSuccessPlan pipeline)).1.2.2.logs ∧
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline)).1.2.2.events=
      (RetainedAliasOwnership.execute (rasSuccessPlan pipeline)).1.2.2.events ∧
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline)).1.2.2.fnLocals=
      (RetainedAliasOwnership.execute (rasSuccessPlan pipeline)).1.2.2.fnLocals := by
  rw [success (raoPlan pipeline) (rasSuccessPlan pipeline) rfl rfl]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem rat_safe (pipeline : Roadmap.Pipeline) : Source.MemOK agEnv agState.2.heap.ty
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline)).1.2 :=
  RetainedAliasTransaction.MemOK (raoPlan pipeline) (rasSuccessPlan pipeline) _ ra_initial_safe

end Solidity.Yul.Views.Controls
