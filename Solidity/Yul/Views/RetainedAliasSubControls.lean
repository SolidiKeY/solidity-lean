import Solidity.Yul.Views.RetainedAliasSub
import Solidity.Yul.Views.RetainedAliasSequenceControls

/-! Saved caller aliases remain distinct from overwritten callee locals.
Source substitution retains the actual reached persistent map and journal. -/
namespace Solidity.Yul.Views.Controls
open RetainedAliasSub

theorem rasub_caller (pipeline : Roadmap.Pipeline) :
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline) raState.1).1.2.1=raState.1 :=
  caller _ _ _

theorem rasub_alias (pipeline : Roadmap.Pipeline) :
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline) raState.1).1.2.1.get .here=
      Source.Val.storRef (τ:=agAliasTy) (by rfl) (agInner 1) := by
  rw [rasub_caller]
  rfl

/-- Replacing saved caller locals by callee aliases loses dormant child1. -/
theorem rasub_not_callee (pipeline : Roadmap.Pipeline) :
    (execute (raoPlan pipeline) (rasSuccessPlan pipeline) raState.1).1.2.1≠raAfter.1 := by
  first | (simp only;done) | skip
  rw [rasub_caller]
  intro lost
  have value := congrArg (fun locals => locals.get .here) lost
  have paths := congrArg valueStoragePaths value
  change [agInner 1]=[agInner 0] at paths
  have different : [agInner 1]≠[agInner 0] := by decide
  exact different paths

theorem rasub_map (pipeline : Roadmap.Pipeline) :
    finiteEncode (rasSuccessPlan pipeline).next
      ((execute (raoPlan pipeline) (rasSuccessPlan pipeline) raState.1).1.2.2.ex.world.accounts account).storage
      (fun slot => (execute (raoPlan pipeline) (rasSuccessPlan pipeline) raState.1).2.cells (complementKey false account slot))=
        some (rasSuccessPlan pipeline).nextRaw := reencode _ _ _ rfl rfl

theorem rasub_static (pipeline : Roadmap.Pipeline) :
    execute (raoPlan pipeline) (rasPlan pipeline) raState.1=
      ((.error (.revert []),(raState.1,(RetainedAliasOwnership.execute (raoPlan pipeline)).1.2.2)),
        (RetainedAliasOwnership.execute (raoPlan pipeline)).2) := late_static _ _ _ rfl rfl

theorem rasub_static_map (pipeline : Roadmap.Pipeline) :
    finiteEncode (raoPlan pipeline).next
      ((execute (raoPlan pipeline) (rasPlan pipeline) raState.1).1.2.2.ex.world.accounts account).storage
      (fun slot => (execute (raoPlan pipeline) (rasPlan pipeline) raState.1).2.cells (complementKey false account slot))=
        some (raoPlan pipeline).nextRaw := by
  rw [rasub_static]
  exact RetainedAliasOwnership.reencode _ rfl
end Solidity.Yul.Views.Controls
