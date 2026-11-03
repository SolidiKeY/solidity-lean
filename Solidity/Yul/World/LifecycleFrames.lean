import Solidity.Yul.World.SelfDestruct
/-! Lifecycle metadata snapshot framing over actual existing journal outputs.
Entry marks come from the supplied real entry execution; callee reachability,
common logs and compiler/transaction adequacy remain separate obligations. -/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
variable {D : Layout} {L T : Address → SPath → STy}
/-- Restore entry metadata and journal rollback of the actual returned state.
This local snapshot operation is not G42 callee reachability. -/
def rollbackLifecycle (entry out : Lifecycle D L T)
    (receiver caller : Address) (value : Word) (input : Bytes) (static : Bool) : Lifecycle D L T :=
  {entry with execution := (entry.execution.enter receiver caller value input static).rollback out.execution}
theorem rollbackLifecycle_selfDestruct (entry out : Lifecycle D L T) (static : Bool) (a beneficiary : Address)
    (completed : selfDestruct entry static a beneficiary = some out)
    (receiver caller : Address) (value : Word) (input : Bytes) (frameStatic : Bool) :
    rollbackLifecycle entry out receiver caller value input frameStatic = entry := by
  simp only [rollbackLifecycle,
    selfDestruct_rollback entry out static a beneficiary completed receiver caller value input frameStatic]
theorem selfDestruct_journaled (entry out : Lifecycle D L T) (static : Bool) (a beneficiary : Address)
    (completed : selfDestruct entry static a beneficiary = some out) :
    ∃ ops : List (Op D L T), out.execution = entry.execution.run ops := by
  obtain ⟨_,execution,transferred,equal⟩ := (selfDestruct_success_iff entry out static a beneficiary).mp completed
  subst out
  exact destructTransfer_run entry.execution execution (entry.created a) a beneficiary transferred

theorem rollbackLifecycle_two_committed (entry first second : Lifecycle D L T) (static : Bool)
    (a beneficiary a2 beneficiary2 : Address)
    (completed : selfDestruct entry static a beneficiary = some first)
    (completed2 : selfDestruct first static a2 beneficiary2 = some second)
    (receiver caller : Address) (value : Word) (input : Bytes) (frameStatic : Bool) :
    rollbackLifecycle entry
      {second with execution := (first.execution.enter receiver caller value input frameStatic).commit second.execution}
      receiver caller value input frameStatic = entry := by
  obtain ⟨ops,actual⟩ := selfDestruct_journaled entry first static a beneficiary completed
  obtain ⟨ops2,actual2⟩ := selfDestruct_journaled first second static a2 beneficiary2 completed2
  have sequence : second.execution = entry.execution.run (ops ++ ops2) := by
    rw [actual2,actual,run_append]
  simp only [rollbackLifecycle,CallFrame.commit,sequence,rollback_run]
end Solidity.Yul.World
