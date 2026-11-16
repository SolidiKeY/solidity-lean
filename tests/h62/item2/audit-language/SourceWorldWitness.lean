import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Source.World

/-!
Guarded regression: commit must retain writes while rollback restores the frame
mark, including writes in committed inner calls; transaction end clears transient
storage. Full imported telescopes use nonempty operation lists and actual frame
functions, not independently inhabited frame assumptions. Sixteen frozen named
headers match; transfer_none_iff changed and remains uncredited. Account balance
representation evolved, so no old/new monetary meaning equivalence is inferred.
These are current source journal clients, not compiler or EVM frame correctness.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceWorldWitness
open Solidity.Source
open Solidity.Roadmap (Address Word)

def layout : Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
def types : Address → SPath → STy := fun _ _ => .bool
def sender : Address := ⟨0, by decide⟩
def recipient : Address := ⟨1, by decide⟩
def value : Word := ⟨1, by decide⟩
def path : SPath := ⟨⟨some "C", "flag"⟩, []⟩
def initial : ExecState layout types types :=
  ⟨⟨fun a => ⟨if a == sender then 10 else 0, 0, none, Storage.empty⟩⟩, Transient.empty, []⟩
def replacement : Account layout (types sender) :=
  { initial.world.accounts sender with nonce := 1 }
def writtenStorage : Storage layout (types sender) := Storage.empty.write path (.bool true)
def firstOp : Op layout types types := .account sender (fun a => { a with nonce := a.nonce + 1 })
def firstOps : List (Op layout types types) :=
  [firstOp, .transient sender (fun s => s.write path (.bool true))]
def secondOps : List (Op layout types types) :=
  [.account recipient (fun a => { a with nonce := a.nonce + 2 }),
   .transient recipient (fun s => s.write path (.bool true))]
def frame : CallFrame := initial.enter sender recipient value [1, 2] false
def transferred : ExecState layout types types :=
  (initial.apply (.account sender (fun a => a.withBalance 9))).apply
    (.account recipient (fun a => a.withBalance 1))

theorem world_get_full : hypotheses_of% World.set_get := by
  exact ⟨layout, types, initial.world, sender, replacement, True.intro⟩
#verify_hypotheses world_get_full for Solidity.Source.World.set_get
#print axioms world_get_full

theorem world_other_full : hypotheses_of% World.set_other := by
  exact ⟨layout, types, initial.world, sender, recipient, by decide, replacement, True.intro⟩
#verify_hypotheses world_other_full for Solidity.Source.World.set_other
#print axioms world_other_full

theorem world_restore_full : hypotheses_of% World.set_restore := by
  exact ⟨layout, types, initial.world, sender, replacement, True.intro⟩
#verify_hypotheses world_restore_full for Solidity.Source.World.set_restore
#print axioms world_restore_full

theorem transient_restore_full : hypotheses_of% Transient.set_restore := by
  exact ⟨layout, types, initial.transient, sender, writtenStorage, True.intro⟩
#verify_hypotheses transient_restore_full for Solidity.Source.Transient.set_restore
#print axioms transient_restore_full

theorem undo_full : hypotheses_of% ExecState.undo_apply := by
  exact ⟨layout, types, types, initial, firstOp, True.intro⟩
#verify_hypotheses undo_full for Solidity.Source.ExecState.undo_apply
#print axioms undo_full

theorem journal_step_full : hypotheses_of% ExecState.journal_apply := by
  exact ⟨layout, types, types, initial, firstOp, True.intro⟩
#verify_hypotheses journal_step_full for Solidity.Source.ExecState.journal_apply
#print axioms journal_step_full

theorem journal_run_full : hypotheses_of% ExecState.journal_run := by
  exact ⟨layout, types, types, initial, firstOps, True.intro⟩
#verify_hypotheses journal_run_full for Solidity.Source.ExecState.journal_run
#print axioms journal_run_full

theorem undo_run_full : hypotheses_of% ExecState.undoN_run := by
  exact ⟨layout, types, types, initial, firstOps, True.intro⟩
#verify_hypotheses undo_run_full for Solidity.Source.ExecState.undoN_run
#print axioms undo_run_full

theorem rollback_full : hypotheses_of% rollback_run := by
  exact ⟨layout, types, types, initial, firstOps, sender, recipient, value, [1, 2], false, True.intro⟩
#verify_hypotheses rollback_full for Solidity.Source.rollback_run
#print axioms rollback_full

theorem inner_full : hypotheses_of% rollback_inner := by
  exact ⟨layout, types, types, initial, firstOps, secondOps, initial.enter, (initial.run firstOps).enter, rfl, rfl, sender, recipient, value, [1, 2], false, True.intro⟩
#verify_hypotheses inner_full for Solidity.Source.rollback_inner
#print axioms inner_full

theorem append_full : hypotheses_of% run_append := by
  exact ⟨layout, types, types, initial, firstOps, secondOps, True.intro⟩
#verify_hypotheses append_full for Solidity.Source.run_append
#print axioms append_full

theorem outer_commit_full : hypotheses_of% rollback_outer_after_commit := by
  exact ⟨layout, types, types, initial, firstOps, secondOps, [firstOp], sender, recipient, value, [1, 2], false, True.intro⟩
#verify_hypotheses outer_commit_full for Solidity.Source.rollback_outer_after_commit
#print axioms outer_commit_full

theorem commit_full : hypotheses_of% commit_keeps := by
  exact ⟨layout, types, types, frame, initial, True.intro⟩
#verify_hypotheses commit_full for Solidity.Source.commit_keeps
#print axioms commit_full

theorem transfer_rollback_full : hypotheses_of% rollback_transfer := by
  exact ⟨layout, types, types, initial, transferred, sender, recipient, by decide, value, rfl, sender, recipient, [1, 2], false, True.intro⟩
#verify_hypotheses transfer_rollback_full for Solidity.Source.rollback_transfer
#print axioms transfer_rollback_full

theorem end_world_full : hypotheses_of% endTx_world := by
  exact ⟨layout, types, types, initial.run firstOps, True.intro⟩
#verify_hypotheses end_world_full for Solidity.Source.endTx_world
#print axioms end_world_full

theorem end_transient_full : hypotheses_of% endTx_transient := by
  exact ⟨layout, types, types, initial.run firstOps, sender, path, True.intro⟩
#verify_hypotheses end_transient_full for Solidity.Source.endTx_transient
#print axioms end_transient_full

/-- Commit and rollback cannot agree when the actual run changes the state. -/
theorem changed_commit_differs {D : Layout} {L T : Address → SPath → STy}
    (s : ExecState D L T) (ops : List (Op D L T)) (a c : Address) (v : Word)
    (input : List UInt8) (static : Bool) (changed : s.run ops ≠ s) :
    (s.enter a c v input static).commit (s.run ops) ≠
      (s.enter a c v input static).rollback (s.run ops) := by
  rw [CallFrame.commit, rollback_run]
  exact changed

example : initial.run firstOps ≠ initial := by
  intro same
  have nonce := congrArg (fun s => (s.world.accounts sender).nonce) same
  change (1 : Nat) = 0 at nonce
  cases nonce
example : (initial.run firstOps).journal.length = 2 := rfl
example : ((initial.run firstOps).transient.cells sender).read path = some (.bool true) := rfl
example : ((initial.run firstOps).endTx.transient.cells sender).read path = some (.bool false) := rfl
example : frame.rollback (initial.run firstOps) = initial :=
  rollback_run initial firstOps sender recipient value [1, 2] false

#print axioms changed_commit_differs
end Solidity.H62.AuditLanguage.SourceWorldWitness
