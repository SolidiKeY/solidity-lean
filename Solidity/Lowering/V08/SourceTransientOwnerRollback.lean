import Solidity.Lowering.V08.SourceTransientReentry

/-! UNVALIDATED DRAFT: owner-isolated source checkpoint/rollback application.
The imported re-entry module is ALSO UNVALIDATED. No checked dependency or
intrinsic target preservation is claimed. Frames and explicit transaction ends
are supplied Source operations, not proof that a call/transaction is admitted.
No evaluator, encoder, decoder or alternate world representation is introduced. -/
namespace Solidity.Lowering.V08.SourceTransientOwnerRollback
open Solidity Source
open SourceEmitControls
open SourceTransientBytesEmitControls (completed encoded eventSelector)
open SourceTransientReentry (nextOpening nextWritten)

/-- A supplied owner frame selects sender's cells in the SAME declaration Env.
This is not a proof of code installation, caller admission or call dispatch. -/
def ownerFrame : Source.Fr := {frame with this:=sender, sender:=self}
def bothWritten (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.transientUpdate (nextWritten pipeline bytes) sender scratch (.bool true)
/-- The real execution-component snapshot is after self's write, not before it. -/
def checkpoint (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.CallFrame :=
  (nextWritten pipeline bytes).ex.enter sender self frame.value binary false
/-- Explicit rollback affects the journaled execution component only. -/
def restored (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  {bothWritten pipeline bytes with
    ex:=(checkpoint pipeline bytes).rollback (bothWritten pipeline bytes).ex}
def ended (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.endExecution (restored pipeline bytes)

theorem owner_assignment (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) ownerFrame 4 SourceTransientEmitControls.setScratch).run
      (locals,nextWritten pipeline bytes) =
      (.ok (.val (.bool true)),(locals,bothWritten pipeline bytes)) := rfl

theorem both_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,bothWritten pipeline bytes) =
      (.ok (.val (.bool true)),(locals,bothWritten pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,bothWritten pipeline bytes) =
      (.ok (.val (.bool true)),(locals,bothWritten pipeline bytes)) := ⟨rfl,rfl⟩

/-- Consume the published rollback law at the reached snapshot and actual
sender update. The desired entire handler/world equation is not a premise. -/
theorem checkpoint_restore_execution (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (checkpoint pipeline bytes).rollback (bothWritten pipeline bytes).ex =
      (nextWritten pipeline bytes).ex := by
  exact Source.rollback_run (nextWritten pipeline bytes).ex
    [.transient sender (fun cells => cells.set scratch (some (.bool true)))]
    sender self frame.value binary false

theorem checkpoint_restore_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    restored pipeline bytes = nextWritten pipeline bytes := by
  unfold restored
  rw [checkpoint_restore_execution]
  rfl

theorem restored_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,restored pipeline bytes) =
      (.ok (.val (.bool true)),(locals,nextWritten pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,restored pipeline bytes) =
      (.ok (.val (.bool false)),(locals,nextWritten pipeline bytes)) := by
  rw [checkpoint_restore_machine]
  exact ⟨rfl,rfl⟩

theorem end_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,ended pipeline bytes) =
      (.ok (.val (.bool false)),(locals,ended pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,ended pipeline bytes) =
      (.ok (.val (.bool false)),(locals,ended pipeline bytes)) := by
  unfold ended
  rw [checkpoint_restore_machine]
  exact ⟨rfl,rfl⟩

/-- Retain the ENTIRE world and nonjournal machine components, rather than
claiming account framing implies balance preservation. Here only transient ops
actually execute. The complete event selector/payload/log tail remains exact. -/
theorem retained_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (bothWritten pipeline bytes).ex.world = (completed pipeline bytes).ex.world ∧
    (restored pipeline bytes).ex.world = (completed pipeline bytes).ex.world ∧
    (ended pipeline bytes).ex.world = (completed pipeline bytes).ex.world ∧
    (bothWritten pipeline bytes).heap = (completed pipeline bytes).heap ∧
    (restored pipeline bytes).heap = (completed pipeline bytes).heap ∧
    (ended pipeline bytes).heap = (completed pipeline bytes).heap ∧
    (bothWritten pipeline bytes).events = populated.events ∧
    (restored pipeline bytes).events = populated.events ∧
    (ended pipeline bytes).events = populated.events ∧
    (bothWritten pipeline bytes).logs =
      (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (restored pipeline bytes).logs =
      (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (ended pipeline bytes).logs =
      (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (bothWritten pipeline bytes).fnLocals = populated.fnLocals ∧
    (restored pipeline bytes).fnLocals = populated.fnLocals ∧
    (ended pipeline bytes).fnLocals = populated.fnLocals := by
  unfold ended
  rw [checkpoint_restore_machine]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Complete ordered owner/journal boundaries: first next-opening reset,
self write/snapshot, sender write, rollback to snapshot, final explicit end. -/
theorem ordered_boundaries (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((nextOpening pipeline bytes).ex.transient.cells self).read scratch = some (.bool false) ∧
    ((nextOpening pipeline bytes).ex.transient.cells sender).read scratch = some (.bool false) ∧
    (nextOpening pipeline bytes).ex.journal.length = 0 ∧
    ((nextWritten pipeline bytes).ex.transient.cells self).read scratch = some (.bool true) ∧
    ((nextWritten pipeline bytes).ex.transient.cells sender).read scratch = some (.bool false) ∧
    (checkpoint pipeline bytes).mark = 1 ∧
    ((bothWritten pipeline bytes).ex.transient.cells self).read scratch = some (.bool true) ∧
    ((bothWritten pipeline bytes).ex.transient.cells sender).read scratch = some (.bool true) ∧
    (bothWritten pipeline bytes).ex.journal.length = 2 ∧
    ((restored pipeline bytes).ex.transient.cells self).read scratch = some (.bool true) ∧
    ((restored pipeline bytes).ex.transient.cells sender).read scratch = some (.bool false) ∧
    (restored pipeline bytes).ex.journal.length = 1 ∧
    ((ended pipeline bytes).ex.transient.cells self).read scratch = some (.bool false) ∧
    ((ended pipeline bytes).ex.transient.cells sender).read scratch = some (.bool false) ∧
    (ended pipeline bytes).ex.journal.length = 0 := by
  unfold ended
  rw [checkpoint_restore_machine]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Preserve every existing populated numeric/cell/heap observation, with whole
world preservation above covering other fields too. No prior field is removed. -/
theorem complete_populated_vector (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((ended pipeline bytes).ex.world.accounts sender).balance.val = 93 ∧
    ((ended pipeline bytes).ex.world.accounts self).balance.val = 7 ∧
    ((ended pipeline bytes).ex.world.accounts self).code = some 0 ∧
    ((ended pipeline bytes).ex.world.accounts self).nonce = 1 ∧
    ((ended pipeline bytes).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (ended pipeline bytes).heap.next = 2 ∧
    (ended pipeline bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (ended pipeline bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (ended pipeline bytes).events = populated.events ∧
    (ended pipeline bytes).logs = (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (ended pipeline bytes).fnLocals = populated.fnLocals := by
  unfold ended
  rw [checkpoint_restore_machine]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Static refusal preserves the reached self-write snapshot. The timeout
below instead starts after BOTH writes and preserves that exact machine.
Neither halt silently rolls back or allocates/erases heap/log contents. -/
theorem static_owner_refusal (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {ownerFrame with static:=true} 4
      SourceTransientEmitControls.setScratch).run (locals,nextWritten pipeline bytes) =
      (.error (.revert []),(locals,nextWritten pipeline bytes)) := rfl

theorem owner_timeout (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) ownerFrame 0 SourceTransientEmitControls.setScratch).run
      (locals,bothWritten pipeline bytes) =
      (.error .timeout,(locals,bothWritten pipeline bytes)) := rfl

def earlierMark (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.CallFrame :=
  (nextOpening pipeline bytes).ex.enter sender self frame.value binary false

theorem wrong_mark (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (earlierMark pipeline bytes).rollback (bothWritten pipeline bytes).ex ≠
      (nextWritten pipeline bytes).ex := by
  intro same
  have counts := congrArg (fun ex => ex.journal.length) same
  change 0 = 1 at counts
  cases counts

theorem wrong_owner (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    bothWritten pipeline bytes ≠ SourceTransient.transientUpdate
      (nextWritten pipeline bytes) self scratch (.bool true) := by
  intro same
  have cells := congrArg (fun state : Source.St E =>
    (state.ex.transient.cells sender).read scratch) same
  change some (.bool true : Source.Val E.layout .bool) = some (.bool false) at cells
  cases cells

theorem wrong_dirty_reuse (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    restored pipeline bytes ≠ completed pipeline bytes := by
  rw [checkpoint_restore_machine]
  intro same
  have counts := congrArg (fun state : Source.St E => state.ex.journal.length) same
  change 1 = 2 at counts
  cases counts

/-- Actual first execution and both actual owner writes, followed by explicit
published rollback. This is a reached supplied-frame client, not a call engine. -/
theorem reached_client (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (SourceTransientBytesEmitControls.execution pipeline false bytes).run
      (Source.L0 E,SourceTransientEmitControls.opening) =
      (.ok (.normal locals),(Source.L0 E,completed pipeline bytes)) ∧
    (Source.evalE (global pipeline) frame 4 SourceTransientEmitControls.setScratch).run
      (locals,nextOpening pipeline bytes) =
      (.ok (.val (.bool true)),(locals,nextWritten pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 4 SourceTransientEmitControls.setScratch).run
      (locals,nextWritten pipeline bytes) =
      (.ok (.val (.bool true)),(locals,bothWritten pipeline bytes)) ∧
    restored pipeline bytes = nextWritten pipeline bytes :=
  ⟨SourceTransientBytesEmitControls.sequence_complete pipeline bytes 0,
    SourceTransientReentry.reentry_assignment pipeline bytes,
    owner_assignment pipeline bytes,checkpoint_restore_machine pipeline bytes⟩

/-- A distinct earlier outer mark uses the original self-owner context.
Unlike the wrong-mark negative, this is explicitly requested outer rollback. -/
def outerCheckpoint (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.CallFrame :=
  (nextOpening pipeline bytes).ex.enter self sender frame.value binary false

theorem outer_after_inner_execution (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (outerCheckpoint pipeline bytes).rollback (restored pipeline bytes).ex =
      (nextOpening pipeline bytes).ex := by
  rw [checkpoint_restore_machine]
  exact Source.rollback_run (nextOpening pipeline bytes).ex
    [.transient self (fun cells => cells.set scratch (some (.bool true)))]
    self sender frame.value binary false

/-- Two actual distinct snapshots: inner rollback retains self's write; the
separate outer rollback undoes it while preserving the complete old log/heap. -/
theorem nested_restore_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    restored pipeline bytes = nextWritten pipeline bytes ∧
    {restored pipeline bytes with
      ex:=(outerCheckpoint pipeline bytes).rollback (restored pipeline bytes).ex} =
      nextOpening pipeline bytes := by
  refine ⟨checkpoint_restore_machine pipeline bytes, ?_⟩
  rw [outer_after_inner_execution,checkpoint_restore_machine]
  rfl

#print axioms outer_after_inner_execution
#print axioms nested_restore_machine

#print axioms owner_assignment
#print axioms both_reads
#print axioms checkpoint_restore_execution
#print axioms checkpoint_restore_machine
#print axioms restored_reads
#print axioms end_reads
#print axioms retained_machine
#print axioms ordered_boundaries
#print axioms complete_populated_vector
#print axioms static_owner_refusal
#print axioms owner_timeout
#print axioms wrong_mark
#print axioms wrong_owner
#print axioms wrong_dirty_reuse
#print axioms reached_client
end Solidity.Lowering.V08.SourceTransientOwnerRollback
