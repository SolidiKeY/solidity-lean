import Solidity.Lowering.V08.SourceTransientOwnerCommit

/-! Source-only component, kernel-checked by the build: actual inner writes/rollback, later actual owner write,
then explicit outer commit/end. Supplied Source frames and marks do not establish admitted calls,
body dispatch, funded entry or source-to-intrinsic/bytecode adequacy.
Existing Source.evalE alone executes syntax. Operation lists certify the
resulting journal updates; they do not replace expression execution. -/
namespace Solidity.Lowering.V08.SourceTransientInnerRollbackOuterCommit
open Solidity Source
open SourceEmitControls
open SourceTransientBytesEmitControls (completed encoded eventSelector)
open SourceTransientReentry (nextOpening nextWritten)
open SourceTransientOwnerRollback (ownerFrame bothWritten checkpoint outerCheckpoint)
open SourceTransientOwnerCommit (clearSelf ownerObservation)

/-- Real self=false write occurs INSIDE the inner region, without an inner
commit. This is distinct from the prior inner-commit/outer-rollback client. -/
def innerCleared (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.transientUpdate (bothWritten pipeline bytes) self scratch (.bool false)
def innerRestored (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  {innerCleared pipeline bytes with
    ex:=(checkpoint pipeline bytes).rollback (innerCleared pipeline bytes).ex}
def laterWritten (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.transientUpdate (innerRestored pipeline bytes) sender scratch (.bool true)
def outerCommitted (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  {laterWritten pipeline bytes with
    ex:=(outerCheckpoint pipeline bytes).commit (laterWritten pipeline bytes).ex}
def ended (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.endExecution (outerCommitted pipeline bytes)

theorem inner_clear_assignment (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 4 clearSelf).run (locals,bothWritten pipeline bytes) =
      (.ok (.val (.bool false)),(locals,innerCleared pipeline bytes)) := rfl

/-- Certificates of the TWO actual resolved writes, paired with the existing
owner_assignment and inner_clear_assignment, not assumed handler execution. -/
theorem inner_generated_operations (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (innerCleared pipeline bytes).ex = (nextWritten pipeline bytes).ex.run
      [.transient sender (fun cells => cells.set scratch (some (.bool true))),
       .transient self (fun cells => cells.set scratch (some (.bool false)))] := rfl

theorem inner_restore_execution (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (checkpoint pipeline bytes).rollback (innerCleared pipeline bytes).ex =
      (nextWritten pipeline bytes).ex := by
  rw [inner_generated_operations]
  exact Source.rollback_run (nextWritten pipeline bytes).ex
    [.transient sender (fun cells => cells.set scratch (some (.bool true))),
     .transient self (fun cells => cells.set scratch (some (.bool false)))]
    sender self frame.value binary false

theorem inner_restore_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    innerRestored pipeline bytes = nextWritten pipeline bytes := by
  unfold innerRestored
  rw [inner_restore_execution]
  rfl

/-- This later sender write is REAL source execution at the restored machine;
it is not a transplanted equation from the original nextOpening snapshot. -/
theorem later_owner_assignment (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) ownerFrame 4 SourceTransientEmitControls.setScratch).run
      (locals,innerRestored pipeline bytes) =
      (.ok (.val (.bool true)),(locals,laterWritten pipeline bytes)) := by
  unfold laterWritten
  rw [inner_restore_machine]
  rfl

theorem later_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    laterWritten pipeline bytes = bothWritten pipeline bytes := by
  unfold laterWritten
  rw [inner_restore_machine]
  rfl

theorem outer_commit_execution (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (outerCheckpoint pipeline bytes).commit (laterWritten pipeline bytes).ex =
      (laterWritten pipeline bytes).ex :=
  Source.commit_keeps (outerCheckpoint pipeline bytes) (laterWritten pipeline bytes).ex

theorem outer_commit_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    outerCommitted pipeline bytes = laterWritten pipeline bytes := by
  unfold outerCommitted
  rw [outer_commit_execution]

theorem final_committed_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    outerCommitted pipeline bytes = bothWritten pipeline bytes := by
  rw [outer_commit_machine,later_machine]

/-- Full ordered transient/journal vector includes the inner rollback and
separate later write/commit. No intermediate success/error is suppressed. -/
theorem ordered_owner_history (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    [ownerObservation (nextOpening pipeline bytes),ownerObservation (nextWritten pipeline bytes),
     ownerObservation (bothWritten pipeline bytes),ownerObservation (innerCleared pipeline bytes),
     ownerObservation (innerRestored pipeline bytes),ownerObservation (laterWritten pipeline bytes),
     ownerObservation (outerCommitted pipeline bytes),ownerObservation (ended pipeline bytes)] =
    [(some (.bool false),some (.bool false),0),
     (some (.bool true),some (.bool false),1),
     (some (.bool true),some (.bool true),2),
     (some (.bool false),some (.bool true),3),
     (some (.bool true),some (.bool false),1),
     (some (.bool true),some (.bool true),2),
     (some (.bool true),some (.bool true),2),
     (some (.bool false),some (.bool false),0)] := by
  unfold ended
  rw [final_committed_machine,later_machine,inner_restore_machine]
  rfl

/-- Observation of existing typed state fields only, not a replacement state
layer. Whole world/heap equality preserves every unlisted field as well. -/
def retainedFields (state : Source.St E) (pipeline : Roadmap.Pipeline)
    (bytes : Roadmap.Bytes) : Prop :=
  state.ex.world = (completed pipeline bytes).ex.world ∧
  state.heap = (completed pipeline bytes).heap ∧
  state.events = populated.events ∧
  state.logs = (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
  state.fnLocals = populated.fnLocals

theorem all_retained (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    retainedFields (innerCleared pipeline bytes) pipeline bytes ∧
    retainedFields (innerRestored pipeline bytes) pipeline bytes ∧
    retainedFields (laterWritten pipeline bytes) pipeline bytes ∧
    retainedFields (outerCommitted pipeline bytes) pipeline bytes ∧
    retainedFields (ended pipeline bytes) pipeline bytes := by
  unfold ended
  rw [final_committed_machine,later_machine,inner_restore_machine]
  exact ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl⟩,
    ⟨rfl,rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl⟩⟩

theorem complete_populated_vector (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((outerCommitted pipeline bytes).ex.world.accounts sender).balance.val = 93 ∧
    ((outerCommitted pipeline bytes).ex.world.accounts self).balance.val = 7 ∧
    ((outerCommitted pipeline bytes).ex.world.accounts self).code = some 0 ∧
    ((outerCommitted pipeline bytes).ex.world.accounts self).nonce = 1 ∧
    ((outerCommitted pipeline bytes).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (outerCommitted pipeline bytes).ex.journal.length = 2 ∧
    ((outerCommitted pipeline bytes).ex.transient.cells self).read scratch = some (.bool true) ∧
    ((outerCommitted pipeline bytes).ex.transient.cells sender).read scratch = some (.bool true) ∧
    (outerCommitted pipeline bytes).heap.next = 2 ∧
    (outerCommitted pipeline bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (outerCommitted pipeline bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (outerCommitted pipeline bytes).events = populated.events ∧
    (outerCommitted pipeline bytes).logs = (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (outerCommitted pipeline bytes).fnLocals = populated.fnLocals := by
  rw [final_committed_machine]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem restored_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,innerRestored pipeline bytes) =
      (.ok (.val (.bool true)),(locals,nextWritten pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,innerRestored pipeline bytes) =
      (.ok (.val (.bool false)),(locals,nextWritten pipeline bytes)) := by
  rw [inner_restore_machine]
  exact ⟨rfl,rfl⟩

theorem end_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,ended pipeline bytes) =
      (.ok (.val (.bool false)),(locals,ended pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,ended pipeline bytes) =
      (.ok (.val (.bool false)),(locals,ended pipeline bytes)) := by
  unfold ended
  rw [final_committed_machine]
  exact ⟨rfl,rfl⟩

/-- Static later-write refusal leaves the earlier outer self write intact. -/
theorem static_later_refusal (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {ownerFrame with static:=true} 4
      SourceTransientEmitControls.setScratch).run (locals,innerRestored pipeline bytes) =
      (.error (.revert []),(locals,innerRestored pipeline bytes)) := by
  rw [inner_restore_machine]
  rfl

/-- A reached two-write prefix survives an inner clear's zero horizon. -/
theorem timeout_inner_prefix (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) ownerFrame 4 SourceTransientEmitControls.setScratch).run
      (locals,nextWritten pipeline bytes) =
      (.ok (.val (.bool true)),(locals,bothWritten pipeline bytes)) ∧
    (Source.evalE (global pipeline) frame 0 clearSelf).run (locals,bothWritten pipeline bytes) =
      (.error .timeout,(locals,bothWritten pipeline bytes)) :=
  ⟨SourceTransientOwnerRollback.owner_assignment pipeline bytes,rfl⟩

theorem timeout_before_later (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) ownerFrame 0 SourceTransientEmitControls.setScratch).run
      (locals,innerRestored pipeline bytes) =
      (.error .timeout,(locals,innerRestored pipeline bytes)) := rfl

theorem timeout_after_later (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) ownerFrame 0 SourceTransientEmitControls.setScratch).run
      (locals,laterWritten pipeline bytes) =
      (.error .timeout,(locals,laterWritten pipeline bytes)) := rfl

theorem wrong_outer_mark (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (outerCheckpoint pipeline bytes).rollback (innerCleared pipeline bytes).ex ≠
      (innerRestored pipeline bytes).ex := by
  rw [inner_restore_machine]
  intro same
  have lengths := congrArg (fun state => state.journal.length) same
  change 0 = 1 at lengths
  cases lengths

theorem wrong_auto_undo (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    outerCommitted pipeline bytes ≠ innerRestored pipeline bytes := by
  rw [final_committed_machine,inner_restore_machine]
  intro same
  have lengths := congrArg (fun state : Source.St E => state.ex.journal.length) same
  change 2 = 1 at lengths
  cases lengths

theorem forgetting_later_write (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    laterWritten pipeline bytes ≠ innerRestored pipeline bytes := by
  rw [later_machine,inner_restore_machine]
  intro same
  have lengths := congrArg (fun state : Source.St E => state.ex.journal.length) same
  change 2 = 1 at lengths
  cases lengths

/-- Terminal state alone cannot detect the forgotten transient write: explicit
end erases that difference, while the reached history above discriminates it. -/
theorem same_end_different_prefix (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    laterWritten pipeline bytes ≠ innerRestored pipeline bytes ∧
    SourceTransient.endExecution (laterWritten pipeline bytes) =
      SourceTransient.endExecution (innerRestored pipeline bytes) := by
  refine ⟨forgetting_later_write pipeline bytes, ?_⟩
  rw [later_machine,inner_restore_machine]
  rfl

/-- Consume the actual initial item execution, all real writes and exact
rollback/commit machine equations. Supplied frames are not admitted calls. -/
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
    (Source.evalE (global pipeline) frame 4 clearSelf).run (locals,bothWritten pipeline bytes) =
      (.ok (.val (.bool false)),(locals,innerCleared pipeline bytes)) ∧
    innerRestored pipeline bytes = nextWritten pipeline bytes ∧
    (Source.evalE (global pipeline) ownerFrame 4 SourceTransientEmitControls.setScratch).run
      (locals,innerRestored pipeline bytes) =
      (.ok (.val (.bool true)),(locals,laterWritten pipeline bytes)) ∧
    outerCommitted pipeline bytes = laterWritten pipeline bytes :=
  ⟨SourceTransientBytesEmitControls.sequence_complete pipeline bytes 0,
    SourceTransientReentry.reentry_assignment pipeline bytes,
    SourceTransientOwnerRollback.owner_assignment pipeline bytes,
    inner_clear_assignment pipeline bytes,inner_restore_machine pipeline bytes,
    later_owner_assignment pipeline bytes,outer_commit_machine pipeline bytes⟩

/-- These are concrete clients of the arbitrary-byte laws, not admission caps. -/
theorem payload_clients (pipeline : Roadmap.Pipeline) :
    ∀ bytes ∈ ([[],binary,SourceTransientBytesEmitControls.boundary33] : List Roadmap.Bytes),
      (SourceTransientBytesEmitControls.execution pipeline false bytes).run
        (Source.L0 E,SourceTransientEmitControls.opening) =
        (.ok (.normal locals),(Source.L0 E,completed pipeline bytes)) ∧
      (Source.evalE (global pipeline) ownerFrame 4 SourceTransientEmitControls.setScratch).run
        (locals,innerRestored pipeline bytes) =
        (.ok (.val (.bool true)),(locals,laterWritten pipeline bytes)) ∧
      outerCommitted pipeline bytes = bothWritten pipeline bytes := by
  intro bytes _
  exact ⟨SourceTransientBytesEmitControls.sequence_complete pipeline bytes 0,
    later_owner_assignment pipeline bytes,final_committed_machine pipeline bytes⟩

#print axioms inner_clear_assignment
#print axioms inner_generated_operations
#print axioms inner_restore_execution
#print axioms inner_restore_machine
#print axioms later_owner_assignment
#print axioms later_machine
#print axioms outer_commit_execution
#print axioms outer_commit_machine
#print axioms final_committed_machine
#print axioms ordered_owner_history
#print axioms all_retained
#print axioms complete_populated_vector
#print axioms restored_reads
#print axioms end_reads
#print axioms static_later_refusal
#print axioms timeout_inner_prefix
#print axioms timeout_before_later
#print axioms timeout_after_later
#print axioms wrong_outer_mark
#print axioms wrong_auto_undo
#print axioms forgetting_later_write
#print axioms same_end_different_prefix
#print axioms reached_client
#print axioms payload_clients
end Solidity.Lowering.V08.SourceTransientInnerRollbackOuterCommit
