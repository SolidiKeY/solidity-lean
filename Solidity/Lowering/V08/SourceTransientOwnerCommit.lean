import Solidity.Lowering.V08.SourceTransientOwnerRollback

/-! Source-only component, kernel-checked by the build: explicit inner commit, actual later source write, then
outer rollback. Supplied
Source frames/marks/end operations do not prove call or transaction admission,
body dispatch, intrinsic frame preservation or compiler/bytecode adequacy.
Only existing Source.evalE executes syntax; Op lists below certify its actual
generated journal operations rather than replacing expression execution. -/
namespace Solidity.Lowering.V08.SourceTransientOwnerCommit
open Solidity Source
open SourceEmitControls
open SourceTransientBytesEmitControls (completed encoded eventSelector)
open SourceTransientReentry (nextOpening nextWritten)
open SourceTransientOwnerRollback (ownerFrame bothWritten checkpoint outerCheckpoint)

/-- Apply the ACTUAL published commit at the reached inner boundary. -/
def committed (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  {bothWritten pipeline bytes with
    ex:=(checkpoint pipeline bytes).commit (bothWritten pipeline bytes).ex}
def clearSelf : RExpr E [.bool] .bool :=
  .assign (.state scratchDecl rfl rfl) (.bool false)
def afterClear (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.transientUpdate (committed pipeline bytes) self scratch (.bool false)
def outerRolled (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  {afterClear pipeline bytes with
    ex:=(outerCheckpoint pipeline bytes).rollback (afterClear pipeline bytes).ex}

theorem commit_execution (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (checkpoint pipeline bytes).commit (bothWritten pipeline bytes).ex =
      (bothWritten pipeline bytes).ex :=
  Source.commit_keeps (checkpoint pipeline bytes) (bothWritten pipeline bytes).ex

theorem commit_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    committed pipeline bytes = bothWritten pipeline bytes := by
  unfold committed
  rw [commit_execution]

/-- The later false value is derived from actual resolved assignment, not an
assumed post-handler equation or a substituted operation-list interpreter. -/
theorem clear_assignment (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 4 clearSelf).run (locals,committed pipeline bytes) =
      (.ok (.val (.bool false)),(locals,afterClear pipeline bytes)) := rfl

theorem post_clear_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,afterClear pipeline bytes) =
      (.ok (.val (.bool false)),(locals,afterClear pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,afterClear pipeline bytes) =
      (.ok (.val (.bool true)),(locals,afterClear pipeline bytes)) := ⟨rfl,rfl⟩

/-- The actual reached later write generates exactly this published operation.
This equality is paired with clear_assignment, never used as a source evaluator. -/
theorem generated_later_operation (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (afterClear pipeline bytes).ex =
      ((checkpoint pipeline bytes).commit (bothWritten pipeline bytes).ex).run
        [.transient self (fun cells => cells.set scratch (some (.bool false)))] := rfl

/-- Published outer-after-commit uses identical frame parameters for its marks.
Our marks have distinct owners; commit ignores context by its checked law.
This fact says NOTHING about a context-changing call's admission/execution. -/
theorem commit_context_equivalence (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (checkpoint pipeline bytes).commit (bothWritten pipeline bytes).ex =
      ((nextWritten pipeline bytes).ex.enter self sender frame.value binary false).commit
        (bothWritten pipeline bytes).ex := by
  rw [Source.commit_keeps,Source.commit_keeps]

theorem outer_restore_execution (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (outerCheckpoint pipeline bytes).rollback (afterClear pipeline bytes).ex =
      (nextOpening pipeline bytes).ex := by
  rw [generated_later_operation,commit_context_equivalence]
  exact Source.rollback_outer_after_commit (nextOpening pipeline bytes).ex
    [.transient self (fun cells => cells.set scratch (some (.bool true)))]
    [.transient sender (fun cells => cells.set scratch (some (.bool true)))]
    [.transient self (fun cells => cells.set scratch (some (.bool false)))]
    self sender frame.value binary false

theorem outer_restore_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    outerRolled pipeline bytes = nextOpening pipeline bytes := by
  unfold outerRolled
  rw [outer_restore_execution]
  rfl

/-- Pure observation of the EXISTING typed source state, not a new state layer. -/
def ownerObservation (state : Source.St E) :=
  ((state.ex.transient.cells self).read scratch,
   (state.ex.transient.cells sender).read scratch,state.ex.journal.length)

/-- Complete ordered transient/journal history, including the unchanged commit
boundary and the distinct actual later false write. -/
theorem ordered_owner_history (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    [ownerObservation (nextOpening pipeline bytes),ownerObservation (nextWritten pipeline bytes),
     ownerObservation (bothWritten pipeline bytes),ownerObservation (committed pipeline bytes),
     ownerObservation (afterClear pipeline bytes),ownerObservation (outerRolled pipeline bytes)] =
    [(some (.bool false),some (.bool false),0),
     (some (.bool true),some (.bool false),1),
     (some (.bool true),some (.bool true),2),
     (some (.bool true),some (.bool true),2),
     (some (.bool false),some (.bool true),3),
     (some (.bool false),some (.bool false),0)] := by
  rw [outer_restore_machine]
  rfl

/-- ENTIRE world and heap preservation for real transient-only execution. Exact
selector, arbitrary ABI bytes and complete ordered old log tail remain intact. -/
theorem retained_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (committed pipeline bytes).ex.world = (completed pipeline bytes).ex.world ∧
    (afterClear pipeline bytes).ex.world = (completed pipeline bytes).ex.world ∧
    (outerRolled pipeline bytes).ex.world = (completed pipeline bytes).ex.world ∧
    (committed pipeline bytes).heap = (completed pipeline bytes).heap ∧
    (afterClear pipeline bytes).heap = (completed pipeline bytes).heap ∧
    (outerRolled pipeline bytes).heap = (completed pipeline bytes).heap ∧
    (committed pipeline bytes).events = populated.events ∧
    (afterClear pipeline bytes).events = populated.events ∧
    (outerRolled pipeline bytes).events = populated.events ∧
    (committed pipeline bytes).logs =
      (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (afterClear pipeline bytes).logs =
      (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (outerRolled pipeline bytes).logs =
      (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (committed pipeline bytes).fnLocals = populated.fnLocals ∧
    (afterClear pipeline bytes).fnLocals = populated.fnLocals ∧
    (outerRolled pipeline bytes).fnLocals = populated.fnLocals := by
  rw [outer_restore_machine]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem complete_populated_vector (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((afterClear pipeline bytes).ex.world.accounts sender).balance = 93 ∧
    ((afterClear pipeline bytes).ex.world.accounts self).balance = 7 ∧
    ((afterClear pipeline bytes).ex.world.accounts self).code = some 0 ∧
    ((afterClear pipeline bytes).ex.world.accounts self).nonce = 1 ∧
    ((afterClear pipeline bytes).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (afterClear pipeline bytes).heap.next = 2 ∧
    (afterClear pipeline bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (afterClear pipeline bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (afterClear pipeline bytes).events = populated.events ∧
    (afterClear pipeline bytes).logs = (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (afterClear pipeline bytes).fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Explicit outer rollback supplies these actual reads; no raw halt does so. -/
theorem rollback_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,outerRolled pipeline bytes) =
      (.ok (.val (.bool false)),(locals,nextOpening pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,outerRolled pipeline bytes) =
      (.ok (.val (.bool false)),(locals,nextOpening pipeline bytes)) := by
  rw [outer_restore_machine]
  exact ⟨rfl,rfl⟩

theorem explicit_end_after_rollback (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    SourceTransient.endExecution (outerRolled pipeline bytes) = nextOpening pipeline bytes := by
  rw [outer_restore_machine]
  rfl

theorem static_clear_refusal (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {frame with static:=true} 4 clearSelf).run
      (locals,committed pipeline bytes) =
      (.error (.revert []),(locals,committed pipeline bytes)) := rfl

theorem timeout_before_clear (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 0 clearSelf).run (locals,committed pipeline bytes) =
      (.error .timeout,(locals,committed pipeline bytes)) := rfl

theorem timeout_after_clear (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 0 clearSelf).run (locals,afterClear pipeline bytes) =
      (.error .timeout,(locals,afterClear pipeline bytes)) := rfl

/-- Committing does not undo the sender's reached write. -/
theorem wrong_auto_undo (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    committed pipeline bytes ≠ SourceTransientOwnerRollback.restored pipeline bytes := by
  rw [commit_machine,SourceTransientOwnerRollback.checkpoint_restore_machine]
  intro same
  have lengths := congrArg (fun state : Source.St E => state.ex.journal.length) same
  change 2 = 1 at lengths
  cases lengths

/-- The inner mark leaves self's earlier write; only the OUTER mark restores0. -/
theorem wrong_inner_mark (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (checkpoint pipeline bytes).rollback (afterClear pipeline bytes).ex ≠
      (nextOpening pipeline bytes).ex := by
  intro same
  have lengths := congrArg (fun state => state.journal.length) same
  change 1 = 0 at lengths
  cases lengths

theorem forgetting_later_write (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    afterClear pipeline bytes ≠ committed pipeline bytes := by
  intro same
  have lengths := congrArg (fun state : Source.St E => state.ex.journal.length) same
  change 3 = 2 at lengths
  cases lengths

/-- Actual prior item execution, both owner assignments, real commit, and the
later resolved false write, retaining full results/locals/reached states. -/
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
    committed pipeline bytes = bothWritten pipeline bytes ∧
    (Source.evalE (global pipeline) frame 4 clearSelf).run (locals,committed pipeline bytes) =
      (.ok (.val (.bool false)),(locals,afterClear pipeline bytes)) ∧
    outerRolled pipeline bytes = nextOpening pipeline bytes :=
  ⟨SourceTransientBytesEmitControls.sequence_complete pipeline bytes 0,
    SourceTransientReentry.reentry_assignment pipeline bytes,
    SourceTransientOwnerRollback.owner_assignment pipeline bytes,
    commit_machine pipeline bytes,clear_assignment pipeline bytes,outer_restore_machine pipeline bytes⟩

/-- Concrete empty/binary/33-byte clients, not an admitted payload-length bound. -/
theorem payload_clients (pipeline : Roadmap.Pipeline) :
    ∀ bytes ∈ ([[],binary,SourceTransientBytesEmitControls.boundary33] : List Roadmap.Bytes),
      (SourceTransientBytesEmitControls.execution pipeline false bytes).run
        (Source.L0 E,SourceTransientEmitControls.opening) =
        (.ok (.normal locals),(Source.L0 E,completed pipeline bytes)) ∧
      (Source.evalE (global pipeline) frame 4 clearSelf).run (locals,committed pipeline bytes) =
        (.ok (.val (.bool false)),(locals,afterClear pipeline bytes)) ∧
      outerRolled pipeline bytes = nextOpening pipeline bytes := by
  intro bytes _
  exact ⟨SourceTransientBytesEmitControls.sequence_complete pipeline bytes 0,
    clear_assignment pipeline bytes,outer_restore_machine pipeline bytes⟩

#print axioms commit_execution
#print axioms commit_machine
#print axioms clear_assignment
#print axioms post_clear_reads
#print axioms generated_later_operation
#print axioms commit_context_equivalence
#print axioms outer_restore_execution
#print axioms outer_restore_machine
#print axioms ordered_owner_history
#print axioms retained_machine
#print axioms complete_populated_vector
#print axioms rollback_reads
#print axioms explicit_end_after_rollback
#print axioms static_clear_refusal
#print axioms timeout_before_clear
#print axioms timeout_after_clear
#print axioms wrong_auto_undo
#print axioms wrong_inner_mark
#print axioms forgetting_later_write
#print axioms reached_client
#print axioms payload_clients
end Solidity.Lowering.V08.SourceTransientOwnerCommit
