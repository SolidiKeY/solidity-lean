import Solidity.Lowering.V08.SourceTransientInnerRollbackOuterCommit

/-! Source-only component, kernel-checked by the build: actual static-revert/timeout observations, EXPLICIT
caller rollback, then published end/reset and fresh entry marks/reads.
No automatic unwinding,
try/catch rule, admitted call/transaction or compiler/intrinsic-frame adequacy
is inferred from a Source error. Existing typed Source operations only. -/
namespace Solidity.Lowering.V08.SourceTransientErrorCallerRollback
open Solidity Source
open SourceEmitControls
open SourceTransientBytesEmitControls (completed encoded eventSelector)
open SourceTransientReentry (nextOpening nextWritten)
open SourceTransientOwnerRollback (ownerFrame bothWritten checkpoint outerCheckpoint)
open SourceTransientOwnerCommit (ownerObservation clearSelf)
open SourceTransientInnerRollbackOuterCommit (innerCleared innerRestored retainedFields)

/-- Observe the actual failed evaluator runs, including their returned machine. -/
def staticResult (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :=
  (Source.evalE (global pipeline) {ownerFrame with static:=true} 4
    SourceTransientEmitControls.setScratch).run (locals,innerRestored pipeline bytes)
def timeoutResult (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :=
  (Source.evalE (global pipeline) ownerFrame 0
    SourceTransientEmitControls.setScratch).run (locals,innerRestored pipeline bytes)

/-- Record-only lift of the published journal rollback to existing Source.St.
This does not evaluate syntax or decide whether a caller catches any halt. -/
def rollbackCaller (mark : Source.CallFrame) (state : Source.St E) : Source.St E :=
  {state with ex:=mark.rollback state.ex}
def staticRolled (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  rollbackCaller (outerCheckpoint pipeline bytes) (staticResult pipeline bytes).2.2
def timeoutRolled (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  rollbackCaller (outerCheckpoint pipeline bytes) (timeoutResult pipeline bytes).2.2
def staticFresh (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.endExecution (staticRolled pipeline bytes)
def timeoutFresh (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.endExecution (timeoutRolled pipeline bytes)
/-- The public interface supplies endTx and enter, not a stateful beginTx.
Entering only constructs a frame/mark; actual new-transaction admission is open. -/
def staticFreshFrame (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.CallFrame :=
  (staticFresh pipeline bytes).ex.enter self sender frame.value binary false
def timeoutFreshFrame (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.CallFrame :=
  (timeoutFresh pipeline bytes).ex.enter self sender frame.value binary false

theorem static_execution (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    staticResult pipeline bytes =
      (.error (.revert []),(locals,innerRestored pipeline bytes)) :=
  SourceTransientInnerRollbackOuterCommit.static_later_refusal pipeline bytes

theorem timeout_execution (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    timeoutResult pipeline bytes =
      (.error .timeout,(locals,innerRestored pipeline bytes)) :=
  SourceTransientInnerRollbackOuterCommit.timeout_before_later pipeline bytes

/-- The inherited self write remains until caller rollback is EXPLICITLY applied. -/
theorem caller_rollback_prefix (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    rollbackCaller (outerCheckpoint pipeline bytes) (innerRestored pipeline bytes) =
      nextOpening pipeline bytes := by
  rw [SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  have restoredExecution :
      (outerCheckpoint pipeline bytes).rollback (nextWritten pipeline bytes).ex =
        (nextOpening pipeline bytes).ex := by
    exact Source.rollback_run (nextOpening pipeline bytes).ex
      [.transient self (fun cells => cells.set scratch (some (.bool true)))]
      self sender frame.value binary false
  unfold rollbackCaller
  rw [restoredExecution]
  rfl

theorem static_caller_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    staticRolled pipeline bytes = nextOpening pipeline bytes := by
  unfold staticRolled
  rw [static_execution]
  exact caller_rollback_prefix pipeline bytes

theorem timeout_caller_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    timeoutRolled pipeline bytes = nextOpening pipeline bytes := by
  unfold timeoutRolled
  rw [timeout_execution]
  exact caller_rollback_prefix pipeline bytes

theorem static_fresh_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    staticFresh pipeline bytes = nextOpening pipeline bytes := by
  unfold staticFresh
  rw [static_caller_machine]
  rfl

theorem timeout_fresh_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    timeoutFresh pipeline bytes = nextOpening pipeline bytes := by
  unfold timeoutFresh
  rw [timeout_caller_machine]
  rfl

/-- Exact halts and caller locals survive the observation extension. Revert[]
and timeout are NOT identified or classified as Solidity catchability. -/
theorem caller_observations (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((staticResult pipeline bytes).1,(staticResult pipeline bytes).2.1,staticRolled pipeline bytes) =
      (.error (.revert []),locals,nextOpening pipeline bytes) ∧
    ((timeoutResult pipeline bytes).1,(timeoutResult pipeline bytes).2.1,timeoutRolled pipeline bytes) =
      (.error .timeout,locals,nextOpening pipeline bytes) := by
  rw [static_execution,timeout_execution,static_caller_machine,timeout_caller_machine]
  exact ⟨rfl,rfl⟩

theorem distinct_error_statuses (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (staticResult pipeline bytes).1 ≠ (timeoutResult pipeline bytes).1 := by
  rw [static_execution,timeout_execution]
  intro same
  cases same

/-- Identical owner histories do NOT erase the distinct error results above. -/
theorem static_owner_history (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    [ownerObservation (nextOpening pipeline bytes),ownerObservation (nextWritten pipeline bytes),
     ownerObservation (bothWritten pipeline bytes),ownerObservation (innerCleared pipeline bytes),
     ownerObservation (innerRestored pipeline bytes),ownerObservation (staticResult pipeline bytes).2.2,
     ownerObservation (staticRolled pipeline bytes),ownerObservation (staticFresh pipeline bytes)] =
    [(some (.bool false),some (.bool false),0),
     (some (.bool true),some (.bool false),1),
     (some (.bool true),some (.bool true),2),
     (some (.bool false),some (.bool true),3),
     (some (.bool true),some (.bool false),1),
     (some (.bool true),some (.bool false),1),
     (some (.bool false),some (.bool false),0),
     (some (.bool false),some (.bool false),0)] := by
  rw [static_execution,static_caller_machine,static_fresh_machine,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  rfl

theorem timeout_owner_history (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    [ownerObservation (nextOpening pipeline bytes),ownerObservation (nextWritten pipeline bytes),
     ownerObservation (bothWritten pipeline bytes),ownerObservation (innerCleared pipeline bytes),
     ownerObservation (innerRestored pipeline bytes),ownerObservation (timeoutResult pipeline bytes).2.2,
     ownerObservation (timeoutRolled pipeline bytes),ownerObservation (timeoutFresh pipeline bytes)] =
    [(some (.bool false),some (.bool false),0),
     (some (.bool true),some (.bool false),1),
     (some (.bool true),some (.bool true),2),
     (some (.bool false),some (.bool true),3),
     (some (.bool true),some (.bool false),1),
     (some (.bool true),some (.bool false),1),
     (some (.bool false),some (.bool false),0),
     (some (.bool false),some (.bool false),0)] := by
  rw [timeout_execution,timeout_caller_machine,timeout_fresh_machine,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  rfl

/-- Entire world/heap and complete event bytes/log tail are retained at both
raw-error, caller-rollback and fresh boundaries; no source effect is projected out. -/
theorem all_retained (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    retainedFields (staticResult pipeline bytes).2.2 pipeline bytes ∧
    retainedFields (timeoutResult pipeline bytes).2.2 pipeline bytes ∧
    retainedFields (staticRolled pipeline bytes) pipeline bytes ∧
    retainedFields (timeoutRolled pipeline bytes) pipeline bytes ∧
    retainedFields (staticFresh pipeline bytes) pipeline bytes ∧
    retainedFields (timeoutFresh pipeline bytes) pipeline bytes := by
  rw [static_execution,timeout_execution,static_caller_machine,timeout_caller_machine,
    static_fresh_machine,timeout_fresh_machine,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  exact ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl⟩,
    ⟨rfl,rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl⟩⟩

theorem complete_populated_vector (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    staticFresh pipeline bytes = timeoutFresh pipeline bytes ∧
    ((staticFresh pipeline bytes).ex.world.accounts sender).balance = 93 ∧
    ((staticFresh pipeline bytes).ex.world.accounts self).balance = 7 ∧
    ((staticFresh pipeline bytes).ex.world.accounts self).code = some 0 ∧
    ((staticFresh pipeline bytes).ex.world.accounts self).nonce = 1 ∧
    ((staticFresh pipeline bytes).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    ((staticFresh pipeline bytes).ex.transient.cells self).read scratch = some (.bool false) ∧
    ((staticFresh pipeline bytes).ex.transient.cells sender).read scratch = some (.bool false) ∧
    (staticFresh pipeline bytes).ex.journal.length = 0 ∧
    (staticFresh pipeline bytes).heap.next = 2 ∧
    (staticFresh pipeline bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (staticFresh pipeline bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (staticFresh pipeline bytes).events = populated.events ∧
    (staticFresh pipeline bytes).logs = (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (staticFresh pipeline bytes).fnLocals = populated.fnLocals := by
  rw [static_fresh_machine,timeout_fresh_machine]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Actual source reads at raw-error input retain the self prefix. -/
theorem raw_error_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (staticResult pipeline bytes).2 =
      (.ok (.val (.bool true)),(locals,innerRestored pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (timeoutResult pipeline bytes).2 =
      (.ok (.val (.bool false)),(locals,innerRestored pipeline bytes)) := by
  rw [static_execution,timeout_execution,SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  exact ⟨rfl,rfl⟩

theorem fresh_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,staticFresh pipeline bytes) =
      (.ok (.val (.bool false)),(locals,staticFresh pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,staticFresh pipeline bytes) =
      (.ok (.val (.bool false)),(locals,staticFresh pipeline bytes)) ∧
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,timeoutFresh pipeline bytes) =
      (.ok (.val (.bool false)),(locals,timeoutFresh pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,timeoutFresh pipeline bytes) =
      (.ok (.val (.bool false)),(locals,timeoutFresh pipeline bytes)) := by
  rw [static_fresh_machine,timeout_fresh_machine]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem fresh_entry_marks (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (staticFreshFrame pipeline bytes).mark = 0 ∧
    (timeoutFreshFrame pipeline bytes).mark = 0 := by
  unfold staticFreshFrame timeoutFreshFrame
  rw [static_fresh_machine,timeout_fresh_machine]
  exact ⟨rfl,rfl⟩

theorem omitted_caller_rollback (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (staticResult pipeline bytes).2.2 ≠ staticRolled pipeline bytes ∧
    (timeoutResult pipeline bytes).2.2 ≠ timeoutRolled pipeline bytes := by
  rw [static_execution,timeout_execution,static_caller_machine,timeout_caller_machine,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  constructor
  · intro same
    have lengths := congrArg (fun state : Source.St E => state.ex.journal.length) same
    change 1 = 0 at lengths
    cases lengths
  · intro same
    have lengths := congrArg (fun state : Source.St E => state.ex.journal.length) same
    change 1 = 0 at lengths
    cases lengths

theorem wrong_inner_mark (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (checkpoint pipeline bytes).rollback (staticResult pipeline bytes).2.2.ex ≠
      (staticRolled pipeline bytes).ex := by
  rw [static_execution,static_caller_machine,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  intro same
  have lengths := congrArg (fun state => state.journal.length) same
  change 1 = 0 at lengths
  cases lengths

/-- Skipping the real self effect is wrong at the error boundary, even though
end alone normalizes to the same final machine. Exact errors remain distinct. -/
theorem skipped_effect_hidden_by_end (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (staticResult pipeline bytes).2.2 ≠ nextOpening pipeline bytes ∧
    SourceTransient.endExecution (staticResult pipeline bytes).2.2 = staticFresh pipeline bytes ∧
    (timeoutResult pipeline bytes).2.2 ≠ nextOpening pipeline bytes ∧
    SourceTransient.endExecution (timeoutResult pipeline bytes).2.2 = timeoutFresh pipeline bytes := by
  rw [static_execution,timeout_execution,static_fresh_machine,timeout_fresh_machine,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  have different : nextWritten pipeline bytes ≠ nextOpening pipeline bytes := by
    intro same
    have lengths := congrArg (fun state : Source.St E => state.ex.journal.length) same
    change 1 = 0 at lengths
    cases lengths
  exact ⟨different,rfl,different,rfl⟩

/-- Actual reached prefix and both alternative evaluator error routes, each
followed by explicit caller rollback/end. No whole-handler result is assumed. -/
theorem reached_clients (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
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
    staticResult pipeline bytes = (.error (.revert []),(locals,innerRestored pipeline bytes)) ∧
    timeoutResult pipeline bytes = (.error .timeout,(locals,innerRestored pipeline bytes)) ∧
    staticRolled pipeline bytes = nextOpening pipeline bytes ∧
    timeoutRolled pipeline bytes = nextOpening pipeline bytes ∧
    staticFresh pipeline bytes = nextOpening pipeline bytes ∧
    timeoutFresh pipeline bytes = nextOpening pipeline bytes :=
  ⟨SourceTransientBytesEmitControls.sequence_complete pipeline bytes 0,
    SourceTransientReentry.reentry_assignment pipeline bytes,
    SourceTransientOwnerRollback.owner_assignment pipeline bytes,
    SourceTransientInnerRollbackOuterCommit.inner_clear_assignment pipeline bytes,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine pipeline bytes,
    static_execution pipeline bytes,timeout_execution pipeline bytes,
    static_caller_machine pipeline bytes,timeout_caller_machine pipeline bytes,
    static_fresh_machine pipeline bytes,timeout_fresh_machine pipeline bytes⟩

/-- Empty/binary/33-byte clients instantiate arbitrary-byte laws, not a profile. -/
theorem payload_clients (pipeline : Roadmap.Pipeline) :
    ∀ bytes ∈ ([[],binary,SourceTransientBytesEmitControls.boundary33] : List Roadmap.Bytes),
      staticResult pipeline bytes = (.error (.revert []),(locals,innerRestored pipeline bytes)) ∧
      timeoutResult pipeline bytes = (.error .timeout,(locals,innerRestored pipeline bytes)) ∧
      staticFresh pipeline bytes = nextOpening pipeline bytes ∧
      timeoutFresh pipeline bytes = nextOpening pipeline bytes := by
  intro bytes _
  exact ⟨static_execution pipeline bytes,timeout_execution pipeline bytes,
    static_fresh_machine pipeline bytes,timeout_fresh_machine pipeline bytes⟩

#print axioms static_execution
#print axioms timeout_execution
#print axioms caller_rollback_prefix
#print axioms static_caller_machine
#print axioms timeout_caller_machine
#print axioms static_fresh_machine
#print axioms timeout_fresh_machine
#print axioms caller_observations
#print axioms distinct_error_statuses
#print axioms static_owner_history
#print axioms timeout_owner_history
#print axioms all_retained
#print axioms complete_populated_vector
#print axioms raw_error_reads
#print axioms fresh_reads
#print axioms fresh_entry_marks
#print axioms omitted_caller_rollback
#print axioms wrong_inner_mark
#print axioms skipped_effect_hidden_by_end
#print axioms reached_clients
#print axioms payload_clients
end Solidity.Lowering.V08.SourceTransientErrorCallerRollback
