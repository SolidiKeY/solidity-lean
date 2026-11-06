import Solidity.Lowering.V08.SourceTransientErrorCallerRollback

/-! Source-only component, kernel-checked by the build: actual successful nonzero Source transfer at a reached
transient state, distinct inner/outer rollback, and end WITHOUT payment rollback.
The Op witness below is
proved to be the ACTUAL transfer Option result, never an assumed paid state or
another interpreter. Supplied marks do not establish admitted payment dispatch,
external calls, SourceSpec, intrinsic frames or compiler/EVM adequacy. -/
namespace Solidity.Lowering.V08.SourceTransientReachedPayment
open Solidity Source
open SourceEmitControls
open SourceTransientBytesEmitControls (completed encoded eventSelector)
open SourceTransientReentry (nextOpening nextWritten)
open SourceTransientOwnerRollback (ownerFrame bothWritten outerCheckpoint)
open SourceTransientOwnerCommit (clearSelf)
open SourceTransientInnerRollbackOuterCommit (innerCleared innerRestored)
open SourceTransientErrorCallerRollback (rollbackCaller)

def amount : Roadmap.Word := ⟨5,by decide +kernel⟩
def senderAfter : Roadmap.Word := ⟨88,by decide +kernel⟩
def receiverAfter : Roadmap.Word := ⟨12,by decide +kernel⟩
/-- Concrete witness for the actual two journaled account updates. -/
def paid (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  {innerRestored pipeline bytes with ex:=
    (((innerRestored pipeline bytes).ex.apply
      (.account sender (fun account => account.withBalance senderAfter))).apply
      (.account self (fun account => account.withBalance receiverAfter)))}
/-- This mark is taken BEFORE transfer at the actual reached journal1 state. -/
def paymentCheckpoint (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.CallFrame :=
  (innerRestored pipeline bytes).ex.enter self sender amount binary false
def innerRolled (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  {paid pipeline bytes with ex:=
    (paymentCheckpoint pipeline bytes).rollback (paid pipeline bytes).ex}
def outerRolled (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  rollbackCaller (outerCheckpoint pipeline bytes) (innerRolled pipeline bytes)
def rollbackEnded (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.endExecution (outerRolled pipeline bytes)
/-- Alternative branch directly from paid, NOT sequentially after rollback. -/
def paidEnded (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.endExecution (paid pipeline bytes)

theorem amount_nonzero : amount.val = 5 ∧ amount.val ≠ 0 := by decide +kernel

/-- Derive successful Option output from the published transfer definition.
No transfer success or desired whole-handler equation is a premise. -/
theorem transfer_success (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (innerRestored pipeline bytes).ex.transfer sender self amount = some (paid pipeline bytes).ex := by
  unfold paid
  rw [SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  rfl

theorem payment_inner_execution (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (paymentCheckpoint pipeline bytes).rollback (paid pipeline bytes).ex =
      (innerRestored pipeline bytes).ex := by
  exact Source.rollback_transfer (innerRestored pipeline bytes).ex (paid pipeline bytes).ex
    (by decide +kernel : sender ≠ self) amount (transfer_success pipeline bytes)
    self sender binary false

theorem payment_inner_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    innerRolled pipeline bytes = innerRestored pipeline bytes := by
  unfold innerRolled
  rw [payment_inner_execution]
  rfl

theorem payment_outer_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    outerRolled pipeline bytes = nextOpening pipeline bytes := by
  unfold outerRolled
  rw [payment_inner_machine]
  exact SourceTransientErrorCallerRollback.caller_rollback_prefix pipeline bytes

theorem end_after_rollbacks (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    rollbackEnded pipeline bytes = nextOpening pipeline bytes := by
  unfold rollbackEnded
  rw [payment_outer_machine]
  rfl

/-- EXACT changed world, not an invalid claim that payment preserves balances.
Only the two existing typed accounts receive withBalance updates. -/
theorem paid_world_exact (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (paid pipeline bytes).ex.world =
      (((innerRestored pipeline bytes).ex.world.set sender
        (((innerRestored pipeline bytes).ex.world.accounts sender).withBalance senderAfter)).set self
        (((innerRestored pipeline bytes).ex.world.accounts self).withBalance receiverAfter)) := rfl

theorem other_account_preserved (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (address : Roadmap.Address) (notSender : address ≠ sender) (notSelf : address ≠ self) :
    ((paid pipeline bytes).ex.world.accounts address) =
      ((innerRestored pipeline bytes).ex.world.accounts address) := by
  rw [paid_world_exact]
  simp only [Source.World.set,notSender,notSelf,↓reduceDIte]

/-- Code, nonce and ENTIRE persistent storage of BOTH owners are unchanged.
This follows from actual withBalance operations, not generic frame assumptions. -/
theorem account_fields_preserved (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((paid pipeline bytes).ex.world.accounts sender).storage =
      ((innerRestored pipeline bytes).ex.world.accounts sender).storage ∧
    ((paid pipeline bytes).ex.world.accounts self).storage =
      ((innerRestored pipeline bytes).ex.world.accounts self).storage ∧
    ((paid pipeline bytes).ex.world.accounts sender).code =
      ((innerRestored pipeline bytes).ex.world.accounts sender).code ∧
    ((paid pipeline bytes).ex.world.accounts self).code =
      ((innerRestored pipeline bytes).ex.world.accounts self).code ∧
    ((paid pipeline bytes).ex.world.accounts sender).nonce =
      ((innerRestored pipeline bytes).ex.world.accounts sender).nonce ∧
    ((paid pipeline bytes).ex.world.accounts self).nonce =
      ((innerRestored pipeline bytes).ex.world.accounts self).nonce := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Explicit end preserves the PAID world, it does not undo a transfer. -/
theorem paid_end_world (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (paidEnded pipeline bytes).ex.world = (paid pipeline bytes).ex.world :=
  Source.endTx_world (paid pipeline bytes).ex

def paymentObservation (state : Source.St E) :=
  ((state.ex.world.accounts sender).balance.val,(state.ex.world.accounts self).balance.val,
   (state.ex.transient.cells self).read scratch,(state.ex.transient.cells sender).read scratch,
   state.ex.journal.length)

/-- Common prefix and the EXPLICIT rollback branch. Direct end is a separate
branch below, never mislabeled as a sequential step after rollback. -/
theorem rollback_branch_history (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    [paymentObservation (nextOpening pipeline bytes),paymentObservation (nextWritten pipeline bytes),
     paymentObservation (bothWritten pipeline bytes),paymentObservation (innerCleared pipeline bytes),
     paymentObservation (innerRestored pipeline bytes),paymentObservation (paid pipeline bytes),
     paymentObservation (innerRolled pipeline bytes),paymentObservation (outerRolled pipeline bytes),
     paymentObservation (rollbackEnded pipeline bytes)] =
    [(93,7,some (.bool false),some (.bool false),0),
     (93,7,some (.bool true),some (.bool false),1),
     (93,7,some (.bool true),some (.bool true),2),
     (93,7,some (.bool false),some (.bool true),3),
     (93,7,some (.bool true),some (.bool false),1),
     (88,12,some (.bool true),some (.bool false),3),
     (93,7,some (.bool true),some (.bool false),1),
     (93,7,some (.bool false),some (.bool false),0),
     (93,7,some (.bool false),some (.bool false),0)] := by
  rw [payment_inner_machine,payment_outer_machine,end_after_rollbacks,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  rfl

theorem direct_end_branch (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    [paymentObservation (paid pipeline bytes),paymentObservation (paidEnded pipeline bytes)] =
    [(88,12,some (.bool true),some (.bool false),3),
     (88,12,some (.bool false),some (.bool false),0)] := by
  unfold paidEnded paid
  rw [SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  rfl

/-- Observation of existing typed non-world fields only. World is separately
specified by paid_world_exact and whole rollback machine equalities. -/
def retainedMemory (state : Source.St E) (pipeline : Roadmap.Pipeline)
    (bytes : Roadmap.Bytes) : Prop :=
  state.heap = (completed pipeline bytes).heap ∧
  state.events = populated.events ∧
  state.logs = (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
  state.fnLocals = populated.fnLocals

theorem all_memory_retained (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    retainedMemory (paid pipeline bytes) pipeline bytes ∧
    retainedMemory (innerRolled pipeline bytes) pipeline bytes ∧
    retainedMemory (outerRolled pipeline bytes) pipeline bytes ∧
    retainedMemory (rollbackEnded pipeline bytes) pipeline bytes ∧
    retainedMemory (paidEnded pipeline bytes) pipeline bytes := by
  unfold paidEnded
  rw [payment_inner_machine,payment_outer_machine,end_after_rollbacks,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  exact ⟨⟨rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl⟩,
    ⟨rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl⟩⟩

theorem complete_populated_vector (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((paid pipeline bytes).ex.world.accounts sender).balance.val = 88 ∧
    ((paid pipeline bytes).ex.world.accounts self).balance.val = 12 ∧
    ((paid pipeline bytes).ex.world.accounts self).code = some 0 ∧
    ((paid pipeline bytes).ex.world.accounts self).nonce = 1 ∧
    ((paid pipeline bytes).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (paid pipeline bytes).ex.journal.length = 3 ∧
    ((paid pipeline bytes).ex.transient.cells self).read scratch = some (.bool true) ∧
    ((paid pipeline bytes).ex.transient.cells sender).read scratch = some (.bool false) ∧
    (paymentCheckpoint pipeline bytes).mark = 1 ∧
    (paid pipeline bytes).heap.next = 2 ∧
    (paid pipeline bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (paid pipeline bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (paid pipeline bytes).events = populated.events ∧
    (paid pipeline bytes).logs = (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (paid pipeline bytes).fnLocals = populated.fnLocals := by
  unfold paid paymentCheckpoint
  rw [SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Actual source reads at paid and post-end states, retaining exact machines. -/
theorem paid_and_end_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,paid pipeline bytes) =
      (.ok (.val (.bool true)),(locals,paid pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,paid pipeline bytes) =
      (.ok (.val (.bool false)),(locals,paid pipeline bytes)) ∧
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,paidEnded pipeline bytes) =
      (.ok (.val (.bool false)),(locals,paidEnded pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,paidEnded pipeline bytes) =
      (.ok (.val (.bool false)),(locals,paidEnded pipeline bytes)) := by
  unfold paidEnded paid
  rw [SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Halt alternatives are derived anew at the CHANGED paid input. Neither
source static refusal nor horizon timeout automatically refunds the payment. -/
theorem static_refusal_paid (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {ownerFrame with static:=true} 4
      SourceTransientEmitControls.setScratch).run (locals,paid pipeline bytes) =
      (.error (.revert []),(locals,paid pipeline bytes)) := rfl

theorem timeout_paid (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) ownerFrame 0 SourceTransientEmitControls.setScratch).run
      (locals,paid pipeline bytes) = (.error .timeout,(locals,paid pipeline bytes)) := rfl

theorem skipped_payment (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (innerRestored pipeline bytes).ex.transfer sender self amount ≠
      some (innerRestored pipeline bytes).ex := by
  rw [transfer_success]
  intro same
  have states := Option.some.inj same
  have balances := congrArg (fun state => (state.world.accounts sender).balance.val) states
  change 88 = 93 at balances
  cases balances

theorem wrong_outer_mark (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (outerCheckpoint pipeline bytes).rollback (paid pipeline bytes).ex ≠
      (innerRestored pipeline bytes).ex := by
  rw [SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  intro same
  have lengths := congrArg (fun state => state.journal.length) same
  change 0 = 1 at lengths
  cases lengths

theorem end_is_not_payment_rollback (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    paidEnded pipeline bytes ≠ innerRolled pipeline bytes ∧
    paidEnded pipeline bytes ≠ rollbackEnded pipeline bytes := by
  rw [payment_inner_machine,end_after_rollbacks]
  constructor
  · intro same
    have balances := congrArg (fun state : Source.St E =>
      (state.ex.world.accounts sender).balance.val) same
    change 88 = 93 at balances
    cases balances
  · intro same
    have balances := congrArg (fun state : Source.St E =>
      (state.ex.world.accounts sender).balance.val) same
    change 88 = 93 at balances
    cases balances

/-- Actual initial byte-event and resolved prefix execution, actual transfer
Option, and separately requested rollback/end routes. No handler is assumed. -/
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
    (innerRestored pipeline bytes).ex.transfer sender self amount = some (paid pipeline bytes).ex ∧
    innerRolled pipeline bytes = innerRestored pipeline bytes ∧
    outerRolled pipeline bytes = nextOpening pipeline bytes ∧
    (paidEnded pipeline bytes).ex.world = (paid pipeline bytes).ex.world :=
  ⟨SourceTransientBytesEmitControls.sequence_complete pipeline bytes 0,
    SourceTransientReentry.reentry_assignment pipeline bytes,
    SourceTransientOwnerRollback.owner_assignment pipeline bytes,
    SourceTransientInnerRollbackOuterCommit.inner_clear_assignment pipeline bytes,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine pipeline bytes,
    transfer_success pipeline bytes,payment_inner_machine pipeline bytes,
    payment_outer_machine pipeline bytes,paid_end_world pipeline bytes⟩

theorem payload_clients (pipeline : Roadmap.Pipeline) :
    ∀ bytes ∈ ([[],binary,SourceTransientBytesEmitControls.boundary33] : List Roadmap.Bytes),
      (innerRestored pipeline bytes).ex.transfer sender self amount = some (paid pipeline bytes).ex ∧
      innerRolled pipeline bytes = innerRestored pipeline bytes ∧
      outerRolled pipeline bytes = nextOpening pipeline bytes ∧
      (paidEnded pipeline bytes).ex.world = (paid pipeline bytes).ex.world := by
  intro bytes _
  exact ⟨transfer_success pipeline bytes,payment_inner_machine pipeline bytes,
    payment_outer_machine pipeline bytes,paid_end_world pipeline bytes⟩

#print axioms amount_nonzero
#print axioms transfer_success
#print axioms payment_inner_execution
#print axioms payment_inner_machine
#print axioms payment_outer_machine
#print axioms end_after_rollbacks
#print axioms paid_world_exact
#print axioms other_account_preserved
#print axioms account_fields_preserved
#print axioms paid_end_world
#print axioms rollback_branch_history
#print axioms direct_end_branch
#print axioms all_memory_retained
#print axioms complete_populated_vector
#print axioms paid_and_end_reads
#print axioms static_refusal_paid
#print axioms timeout_paid
#print axioms skipped_payment
#print axioms wrong_outer_mark
#print axioms end_is_not_payment_rollback
#print axioms reached_client
#print axioms payload_clients
end Solidity.Lowering.V08.SourceTransientReachedPayment
