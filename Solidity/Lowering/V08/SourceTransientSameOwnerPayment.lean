import Solidity.Lowering.V08.SourceTransientRejectedPayment

/-! Source-only component, kernel-checked by the build: same-owner transfer affordability/identity at actual
paid88/12, contrasted with distinct-owner full-balance transfer. Option.none supplies NO state or Source
halt/refund. Record maps below observe actual Some results without inventing
call/transaction semantics. No admitted dispatch/intrinsic/bytecode adequacy. -/
namespace Solidity.Lowering.V08.SourceTransientSameOwnerPayment
open Solidity Source
open SourceEmitControls
open SourceTransientBytesEmitControls (completed encoded eventSelector)
open SourceTransientReentry (nextOpening)
open SourceTransientOwnerRollback (ownerFrame outerCheckpoint)
open SourceTransientInnerRollbackOuterCommit (innerRestored)
open SourceTransientErrorCallerRollback (rollbackCaller)
open SourceTransientReachedPayment (paid innerRolled outerRolled paidEnded retainedMemory paymentObservation)
open SourceTransientRejectedPayment (amount89)

def amount88 : Roadmap.Word := ⟨88,by decide +kernel⟩
def zeroWord : Roadmap.Word := ⟨0,by decide +kernel⟩
def hundred : Roadmap.Word := ⟨100,by decide +kernel⟩
def same88 (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :=
  (paid pipeline bytes).ex.transfer sender sender amount88
def same89 (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :=
  (paid pipeline bytes).ex.transfer sender sender amount89
/-- Actual two-account-update witness ONLY for the distinct-owner branch. -/
def drained (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  {paid pipeline bytes with ex:=
    (((paid pipeline bytes).ex.apply (.account sender (fun a => a.withBalance zeroWord))).apply
      (.account self (fun a => a.withBalance hundred)))}
def drainCheckpoint (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.CallFrame :=
  (paid pipeline bytes).ex.enter self sender amount88 binary false
def drainRolled (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  {drained pipeline bytes with ex:=
    (drainCheckpoint pipeline bytes).rollback (drained pipeline bytes).ex}
def drainedEnd (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.endExecution (drained pipeline bytes)
def bothPaymentsRolled (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  rollbackCaller (SourceTransientReachedPayment.paymentCheckpoint pipeline bytes)
    (drainRolled pipeline bytes)

/-- Equal owners STILL require affordability; successful transfer is exactly
identity of the ENTIRE execution state, not merely a balance projection. -/
theorem same88_identity (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    same88 pipeline bytes = some (paid pipeline bytes).ex := rfl

theorem same89_rejected (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    same89 pipeline bytes = none := rfl

/-- Explicit record-only observation of the actual Some execution state. -/
theorem same88_full_state (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (same88 pipeline bytes).map (fun ex => {paid pipeline bytes with ex:=ex}) =
      some (paid pipeline bytes) := by
  rw [same88_identity]
  rfl

theorem same89_no_state (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (same89 pipeline bytes).map (fun ex => {paid pipeline bytes with ex:=ex}) = none := by
  rw [same89_rejected]
  rfl

theorem distinct88_success (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (paid pipeline bytes).ex.transfer sender self amount88 = some (drained pipeline bytes).ex := by
  unfold drained
  rfl

theorem distinct88_full_state (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((paid pipeline bytes).ex.transfer sender self amount88).map
      (fun ex => {paid pipeline bytes with ex:=ex}) = some (drained pipeline bytes) := by
  rw [distinct88_success]
  rfl

/-- These are three alternative attempts from the SAME existing paid input,
not a trace claiming a state is obtained from rejected Option.none. -/
theorem case_results (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (same88 pipeline bytes,same89 pipeline bytes,(paid pipeline bytes).ex.transfer sender self amount88) =
      (some (paid pipeline bytes).ex,none,some (drained pipeline bytes).ex) := by
  rw [same88_identity,same89_rejected,distinct88_success]

theorem drain_rollback_execution (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (drainCheckpoint pipeline bytes).rollback (drained pipeline bytes).ex =
      (paid pipeline bytes).ex := by
  exact Source.rollback_transfer (paid pipeline bytes).ex (drained pipeline bytes).ex
    (by decide +kernel : sender ≠ self) amount88 (distinct88_success pipeline bytes)
    self sender binary false

theorem drain_rollback_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    drainRolled pipeline bytes = paid pipeline bytes := by
  unfold drainRolled
  rw [drain_rollback_execution]
  rfl

theorem both_payments_rollback_machine (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    bothPaymentsRolled pipeline bytes = innerRestored pipeline bytes := by
  unfold bothPaymentsRolled
  rw [drain_rollback_machine]
  exact SourceTransientReachedPayment.payment_inner_machine pipeline bytes

theorem outer_after_both_payments (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    rollbackCaller (outerCheckpoint pipeline bytes) (bothPaymentsRolled pipeline bytes) =
      nextOpening pipeline bytes := by
  rw [both_payments_rollback_machine]
  exact SourceTransientErrorCallerRollback.caller_rollback_prefix pipeline bytes

theorem end_after_all_rollbacks (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    SourceTransient.endExecution
      (rollbackCaller (outerCheckpoint pipeline bytes) (bothPaymentsRolled pipeline bytes)) =
      nextOpening pipeline bytes := by
  rw [outer_after_both_payments]
  rfl

theorem drained_world_exact (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (drained pipeline bytes).ex.world =
      (((paid pipeline bytes).ex.world.set sender
        (((paid pipeline bytes).ex.world.accounts sender).withBalance zeroWord)).set self
        (((paid pipeline bytes).ex.world.accounts self).withBalance hundred)) := rfl

theorem other_account_preserved (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (address : Roadmap.Address) (notSender : address ≠ sender) (notSelf : address ≠ self) :
    ((drained pipeline bytes).ex.world.accounts address) =
      ((paid pipeline bytes).ex.world.accounts address) := by
  rw [drained_world_exact]
  simp only [Source.World.set,notSender,notSelf,↓reduceDIte]

theorem account_fields_preserved (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((drained pipeline bytes).ex.world.accounts sender).storage =
      ((paid pipeline bytes).ex.world.accounts sender).storage ∧
    ((drained pipeline bytes).ex.world.accounts self).storage =
      ((paid pipeline bytes).ex.world.accounts self).storage ∧
    ((drained pipeline bytes).ex.world.accounts sender).code =
      ((paid pipeline bytes).ex.world.accounts sender).code ∧
    ((drained pipeline bytes).ex.world.accounts self).code =
      ((paid pipeline bytes).ex.world.accounts self).code ∧
    ((drained pipeline bytes).ex.world.accounts sender).nonce =
      ((paid pipeline bytes).ex.world.accounts sender).nonce ∧
    ((drained pipeline bytes).ex.world.accounts self).nonce =
      ((paid pipeline bytes).ex.world.accounts self).nonce := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Distinct success: two NEW journal entries. Same-owner success: ZERO new
entries and exactly the existing88/12 state. Direct end is a separate fork. -/
theorem state_observations (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (same88 pipeline bytes).map (fun ex => ex.journal.length) = some 3 ∧
    paymentObservation (drained pipeline bytes) = (0,100,some (.bool true),some (.bool false),5) ∧
    paymentObservation (drainRolled pipeline bytes) = (88,12,some (.bool true),some (.bool false),3) ∧
    paymentObservation (bothPaymentsRolled pipeline bytes) = (93,7,some (.bool true),some (.bool false),1) ∧
    paymentObservation (drainedEnd pipeline bytes) = (0,100,some (.bool false),some (.bool false),0) := by
  rw [same88_identity,drain_rollback_machine,both_payments_rollback_machine]
  unfold drainedEnd drained
  rw [SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem all_memory_retained (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    retainedMemory (paid pipeline bytes) pipeline bytes ∧
    retainedMemory (drained pipeline bytes) pipeline bytes ∧
    retainedMemory (drainRolled pipeline bytes) pipeline bytes ∧
    retainedMemory (bothPaymentsRolled pipeline bytes) pipeline bytes ∧
    retainedMemory (drainedEnd pipeline bytes) pipeline bytes := by
  rw [drain_rollback_machine,both_payments_rollback_machine]
  exact ⟨⟨rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl⟩,
    ⟨rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl⟩⟩

theorem complete_populated_vector (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((drained pipeline bytes).ex.world.accounts sender).balance.val = 0 ∧
    ((drained pipeline bytes).ex.world.accounts self).balance.val = 100 ∧
    ((drained pipeline bytes).ex.world.accounts self).code = some 0 ∧
    ((drained pipeline bytes).ex.world.accounts self).nonce = 1 ∧
    ((drained pipeline bytes).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (drainCheckpoint pipeline bytes).mark = 3 ∧
    (drained pipeline bytes).heap.next = 2 ∧
    (drained pipeline bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (drained pipeline bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (drained pipeline bytes).events = populated.events ∧
    (drained pipeline bytes).logs = (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (drained pipeline bytes).fnLocals = populated.fnLocals := by
  unfold drained drainCheckpoint SourceTransientReachedPayment.paid
  rw [SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem actual_drained_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,drained pipeline bytes) =
      (.ok (.val (.bool true)),(locals,drained pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,drained pipeline bytes) =
      (.ok (.val (.bool false)),(locals,drained pipeline bytes)) ∧
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,drainedEnd pipeline bytes) =
      (.ok (.val (.bool false)),(locals,drainedEnd pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,drainedEnd pipeline bytes) =
      (.ok (.val (.bool false)),(locals,drainedEnd pipeline bytes)) := by
  unfold drainedEnd drained SourceTransientReachedPayment.paid
  rw [SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem end_keeps_drained_world (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (drainedEnd pipeline bytes).ex.world = (drained pipeline bytes).ex.world :=
  Source.endTx_world (drained pipeline bytes).ex

theorem wrong_self_transfer (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    same88 pipeline bytes ≠ (paid pipeline bytes).ex.transfer sender self amount88 := by
  rw [same88_identity,distinct88_success]
  intro same
  have states := Option.some.inj same
  have balances := congrArg (fun ex => (ex.world.accounts sender).balance.val) states
  change 88 = 0 at balances
  cases balances

theorem wrong_same_owner_journal (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (same88 pipeline bytes).map (fun ex => ex.journal.length) ≠ some 5 := by
  rw [same88_identity]
  intro same
  have lengths := Option.some.inj same
  change 3 = 5 at lengths
  cases lengths

theorem wrong_refund (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    same89 pipeline bytes ≠ some (innerRolled pipeline bytes).ex := by
  rw [same89_rejected]
  intro same
  cases same

/-- New alternatives consume the actual first funded prefix; previous actual
prefix execution remains in SourceTransientReachedPayment.reached_client. -/
theorem funded_client (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (innerRestored pipeline bytes).ex.transfer sender self SourceTransientReachedPayment.amount =
      some (paid pipeline bytes).ex ∧
    same88 pipeline bytes = some (paid pipeline bytes).ex ∧
    same89 pipeline bytes = none ∧
    (paid pipeline bytes).ex.transfer sender self amount88 = some (drained pipeline bytes).ex ∧
    drainRolled pipeline bytes = paid pipeline bytes ∧
    bothPaymentsRolled pipeline bytes = innerRestored pipeline bytes :=
  ⟨SourceTransientReachedPayment.transfer_success pipeline bytes,same88_identity pipeline bytes,
    same89_rejected pipeline bytes,distinct88_success pipeline bytes,
    drain_rollback_machine pipeline bytes,both_payments_rollback_machine pipeline bytes⟩

theorem payload_clients (pipeline : Roadmap.Pipeline) :
    ∀ bytes ∈ ([[],binary,SourceTransientBytesEmitControls.boundary33] : List Roadmap.Bytes),
      same88 pipeline bytes = some (paid pipeline bytes).ex ∧
      same89 pipeline bytes = none ∧
      (paid pipeline bytes).ex.transfer sender self amount88 = some (drained pipeline bytes).ex := by
  intro bytes _
  exact ⟨same88_identity pipeline bytes,same89_rejected pipeline bytes,distinct88_success pipeline bytes⟩

/-- Connect the new full-state alternatives to the ACTUAL first source item
execution, consuming the published local producer rather than assuming it. -/
theorem reached_client (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (SourceTransientBytesEmitControls.execution pipeline false bytes).run
      (Source.L0 E,SourceTransientEmitControls.opening) =
      (.ok (.normal locals),(Source.L0 E,completed pipeline bytes)) ∧
    (innerRestored pipeline bytes).ex.transfer sender self SourceTransientReachedPayment.amount =
      some (paid pipeline bytes).ex ∧
    (same88 pipeline bytes).map (fun ex => {paid pipeline bytes with ex:=ex}) =
      some (paid pipeline bytes) ∧
    same89 pipeline bytes = none ∧
    ((paid pipeline bytes).ex.transfer sender self amount88).map
      (fun ex => {paid pipeline bytes with ex:=ex}) = some (drained pipeline bytes) :=
  ⟨(SourceTransientReachedPayment.reached_client pipeline bytes).1,
    SourceTransientReachedPayment.transfer_success pipeline bytes,same88_full_state pipeline bytes,
    same89_rejected pipeline bytes,distinct88_full_state pipeline bytes⟩

#print axioms reached_client

#print axioms same88_identity
#print axioms same89_rejected
#print axioms same88_full_state
#print axioms same89_no_state
#print axioms distinct88_success
#print axioms distinct88_full_state
#print axioms case_results
#print axioms drain_rollback_execution
#print axioms drain_rollback_machine
#print axioms both_payments_rollback_machine
#print axioms outer_after_both_payments
#print axioms end_after_all_rollbacks
#print axioms drained_world_exact
#print axioms other_account_preserved
#print axioms account_fields_preserved
#print axioms state_observations
#print axioms all_memory_retained
#print axioms complete_populated_vector
#print axioms actual_drained_reads
#print axioms end_keeps_drained_world
#print axioms wrong_self_transfer
#print axioms wrong_same_owner_journal
#print axioms wrong_refund
#print axioms funded_client
#print axioms payload_clients
end Solidity.Lowering.V08.SourceTransientSameOwnerPayment
