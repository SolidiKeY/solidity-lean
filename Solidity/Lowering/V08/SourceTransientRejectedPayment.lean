import Solidity.Lowering.V08.SourceTransientReachedPayment

/-! Source-only component, kernel-checked by the build: rejected second Source transfer at an ACTUALLY reached
paid prefix. Option.none
has NO state output and is NOT a Source halt/call-dispatch or automatic-refund
rule. Existing paid input is observed separately; rollback/end are explicit
published operations applied to that input. No replacement interpreter/state
layer, admitted payment/call, SourceSpec or intrinsic/bytecode adequacy. -/
namespace Solidity.Lowering.V08.SourceTransientRejectedPayment
open Solidity Source
open SourceEmitControls
open SourceTransientBytesEmitControls (completed encoded eventSelector)
open SourceTransientReentry (nextOpening nextWritten)
open SourceTransientOwnerRollback (ownerFrame bothWritten)
open SourceTransientOwnerCommit (clearSelf)
open SourceTransientInnerRollbackOuterCommit (innerCleared innerRestored)
open SourceTransientReachedPayment (paid innerRolled outerRolled rollbackEnded paidEnded paymentObservation)

def amount89 : Roadmap.Word := ⟨89,by decide +kernel⟩
def earlySenderAfter : Roadmap.Word := ⟨4,by decide +kernel⟩
def earlyReceiverAfter : Roadmap.Word := ⟨96,by decide +kernel⟩
/-- ONLY the actual Option result; no synthetic post-failure state is defined. -/
def rejectedResult (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :=
  (paid pipeline bytes).ex.transfer sender self amount89
/-- Witness for the DIFFERENT affordable branch at the prepayment state. -/
def earlyLarge (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  {innerRestored pipeline bytes with ex:=
    (((innerRestored pipeline bytes).ex.apply
      (.account sender (fun account => account.withBalance earlySenderAfter))).apply
      (.account self (fun account => account.withBalance earlyReceiverAfter)))}

theorem rejected_at_paid (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    rejectedResult pipeline bytes = none := by
  apply (Source.transfer_none_iff (paid pipeline bytes).ex
    (by decide +kernel : sender ≠ self) amount89).2
  intro allowed
  have enough : 89 ≤ 88 := allowed.1
  exact (by decide +kernel : ¬ ((89 : Nat) ≤ 88)) enough

/-- Failure is specifically insufficient sender funds, NOT destination overflow. -/
theorem paid_failure_reason (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    amount89.val = 89 ∧
    ((paid pipeline bytes).ex.world.accounts sender).balance = 88 ∧
    ¬ (amount89.val ≤ ((paid pipeline bytes).ex.world.accounts sender).balance) ∧
    ((paid pipeline bytes).ex.world.accounts self).balance + amount89.val < 2^256 := by
  exact ⟨rfl,rfl,(by decide +kernel : ¬ ((89 : Nat) ≤ 88)),
    (by decide +kernel : (12 : Nat) + 89 < 2^256)⟩

/-- Actual affordable Option output from the real definition, not an assumed
paid result. This branch starts BEFORE the first transfer5, never after it. -/
theorem early_success (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (innerRestored pipeline bytes).ex.transfer sender self amount89 = some (earlyLarge pipeline bytes).ex := by
  unfold earlyLarge
  rw [SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  rfl

theorem transfer_result_history (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    [(innerRestored pipeline bytes).ex.transfer sender self SourceTransientReachedPayment.amount,
      rejectedResult pipeline bytes] = [some (paid pipeline bytes).ex,none] := by
  rw [SourceTransientReachedPayment.transfer_success,rejected_at_paid]

/-- Observation explicitly pairs a computed Option with its EXISTING input.
It does not infer or manufacture an output state from none. -/
theorem rejected_input_observation (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (rejectedResult pipeline bytes,paid pipeline bytes) = (none,paid pipeline bytes) := by
  rw [rejected_at_paid]

theorem rejected_input_world (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (rejectedResult pipeline bytes,(paid pipeline bytes).ex.world) =
      (none,(((innerRestored pipeline bytes).ex.world.set sender
        (((innerRestored pipeline bytes).ex.world.accounts sender).withBalance
          SourceTransientReachedPayment.senderAfter)).set self
        (((innerRestored pipeline bytes).ex.world.accounts self).withBalance
          SourceTransientReachedPayment.receiverAfter))) := by
  rw [rejected_at_paid,SourceTransientReachedPayment.paid_world_exact]

theorem rejected_input_other_account (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (address : Roadmap.Address) (notSender : address ≠ sender) (notSelf : address ≠ self) :
    (rejectedResult pipeline bytes,((paid pipeline bytes).ex.world.accounts address)) =
      (none,((innerRestored pipeline bytes).ex.world.accounts address)) := by
  rw [rejected_at_paid,
    SourceTransientReachedPayment.other_account_preserved pipeline bytes address notSender notSelf]

/-- Full persistent storage/code/nonce of BOTH input owners are observed intact,
not inferred from rejection itself or account framing of an arbitrary call. -/
theorem rejected_input_accounts (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    rejectedResult pipeline bytes = none ∧
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
      ((innerRestored pipeline bytes).ex.world.accounts self).nonce :=
  ⟨rejected_at_paid pipeline bytes,SourceTransientReachedPayment.account_fields_preserved pipeline bytes⟩

theorem retained_input_vector (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    rejectedResult pipeline bytes = none ∧
    paymentObservation (paid pipeline bytes) = (88,12,some (.bool true),some (.bool false),3) ∧
    (paid pipeline bytes).heap = (completed pipeline bytes).heap ∧
    (paid pipeline bytes).heap.next = 2 ∧
    (paid pipeline bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (paid pipeline bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (paid pipeline bytes).events = populated.events ∧
    (paid pipeline bytes).logs = (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (paid pipeline bytes).fnLocals = populated.fnLocals := by
  rw [rejected_at_paid]
  unfold paid
  rw [SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Separate affordable counterfactual branch; its world is exactly the two
account replacements4/96. It is never substituted for the actual paid input. -/
theorem early_world_exact (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (earlyLarge pipeline bytes).ex.world =
      (((innerRestored pipeline bytes).ex.world.set sender
        (((innerRestored pipeline bytes).ex.world.accounts sender).withBalance earlySenderAfter)).set self
        (((innerRestored pipeline bytes).ex.world.accounts self).withBalance earlyReceiverAfter)) := rfl

theorem early_branch_observation (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((innerRestored pipeline bytes).ex.transfer sender self amount89,
      [paymentObservation (innerRestored pipeline bytes),paymentObservation (earlyLarge pipeline bytes)]) =
    (some (earlyLarge pipeline bytes).ex,
      [(93,7,some (.bool true),some (.bool false),1),
       (4,96,some (.bool true),some (.bool false),3)]) := by
  rw [early_success]
  unfold earlyLarge
  rw [SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  rfl

/-- Prefix observations, exact rejected Option, then EXPLICIT rollback/end
observations of the retained paid INPUT. No state is projected from none. -/
theorem rejected_rollback_branch (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ([paymentObservation (nextOpening pipeline bytes),paymentObservation (nextWritten pipeline bytes),
      paymentObservation (bothWritten pipeline bytes),paymentObservation (innerCleared pipeline bytes),
      paymentObservation (innerRestored pipeline bytes),paymentObservation (paid pipeline bytes)],
     rejectedResult pipeline bytes,
     [paymentObservation (paid pipeline bytes),paymentObservation (innerRolled pipeline bytes),
      paymentObservation (outerRolled pipeline bytes),paymentObservation (rollbackEnded pipeline bytes)]) =
    ([(93,7,some (.bool false),some (.bool false),0),
      (93,7,some (.bool true),some (.bool false),1),
      (93,7,some (.bool true),some (.bool true),2),
      (93,7,some (.bool false),some (.bool true),3),
      (93,7,some (.bool true),some (.bool false),1),
      (88,12,some (.bool true),some (.bool false),3)],
     none,
     [(88,12,some (.bool true),some (.bool false),3),
      (93,7,some (.bool true),some (.bool false),1),
      (93,7,some (.bool false),some (.bool false),0),
      (93,7,some (.bool false),some (.bool false),0)]) := by
  rw [rejected_at_paid,SourceTransientReachedPayment.payment_inner_machine,
    SourceTransientReachedPayment.payment_outer_machine,SourceTransientReachedPayment.end_after_rollbacks,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  rfl

/-- Direct end is an ALTERNATIVE fork from retained paid input, not a refund. -/
theorem rejected_direct_end_branch (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (rejectedResult pipeline bytes,
      [paymentObservation (paid pipeline bytes),paymentObservation (paidEnded pipeline bytes)]) =
    (none,[(88,12,some (.bool true),some (.bool false),3),
           (88,12,some (.bool false),some (.bool false),0)]) := by
  rw [rejected_at_paid,SourceTransientReachedPayment.direct_end_branch]

/-- Existing paid-input and direct-end reads are ACTUAL evaluator equations;
rejection introduces no new state to which they could be transplanted. -/
theorem actual_paid_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    rejectedResult pipeline bytes = none ∧
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
      (.ok (.val (.bool false)),(locals,paidEnded pipeline bytes)) :=
  ⟨rejected_at_paid pipeline bytes,SourceTransientReachedPayment.paid_and_end_reads pipeline bytes⟩

theorem actual_rollback_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,innerRolled pipeline bytes) =
      (.ok (.val (.bool true)),(locals,innerRolled pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,innerRolled pipeline bytes) =
      (.ok (.val (.bool false)),(locals,innerRolled pipeline bytes)) ∧
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,outerRolled pipeline bytes) =
      (.ok (.val (.bool false)),(locals,outerRolled pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,outerRolled pipeline bytes) =
      (.ok (.val (.bool false)),(locals,outerRolled pipeline bytes)) := by
  rw [SourceTransientReachedPayment.payment_inner_machine,
    SourceTransientReachedPayment.payment_outer_machine,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Option.none is not a Source.revert/timeout. Those existing independent
error controls retain the SAME paid input without automatic payment rollback. -/
theorem separate_source_errors (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    rejectedResult pipeline bytes = none ∧
    (Source.evalE (global pipeline) {ownerFrame with static:=true} 4
      SourceTransientEmitControls.setScratch).run (locals,paid pipeline bytes) =
      (.error (.revert []),(locals,paid pipeline bytes)) ∧
    (Source.evalE (global pipeline) ownerFrame 0 SourceTransientEmitControls.setScratch).run
      (locals,paid pipeline bytes) = (.error .timeout,(locals,paid pipeline bytes)) :=
  ⟨rejected_at_paid pipeline bytes,SourceTransientReachedPayment.static_refusal_paid pipeline bytes,
    SourceTransientReachedPayment.timeout_paid pipeline bytes⟩

theorem stale_affordability (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    rejectedResult pipeline bytes ≠ (innerRestored pipeline bytes).ex.transfer sender self amount89 := by
  rw [rejected_at_paid,early_success]
  intro same
  cases same

theorem false_refund (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (paid pipeline bytes).ex ≠ (innerRolled pipeline bytes).ex := by
  rw [SourceTransientReachedPayment.payment_inner_machine]
  intro same
  have balances := congrArg (fun state => (state.world.accounts sender).balance) same
  change 88 = 93 at balances
  cases balances

/-- Reused negatives concern EXPLICIT operations on input, not a hidden world
returned by rejection. Skipping payment5 changes the later89 affordability. -/
theorem negative_controls (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (innerRestored pipeline bytes).ex.transfer sender self SourceTransientReachedPayment.amount ≠
      some (innerRestored pipeline bytes).ex ∧
    (SourceTransientOwnerRollback.outerCheckpoint pipeline bytes).rollback (paid pipeline bytes).ex ≠
      (innerRestored pipeline bytes).ex ∧
    paidEnded pipeline bytes ≠ innerRolled pipeline bytes ∧
    paidEnded pipeline bytes ≠ rollbackEnded pipeline bytes :=
  ⟨SourceTransientReachedPayment.skipped_payment pipeline bytes,
    SourceTransientReachedPayment.wrong_outer_mark pipeline bytes,
    SourceTransientReachedPayment.end_is_not_payment_rollback pipeline bytes⟩

/-- Actual reached source prefix, first successful Option, second rejected
Option, and independent rollback/end facts. No whole handler output premise. -/
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
    (innerRestored pipeline bytes).ex.transfer sender self SourceTransientReachedPayment.amount =
      some (paid pipeline bytes).ex ∧
    rejectedResult pipeline bytes = none ∧
    innerRolled pipeline bytes = innerRestored pipeline bytes ∧
    outerRolled pipeline bytes = nextOpening pipeline bytes ∧
    (paidEnded pipeline bytes).ex.world = (paid pipeline bytes).ex.world :=
  ⟨SourceTransientBytesEmitControls.sequence_complete pipeline bytes 0,
    SourceTransientReentry.reentry_assignment pipeline bytes,
    SourceTransientOwnerRollback.owner_assignment pipeline bytes,
    SourceTransientInnerRollbackOuterCommit.inner_clear_assignment pipeline bytes,
    SourceTransientInnerRollbackOuterCommit.inner_restore_machine pipeline bytes,
    SourceTransientReachedPayment.transfer_success pipeline bytes,rejected_at_paid pipeline bytes,
    SourceTransientReachedPayment.payment_inner_machine pipeline bytes,
    SourceTransientReachedPayment.payment_outer_machine pipeline bytes,
    SourceTransientReachedPayment.paid_end_world pipeline bytes⟩

theorem payload_clients (pipeline : Roadmap.Pipeline) :
    ∀ bytes ∈ ([[],binary,SourceTransientBytesEmitControls.boundary33] : List Roadmap.Bytes),
      rejectedResult pipeline bytes = none ∧
      (innerRestored pipeline bytes).ex.transfer sender self amount89 = some (earlyLarge pipeline bytes).ex ∧
      innerRolled pipeline bytes = innerRestored pipeline bytes ∧
      (paidEnded pipeline bytes).ex.world = (paid pipeline bytes).ex.world := by
  intro bytes _
  exact ⟨rejected_at_paid pipeline bytes,early_success pipeline bytes,
    SourceTransientReachedPayment.payment_inner_machine pipeline bytes,
    SourceTransientReachedPayment.paid_end_world pipeline bytes⟩

#print axioms rejected_at_paid
#print axioms paid_failure_reason
#print axioms early_success
#print axioms transfer_result_history
#print axioms rejected_input_observation
#print axioms rejected_input_world
#print axioms rejected_input_other_account
#print axioms rejected_input_accounts
#print axioms retained_input_vector
#print axioms early_world_exact
#print axioms early_branch_observation
#print axioms rejected_rollback_branch
#print axioms rejected_direct_end_branch
#print axioms actual_paid_reads
#print axioms actual_rollback_reads
#print axioms separate_source_errors
#print axioms stale_affordability
#print axioms false_refund
#print axioms negative_controls
#print axioms reached_client
#print axioms payload_clients
end Solidity.Lowering.V08.SourceTransientRejectedPayment
