import Solidity.Lowering.V08.SourceTransientSameOwnerPayment

/-! Source-only component, kernel-checked by the build.
Actual distinct-owner zero Source transfer preserves WORLD but journals TWO
account updates. Same-owner zero is exact identity. No admitted call/payment,
SourceSpec, intrinsic-frame, compiler/EVM or observed-axiom claim. -/
namespace Solidity.Lowering.V08.SourceTransientZeroPayment
open Solidity Source
open SourceEmitControls
open SourceTransientBytesEmitControls (completed encoded eventSelector)
open SourceTransientOwnerRollback (ownerFrame)
open SourceTransientInnerRollbackOuterCommit (innerRestored)
open SourceTransientReachedPayment (paid senderAfter receiverAfter paymentObservation)
open SourceTransientSameOwnerPayment (zeroWord)

def zeroPaid (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  {paid p bytes with ex:=
    (((paid p bytes).ex.apply (.account sender (fun a => a.withBalance senderAfter))).apply
      (.account self (fun a => a.withBalance receiverAfter)))}
def mark (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.CallFrame :=
  (paid p bytes).ex.enter self sender zeroWord binary false
def rolled (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  {zeroPaid p bytes with ex:=(mark p bytes).rollback (zeroPaid p bytes).ex}
def ended (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.endExecution (zeroPaid p bytes)

theorem distinct_zero (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (paid p bytes).ex.transfer sender self zeroWord = some (zeroPaid p bytes).ex := by
  unfold zeroPaid
  rfl

theorem same_zero (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (paid p bytes).ex.transfer sender sender zeroWord = some (paid p bytes).ex := rfl

/-- WHOLE typed world equality, not just unchanged balances. No conclusion
about the journal follows from this equality. -/
theorem world_identity (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (zeroPaid p bytes).ex.world = (paid p bytes).ex.world := by
  change Source.World.mk _ = Source.World.mk _
  congr 1
  funext address
  by_cases hs : address = sender
  · subst address; rfl
  by_cases ht : address = self
  · subst address; rfl
  · simp only [Source.ExecState.apply,Source.World.set,hs,ht,↓reduceDIte]
    exact SourceTransientReachedPayment.other_account_preserved p bytes address hs ht

theorem full_observations (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (zeroPaid p bytes).ex.world = (paid p bytes).ex.world ∧
    (zeroPaid p bytes).ex.transient = (paid p bytes).ex.transient ∧
    (zeroPaid p bytes).heap = (paid p bytes).heap ∧
    (zeroPaid p bytes).events = populated.events ∧
    (zeroPaid p bytes).logs = (self,eventSelector p ++ encoded bytes) :: populated.logs ∧
    (zeroPaid p bytes).fnLocals = populated.fnLocals ∧
    (zeroPaid p bytes).ex.journal.length = 5 ∧ (paid p bytes).ex.journal.length = 3 :=
  ⟨world_identity p bytes,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem memory_identities (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (zeroPaid p bytes).heap.next = 2 ∧
    (zeroPaid p bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (zeroPaid p bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ := ⟨rfl,rfl,rfl⟩

theorem not_execution_identity (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (zeroPaid p bytes).ex ≠ (paid p bytes).ex := by
  intro same
  have lengths := congrArg (fun ex => ex.journal.length) same
  change 5 = 3 at lengths
  cases lengths

theorem wrong_zero_identity (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (paid p bytes).ex.transfer sender self zeroWord ≠ some (paid p bytes).ex := by
  rw [distinct_zero]
  intro same
  exact not_execution_identity p bytes (Option.some.inj same)

theorem explicit_rollback (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    rolled p bytes = paid p bytes := by
  have execution : (mark p bytes).rollback (zeroPaid p bytes).ex = (paid p bytes).ex :=
    Source.rollback_transfer (paid p bytes).ex (zeroPaid p bytes).ex
      (by decide +kernel : sender ≠ self) zeroWord (distinct_zero p bytes) self sender binary false
  unfold rolled
  rw [execution]
  rfl

theorem direct_end_world (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (ended p bytes).ex.world = (paid p bytes).ex.world :=
  (Source.endTx_world (zeroPaid p bytes).ex).trans (world_identity p bytes)

/-- End erases the journal distinction; it does not make the transfer itself
identity. These are two explicit operations, not an inferred refund rule. -/
theorem end_same_but_prefix_different (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ended p bytes = SourceTransient.endExecution (paid p bytes) ∧
    (zeroPaid p bytes).ex ≠ (paid p bytes).ex := by
  refine ⟨?_,not_execution_identity p bytes⟩
  unfold ended SourceTransient.endExecution Source.ExecState.endTx
  rw [world_identity]
  rfl

theorem ordered_observations (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    [paymentObservation (paid p bytes),paymentObservation (zeroPaid p bytes),
      paymentObservation (rolled p bytes)] =
      [(88,12,some (.bool true),some (.bool false),3),
       (88,12,some (.bool true),some (.bool false),5),
       (88,12,some (.bool true),some (.bool false),3)] ∧
    paymentObservation (ended p bytes) = (88,12,some (.bool false),some (.bool false),0) := by
  rw [explicit_rollback]
  exact ⟨rfl,rfl⟩

theorem actual_reads (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) frame 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,zeroPaid p bytes) = (.ok (.val (.bool true)),(locals,zeroPaid p bytes)) ∧
    (Source.evalE (global p) ownerFrame 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,zeroPaid p bytes) = (.ok (.val (.bool false)),(locals,zeroPaid p bytes)) ∧
    (Source.evalE (global p) frame 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,ended p bytes) = (.ok (.val (.bool false)),(locals,ended p bytes)) ∧
    (Source.evalE (global p) ownerFrame 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,ended p bytes) = (.ok (.val (.bool false)),(locals,ended p bytes)) := ⟨rfl,rfl,rfl,rfl⟩

theorem reached_client (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (SourceTransientBytesEmitControls.execution p false bytes).run
      (Source.L0 E,SourceTransientEmitControls.opening) =
      (.ok (.normal locals),(Source.L0 E,completed p bytes)) ∧
    (innerRestored p bytes).ex.transfer sender self SourceTransientReachedPayment.amount =
      some (paid p bytes).ex ∧
    (paid p bytes).ex.transfer sender self zeroWord = some (zeroPaid p bytes).ex ∧
    (paid p bytes).ex.transfer sender sender zeroWord = some (paid p bytes).ex ∧
    rolled p bytes = paid p bytes :=
  ⟨(SourceTransientReachedPayment.reached_client p bytes).1,
    SourceTransientReachedPayment.transfer_success p bytes,distinct_zero p bytes,
    same_zero p bytes,explicit_rollback p bytes⟩

#print axioms distinct_zero
#print axioms same_zero
#print axioms world_identity
#print axioms full_observations
#print axioms memory_identities
#print axioms not_execution_identity
#print axioms wrong_zero_identity
#print axioms explicit_rollback
#print axioms direct_end_world
#print axioms end_same_but_prefix_different
#print axioms ordered_observations
#print axioms actual_reads
#print axioms reached_client
end Solidity.Lowering.V08.SourceTransientZeroPayment
