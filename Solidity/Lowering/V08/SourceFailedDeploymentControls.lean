import Solidity.Lowering.V08.SourcePayableDeploymentControls
import Solidity.Lowering.V08.SourceFailures

/-! Constructor failure/rollback clients of existing producers. Reason execution
and encoding are consumed unchanged, not reimplemented. The alternative typed
failure body is supplied, not asserted to elaborate the successful syntax unit.
No try-new catch-selection or compiler/runtime-frame correspondence is claimed. -/
namespace Solidity.Lowering.V08.SourceFailedDeploymentControls
open Solidity Source
open SourcePayableDeploymentControls

def failedBody (bytes : Roadmap.Bytes) : Source.RBody E :=
  {sourceBody with items:=.stmt (.expr (.assign (.state savedDecl saved_type rfl) (.bool true))) (.stmt (.expr (SourceFailures.reason bytes)) .nil)}

def failedGlobal (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.Glob E :=
  {global p with prog:={program with ctor:=fun c => if c="Pay" then some (failedBody bytes) else none}}
def rolled : Source.St E :=
  {written with ex:=written.ex.undoN 2,heap:=Source.Heap.empty}
def timedAfterWrite : Source.St E := {written with heap:=Source.Heap.empty}

/-- Actual completed constructor failure AFTER its persistent write. -/
theorem constructor_failed (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.construct (failedGlobal p bytes)
      {this:=self,sender,value:=word 7,static:=false,contract:="Pay"}
      (extra+10) "Pay" (Source.L0 E)).run (Source.L0 E,placed) =
      (.error (.revert (Source.errorData bytes)),(Source.L0 E,written)) := by
  cases p <;> rfl

/-- Source.deploy catches its constructor revert and explicitly restores its mark. -/
theorem deployment_failed (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.deploy (failedGlobal p bytes) (extra+10) "Pay" self sender (word 7) []).run
      (Source.L0 E,populated) =
      (.ok (.revert (Source.errorData bytes)),(Source.L0 E,rolled)) := by
  cases p <;> rfl

theorem rolled_execution : rolled.ex = populated.ex := by
  exact Source.ExecState.undoN_run populated.ex [
    .account self (fun _ => {balance:=word 12,nonce:=1,code:=none,storage:=Source.Storage.empty}),
    .account self (fun a => {a with storage:=a.storage.write savedDecl.path (.bool true)})]

theorem rolled_machine : rolled = {populated with heap:=Source.Heap.empty} := by
  have same : written.ex.undoN 2 = populated.ex := rolled_execution
  change {populated with ex:=written.ex.undoN 2,heap:=Source.Heap.empty} = _
  rw [same]

/-- A short constructor reaches its write but not the completed reason failure. -/
theorem timeout_after_write (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.deploy (failedGlobal p bytes) 6 "Pay" self sender (word 7) []).run
      (Source.L0 E,populated) = (.error .timeout,(Source.L0 E,timedAfterWrite)) := by
  cases p <;> rfl

theorem rollback_vector :
    (rolled.ex.world.accounts sender).balance.val = 93 ∧
    (rolled.ex.world.accounts self).balance.val = 5 ∧
    (rolled.ex.world.accounts self).nonce = 0 ∧
    (rolled.ex.world.accounts self).code = none ∧
    (rolled.ex.world.accounts self).storage.read savedDecl.path = some (.bool false) ∧
    rolled.ex.journal.length = 2 ∧ rolled.heap.next = 0 ∧
    rolled.logs = populated.logs ∧ rolled.events = populated.events ∧
    rolled.fnLocals = populated.fnLocals := by
  rw [rolled_machine]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem timeout_vector :
    (timedAfterWrite.ex.world.accounts self).balance.val = 12 ∧
    (timedAfterWrite.ex.world.accounts self).storage.read savedDecl.path = some (.bool true) ∧
    (timedAfterWrite.ex.world.accounts self).code = none ∧
    timedAfterWrite.ex.journal.length = 4 ∧ timedAfterWrite.heap.next = 0 ∧
    timedAfterWrite.logs = populated.logs ∧ timedAfterWrite.events = populated.events ∧
    timedAfterWrite.fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def targetBody (bytes : Roadmap.Bytes) : Prog Cell [] [] :=
  .cons (.block SourcePayableDeploymentControls.targetBody)
    (.cons (SourceFailures.reasonStatement bytes) .nil)
def targetFailure (bytes : Roadmap.Bytes) :=
  targetInitial.create () Controls.self (targetBody bytes) targetContext

theorem target_failed (bytes : Roadmap.Bytes) :
    targetFailure bytes = .error (.revertWith (Semantics.encodeError bytes)) := by
  change Except.error (THalt.ofData (Semantics.encodeError bytes ++ [])) = _
  rw [List.append_nil]
  rfl

theorem target_atomic (bytes : Roadmap.Bytes) :
    ContractWorld.atomic targetInitial (targetFailure bytes) =
      (targetInitial,.error (.revertWith (Semantics.encodeError bytes))) := by
  rw [target_failed]
  rfl

def sourcePayload (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Option Roadmap.Bytes :=
  match ((Source.deploy (failedGlobal p bytes) 10 "Pay" self sender (word 7) []).run
    (Source.L0 E,populated)).1 with
  | .ok (.revert data) => some data
  | _ => none
def targetPayload (bytes : Roadmap.Bytes) : Option (List UInt8) :=
  match targetFailure bytes with
  | .error (.revertWith data) => some data
  | _ => none

/-- Reuse the checked old encoding law only for the resulting exact payload. -/
theorem exact_payload (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    sourcePayload p bytes = targetPayload bytes := by
  unfold sourcePayload targetPayload
  rw [deployment_failed p 0 bytes,target_failed]
  exact congrArg some (errorData_transport_total bytes)

theorem payload_clients (p : Roadmap.Pipeline) :
    sourcePayload p [] = targetPayload [] ∧
    sourcePayload p [0,255,128] = targetPayload [0,255,128] ∧
    sourcePayload p (List.replicate 33 0x81) = targetPayload (List.replicate 33 0x81) :=
  ⟨exact_payload p [],exact_payload p [0,255,128],exact_payload p (List.replicate 33 0x81)⟩

theorem wrong_timeout_rollback : timedAfterWrite.ex ≠ rolled.ex := by
  intro same
  have length := congrArg (fun x => x.journal.length) same
  rw [rolled_execution] at length
  change 4 = 2 at length
  cases length

/-- Only the explicitly compared candidate fields; not a whole-world relation. -/
theorem rollback_candidate :
    ((rolled.ex.world.accounts self).balance.val,(rolled.ex.world.accounts self).code.isSome) =
      ((targetInitial.balance Controls.self).1.toNat,(targetInitial.accounts Controls.self).isSome) := by
  rw [rolled_machine]
  rfl

theorem wrong_heap_rollback : rolled.heap ≠ populated.heap := by
  intro same
  have next := congrArg (fun h => h.next) same
  change 0 = 1 at next
  cases next

theorem wrong_revert_payload (p : Roadmap.Pipeline) :
    sourcePayload p [0,255,128] ≠ targetPayload [0,255,129] := by
  cases p <;> decide +kernel

/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.constructor_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms constructor_failed
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.deployment_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms deployment_failed
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.rolled_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rolled_execution
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.rolled_machine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rolled_machine
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.timeout_after_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms timeout_after_write
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.rollback_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rollback_vector
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.timeout_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms timeout_vector
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.target_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_failed
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.target_atomic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_atomic
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.exact_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exact_payload
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.payload_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms payload_clients
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.wrong_timeout_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_timeout_rollback
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.rollback_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rollback_candidate
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.wrong_heap_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_heap_rollback
/-- info: 'Solidity.Lowering.V08.SourceFailedDeploymentControls.wrong_revert_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_revert_payload
end Solidity.Lowering.V08.SourceFailedDeploymentControls
