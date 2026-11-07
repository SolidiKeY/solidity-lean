import Solidity.Lowering.StorageOps.SourceByteStorageBarrier
import Solidity.Lowering.StorageOps.SourceByteStoragePreparedControls

/-! Actual byte snapshot failure ordering. A malformed source need not time
out; a missing destination and static refusal cannot precede valid capture.
No failed execution is identified with automatic world rollback. -/
namespace Solidity.Lowering.StorageOps.SourceByteStorageBarrierControls
open Solidity
open SourceByteStoragePreparedControls

def initial : Source.Locals env.layout Γ × Source.St env := (locals,seed 2 5)
def missing : Source.SPath := ⟨⟨some "C","missing"⟩,[]⟩
def client (fuel : Nat) (short : fuel≤2) :=
 SourceByteStorageBarrier.load_timeout {frame with static:=true} left fuel 0 2
 (fun j=>if j=0 then 53 else 59) initial short (by
  intro j member
  have cases : j=0 ∨ j=1 := by omega
  rcases cases with rfl | rfl <;> rfl)
def shifted_client (fuel : Nat) (short : fuel≤2) :=
 SourceByteStorageBarrier.load_timeout frame left fuel 1 2
 (fun j=>if j=1 then 59 else 61) initial short (by
  intro j member
  have cases : j=0 ∨ j=1 := by omega
  rcases cases with rfl | rfl <;> rfl)
def copies :=
 [ (program 0 left missing).run initial,
   (program 1 left missing).run initial,
   (program 2 left missing).run initial,
   (program 3 left missing).run initial,
   (program 4 left missing).run initial,
   (program 5 left missing).run initial,
   (program 4 left missing {frame with static:=true}).run initial,
   (program 4 missing right).run initial,
   (program 0 right right).run initial,
   (program 1 right right).run initial ]
def outcomes : Prop := copies=
 [(.error .timeout,initial),(.error .timeout,initial),(.error .timeout,initial),
  (.error .timeout,initial),(.error .timeout,initial),
  (.error (.stuck "storage cell without a value"),initial),(.error .timeout,initial),
  (.error (.stuck "storage cell without a value"),initial),(.error .timeout,initial),(.ok (),initial)]
def ordered : Prop := copies.map (fun r=>
 (r.2.1,row (r.2.2.ex.world.accounts address).storage,context r.2.2,journalRows r.2.2))=
 List.replicate 10
 (locals,(some 2,some 5,[some [7],some [17],some [23],some [71],some [73],some [97]],[some [53],some [59],some [61]]),
 (19,3,some 0,0,true,0,[(7,[9,8])],[.bool]),
 [(7,(some 2,some 5,[some [7],some [17],some [23],some [71],some [73],some [97]],[some [53],some [59],some [61]]),19,3,some 0)])
def captures :=
 [ (Source.loadBytes (E:=env) (Γ:=Γ) frame 0 missing 0 1).run initial,
   (Source.loadBytes (E:=env) (Γ:=Γ) frame 1 missing 0 1).run initial,
   (Source.loadBytes (E:=env) (Γ:=Γ) frame 2 left 1 2).run initial,
   (Source.loadBytes (E:=env) (Γ:=Γ) frame 3 left 1 2).run initial ]
def capture_rows : Prop := captures=
 [(.error .timeout,initial),(.error (.stuck "storage cell without a value"),initial),
  (.error .timeout,initial),(.ok [59,61],initial)]
theorem outcome_certificate : outcomes := by rfl
theorem observations : ordered := by rfl
theorem capture_observations : capture_rows := by rfl
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageBarrierControls.client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms client
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageBarrierControls.shifted_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shifted_client
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageBarrierControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageBarrierControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageBarrierControls.capture_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capture_observations
end Solidity.Lowering.StorageOps.SourceByteStorageBarrierControls
