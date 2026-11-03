import Solidity.Lowering.V08.SourceFailedDeploymentControls

/-! Failed deployment continues through actual published session credit handling.
Supplied creation address/program are not canonical SourceSpec/compiler proofs. -/
namespace Solidity.Lowering.V08.SourceDeploymentSessionControls
open Solidity Source
open SourcePayableDeploymentControls SourceFailedDeploymentControls

def environment : Roadmap.SessionEnv :=
  {deployer:=sender,deployNonce:=⟨0,by decide⟩,deployValue:=word 7,deployArgs:=[],
    balance:=fun _ => word 5,hasCode:=fun _ _ => false,
    requests:=fun _ i => if i=0 then some (.credit self (word 9)) else none,
    callee:=fun _ => .answer (.success [])}
def sourceProgram (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.SrcProg E :=
  ⟨(failedGlobal p bytes).prog,p,Source.SemanticsExamples.toyFixed,"Pay"⟩

/-- An uninstalled failed candidate receives an event, not an account credit. -/
theorem uninstalled_credit_actual (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    Source.runAt (fun _ => do
      if (← Source.instanceAt ((sourceProgram p bytes).glob environment) self).isSome then
        Source.credit self (word 9)) rolled 0 = (.ok (),rolled) := by
  cases p <;> rfl

/-- Complete constructor failure at the populated machine followed by the real
sessionGo branch: the ordered old events remain and final failure is unchanged. -/
theorem reached_continuation (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (match (Source.deploy (failedGlobal p bytes) 10 "Pay" self sender (word 7) []).run
       (Source.L0 E,populated) with
     | (.ok o,(_,s)) => Source.sessionGo (sourceProgram p bytes) environment 10 2 0 s o
     | _ => ⟨[],none⟩) =
      ⟨rolled.events ++ [.credit self (word 9)],some (.revert (Source.errorData bytes))⟩ := by
  rw [deployment_failed p 0 bytes]
  cases p <;> rfl

def binaryExpected : List Roadmap.Event :=
  [.deploy sender (word 7) [] (.revert (Source.errorData [0,255,128])) none,
   .credit self (word 9)]

theorem failed_session_actual (p : Roadmap.Pipeline) :
    (Source.sessionFrom (sourceProgram p [0,255,128]) environment self 20).events = binaryExpected ∧
    (Source.sessionFrom (sourceProgram p [0,255,128]) environment self 20).final =
      some (.revert (Source.errorData [0,255,128])) := by cases p <;> decide +kernel

theorem event_is_not_installation : (rolled.ex.world.accounts self).code = none ∧
    (rolled.ex.world.accounts self).balance.val = 5 ∧ rolled.ex.journal.length = 2 :=
  ⟨rfl,rfl,rfl⟩

theorem wrong_final_success (p : Roadmap.Pipeline) :
    (Source.sessionFrom (sourceProgram p [0,255,128]) environment self 20).final ≠
      some (.success []) := by
  rw [(failed_session_actual p).2]
  intro wrong
  cases wrong

/-- info: 'Solidity.Lowering.V08.SourceDeploymentSessionControls.uninstalled_credit_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms uninstalled_credit_actual
/-- info: 'Solidity.Lowering.V08.SourceDeploymentSessionControls.reached_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reached_continuation
/-- info: 'Solidity.Lowering.V08.SourceDeploymentSessionControls.failed_session_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms failed_session_actual
/-- info: 'Solidity.Lowering.V08.SourceDeploymentSessionControls.event_is_not_installation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms event_is_not_installation
/-- info: 'Solidity.Lowering.V08.SourceDeploymentSessionControls.wrong_final_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_final_success
end Solidity.Lowering.V08.SourceDeploymentSessionControls
