import Solidity.Lowering.Readonly.LocationControls
import Solidity.Lowering.Readonly.SourceDispatchControls
import Solidity.Lowering.Readonly.SourceEnvironmentControls
import Solidity.Lowering.Readonly.SourceStatementControls
import Solidity.Lowering.Readonly.EnvironmentHistoryControls
import Solidity.Lowering.Readonly.ReceiverCapture
import Solidity.Backend.WorldCalls.ClosedSourceControls
import Solidity.Backend.WorldCalls.UnknownSourceControls
import Solidity.Backend.WorldCalls.UnknownRevertControls

/-! Actual inputs to premises hidden by named predicates. These are ordinary
joint clients, not deductions of feasibility from inhabited global records.
The three callback guards are separately refuted, with owner intent retained
as pending rather than reclassified into positive or intentional witnesses. -/
namespace Solidity.H62.ReadonlyAudit.HiddenClients
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Backend.WorldCalls Solidity.Lowering.Readonly

theorem byte_effect_client :
    StaticJournal.History LocationControls.C.memory.ex true
      (LocationControls.byteProgram.run (L0 LocationControls.C.E, LocationControls.C.memory)).2.2.ex :=
  LocationControls.byte_effect (L0 LocationControls.C.E) LocationControls.C.memory

theorem dispatch_effect_client :
    StaticJournal.History sB.ex true
      ((dispatch SourceDispatchControls.global {FC with static := true} 1 SourceDispatchControls.cb).run (L0 EB, sB)).2.2.ex :=
  SourceDispatchControls.selected_at_zero (L0 EB) sB

theorem answer_effect_client :
    StaticJournal.History sB.ex true
      ((envLoop (GB (fun _ => .answer (.success [3]))) 1 1 true).run (L0 EB, sB)).2.2.ex :=
  SourceEnvironmentControls.actual_answer_client (L0 EB) sB

theorem skip_effect_client :
    StaticJournal.History sB.ex true
      ((execS SourceStatementControls.global {FC with static := true} 1 0 none
        SourceStatementControls.skipStmt (L0 EB)).run (L0 EB, sB)).2.2.ex :=
  SourceStatementControls.actual_skip_client (L0 EB) sB

theorem closed_storage_client :
    (((callAddr (ClosedSourceControls.global (.success [1,2])) FC 30 ext (word 0) [4,5] true).run
      (L0 EB, ClosedSourceControls.entry)).2.2.ex.world.accounts thisC).storage =
      (ClosedSourceControls.entry.ex.world.accounts thisC).storage :=
  ClosedSourceControls.closed_storage thisC

theorem reentrant_storage_client :
    (((callAddr (GB (SourceCallHistoryControls.callee (.success [1,2]))) FC 30 ext (word 0) [4,5] true).run
      (L0 EB, ClosedSourceControls.entry)).2.2.ex.world.accounts thisC).storage =
      (ClosedSourceControls.entry.ex.world.accounts thisC).storage :=
  ClosedSourceControls.closed_reentrant_storage thisC

theorem actual_unknown_storage_client :
    (((callAddr SourceCallHistoryControls.global FC 1 ext (word 0) [4,5] true).run
      (L0 EB, HistoryRollbackControls.entry)).2.2.ex.world.accounts thisC).storage =
      (HistoryRollbackControls.entry.ex.world.accounts thisC).storage :=
  SourceCallHistoryControls.actual_unknown_client thisC

theorem unknown_storage_client :
    (UnknownSourceControls.finished.ex.world.accounts thisC).storage = (sB.ex.world.accounts thisC).storage :=
  UnknownSourceControls.storage thisC

theorem credit_storage_client :
    (EnvironmentCreditControls.fundedFinal.ex.world.accounts thisC).storage = (sB.ex.world.accounts thisC).storage :=
  EnvironmentHistoryControls.static_credit_storage thisC

theorem exhausted_storage_client :
    (EnvironmentControls.credited.ex.world.accounts thisC).storage =
      (EnvironmentControls.start.ex.world.accounts thisC).storage :=
  EnvironmentHistoryControls.exhausted_callback_keeps_storage thisC

theorem injective_client : ext = ext := @ReceiverCapture.faithful ext ext rfl

/-- Refuting the choice premise suffices to refute the full child conjunction.
No frozen statement is modified; owner classification remains pending. -/
theorem closed_children_joint_impossible (state : St EB) (target sender : Roadmap.Address)
    (value : Roadmap.Word) (input : Roadmap.Bytes) (requested : Bool)
    (choice : (ClosedSourceControls.global (.success [1,2])).callee state.events =
      .reenter target sender value input requested) : False := by
  cases choice

theorem unknown_children_joint_impossible (state : St EB) (target sender : Roadmap.Address)
    (value : Roadmap.Word) (input : Roadmap.Bytes) (requested : Bool)
    (choice : UnknownSourceControls.global.callee state.events = .reenter target sender value input requested) : False := by
  cases choice

theorem revert_children_joint_impossible (state : St EB) (target sender : Roadmap.Address)
    (value : Roadmap.Word) (input : Roadmap.Bytes) (requested : Bool)
    (choice : UnknownRevertControls.global.callee state.events = .reenter target sender value input requested) : False := by
  simp only [UnknownRevertControls.global, GB, UnknownRevertControls.strategy] at choice
  split at choice <;> cases choice

#print axioms byte_effect_client
#print axioms dispatch_effect_client
#print axioms answer_effect_client
#print axioms skip_effect_client
#print axioms closed_storage_client
#print axioms reentrant_storage_client
#print axioms actual_unknown_storage_client
#print axioms unknown_storage_client
#print axioms credit_storage_client
#print axioms exhausted_storage_client
#print axioms injective_client
#print axioms closed_children_joint_impossible
#print axioms unknown_children_joint_impossible
#print axioms revert_children_joint_impossible
end Solidity.H62.ReadonlyAudit.HiddenClients
