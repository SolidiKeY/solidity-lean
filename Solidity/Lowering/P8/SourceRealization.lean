import Solidity.Lowering.P8.FailureProjection
import Solidity.Lowering.P8.ResourceContractLaw1
import Solidity.Source.Session

/-! The actual published Source execution used as the reference anchor.
No alternate evaluator, claimed SourceSpec, independent reference relation,
source origins or realization inhabitant is introduced. The current machine
has a bare horizon: attaching unused FailurePoints would not implement them. -/
namespace Solidity.Lowering.P8.SpecExecution
open Solidity.Roadmap

/-- Execute the actual environment-indexed Source program/session machine. -/
def run (program : P8a.SourceProgram) (environment : SessionEnv) (horizon : Nat) :
    Prefix Event Outcome :=
  Source.sessionAtEvents program.2 environment horizon

/-- SourceLangEvents uses exactly this actual program/environment/horizon.
It holds definitionally (`sourceLangEvents.sem` is `sessionAtEvents`). -/
def MachineAgreement : Prop :=
  ∀ (program : P8a.SourceProgram) (environment : SessionEnv) (horizon : Nat),
    run program environment horizon =
      (Source.sourceLangEvents program.1).sem program.2 environment horizon


/-- Definitional agreement with the actual published Source session. -/
theorem machineAgreement : MachineAgreement := by
  intro program environment horizon
  rfl

/-- info: 'Solidity.Lowering.P8.SpecExecution.machineAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms machineAgreement

/-- The graph of the actual Source machine, before any unimplemented
failure-resource extension. This is not a frozen OperationalReference: its
bare horizon cannot carry that interface's arbitrary failure plans. -/
def Executes (program : P8a.SourceProgram) (environment : SessionEnv)
    (horizon : Nat) (outcome : Prefix Event Outcome) : Prop :=
  run program environment horizon = outcome

/-- Frozen SourceSpec failure replacement and projection cannot be implemented
on a resource retracting into Nat. In particular the current Source session's
bare horizon is insufficient. This obstruction does not alter either API or
claim that attaching an ignored failure plan implements source execution. -/
theorem no_countable_resource (S : P8a.Spec) (failures : P8a.FailureProjection S)
    (encode : S.lang.Res → Nat) (decode : Nat → S.lang.Res)
    (roundtrip : ∀ r, decode (encode r) = r) : False :=
  ResourceContractLaw1.nat_encodable_resource_impossible S failures encode decode roundtrip

end Solidity.Lowering.P8.SpecExecution
