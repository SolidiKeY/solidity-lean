import Solidity.Lowering.Readonly.EnvironmentCreditControls

/-! Guard individually inhabited credit assumptions being mistaken for joint
source inputs, or static mode being mistaken for balance preservation. Known,
unknown and overflow cases use actual strategy/lookup/credit runs together.
These model witnesses do not claim EVM balance semantics, gas/fork behavior,
constructor reachability or compiler/source-callee/frame adequacy. -/
namespace Solidity.H62.ReadonlyBind.CreditJointControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly
open EnvironmentCreditControls (strategy funded fundedFinal skippedFinal rich)
open EnvironmentCredit (recorded)

def knownGlobal : Glob EB := GB (strategy thisC (word 5))
def unknownGlobal : Glob EB := GB (strategy ext (word 5))
def failedGlobal : Glob EB := GB (strategy thisC (word 1))
def knownStart : St EB := recorded sB thisC (word 5)
def unknownStart : St EB := recorded sB ext (word 5)
def failedStart : St EB := recorded rich thisC (word 1)

/-- All three hypotheses of the known-instance credit law hold at one point. -/
theorem known_inputs :
    knownGlobal.callee sB.events = .credit thisC (word 5) ∧
    (instanceAt knownGlobal thisC : EM EB [] _).run (L0 EB, knownStart) =
      (.ok (some "C"), (L0 EB, knownStart)) ∧
    (credit thisC (word 5) : EM EB [] Unit).run (L0 EB, knownStart) =
      (.ok (), (L0 EB, funded)) := ⟨rfl, rfl, rfl⟩

/-- Both unknown-instance hypotheses hold together, without assuming a credit. -/
theorem unknown_inputs :
    unknownGlobal.callee sB.events = .credit ext (word 5) ∧
    (instanceAt unknownGlobal ext : EM EB [] _).run (L0 EB, unknownStart) =
      (.ok none, (L0 EB, unknownStart)) := ⟨rfl, rfl⟩

/-- Choice, known-instance lookup and actual failed credit hold together. -/
theorem failed_inputs :
    failedGlobal.callee rich.events = .credit thisC (word 1) ∧
    (instanceAt failedGlobal thisC : EM EB [] _).run (L0 EB, failedStart) =
      (.ok (some "C"), (L0 EB, failedStart)) ∧
    (credit thisC (word 1) : EM EB [] Unit).run (L0 EB, failedStart) =
      (.error (.revert []), (L0 EB, failedStart)) := ⟨rfl, rfl, rfl⟩

theorem known_success :
    (envLoop knownGlobal 2 1 true).run (L0 EB, sB) =
      (.ok (.success [7]), (L0 EB, fundedFinal)) := by
  rw [EnvironmentCredit.known knownGlobal 1 1 true sB funded thisC (word 5) "C"
    known_inputs.1 known_inputs.2.1 known_inputs.2.2]
  rw [EnvironmentSteps.answer knownGlobal 0 1 true funded (.success [7]) (by rfl)]
  rfl

theorem unknown_success :
    (envLoop unknownGlobal 2 1 true).run (L0 EB, sB) =
      (.ok (.success [7]), (L0 EB, skippedFinal)) := by
  rw [EnvironmentCredit.unknown unknownGlobal 1 1 true sB ext (word 5)
    unknown_inputs.1 unknown_inputs.2]
  change (envLoop unknownGlobal 1 1 true).run (L0 EB, unknownStart) = _
  rw [EnvironmentSteps.answer unknownGlobal 0 1 true unknownStart (.success [7]) (by rfl)]
  rfl

theorem credit_failure :
    (envLoop failedGlobal 2 1 true).run (L0 EB, rich) =
      (.error (.revert []), (L0 EB, failedStart)) := by
  exact EnvironmentCredit.failed failedGlobal 1 1 true rich failedStart thisC
    (word 1) "C" (.revert []) failed_inputs.1 failed_inputs.2.1 failed_inputs.2.2

/-- A real successful static credit changes balance while retaining storage. -/
theorem known_balance_and_storage :
    (fundedFinal.ex.world.accounts thisC).balance = 5 ∧
    (fundedFinal.ex.world.accounts thisC).storage = (sB.ex.world.accounts thisC).storage := by
  constructor
  · decide +kernel
  · exact EnvironmentCreditControls.storage_kept

/-- Unknown-instance handling records the attempted credit but leaves execution state unchanged. -/
theorem unknown_no_credit :
    skippedFinal.ex = sB.ex ∧ skippedFinal.events =
      [.credit ext (word 5), .answer (.success [7]) none] := ⟨rfl, rfl⟩

end Solidity.H62.ReadonlyBind.CreditJointControls
