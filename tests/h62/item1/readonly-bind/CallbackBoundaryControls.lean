import Solidity.Lowering.Readonly.EnvironmentCreditControls

/-! Guard callback depth/static refusal being confused with credit failure or
suppressed strategy continuation. These actual source runs use the same saturated
balance and nonzero callback value. They test the model guard before credit,
not EVM gas/fork behavior, deployed constructor reachability or compiler adequacy.
-/
namespace Solidity.H62.ReadonlyBind.CallbackBoundaryControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly
open EnvironmentSteps
open EnvironmentCreditControls (rich)

/-- After a completed callback attempt, answer with distinct observable bytes. -/
def strategy : Solidity.Roadmap.Strategy :=
  fun events => if events.any (fun event => match event with | .reentered _ => true | _ => false)
    then .answer (.success [7]) else .reenter thisC ext (word 1) (selOf "cb()") false

def global : Glob EB := { GB answerOnly with callee := strategy }

def attempted : St EB := entered rich thisC ext (word 1) (selOf "cb()") false
def refused : St EB := completed attempted (.revert [])
def finished : St EB := { refused with events := refused.events ++ [.answer (.success [7]) none] }

/-- Both hypotheses of the depth-refusal specialization hold together. -/
theorem depth_inputs :
    global.callee rich.events = .reenter thisC ext (word 1) (selOf "cb()") false ∧
    (decide (1024 ≥ 1024) || (false && decide ((word 1).val ≠ 0))) = true :=
  ⟨rfl, by decide⟩

/-- Both hypotheses of the inherited-static nonzero-value refusal hold together. -/
theorem static_inputs :
    global.callee rich.events = .reenter thisC ext (word 1) (selOf "cb()") false ∧
    (decide (1023 ≥ 1024) || (true && decide ((word 1).val ≠ 0))) = true :=
  ⟨rfl, by decide⟩

theorem depth_refusal_continues :
    (envLoop global 2 1024 false).run (L0 EB, rich) =
      (.ok (.success [7]), (L0 EB, finished)) := by
  rw [EnvironmentSteps.refused global 1 1024 false false rich thisC ext
    (word 1) (selOf "cb()") depth_inputs.1 depth_inputs.2]
  change (envLoop global 1 1024 false).run (L0 EB, refused) = _
  rw [EnvironmentSteps.answer global 0 1024 false refused (.success [7]) (by rfl)]
  rfl

theorem static_refusal_continues :
    (envLoop global 2 1023 true).run (L0 EB, rich) =
      (.ok (.success [7]), (L0 EB, finished)) := by
  rw [EnvironmentSteps.refused global 1 1023 true false rich thisC ext
    (word 1) (selOf "cb()") static_inputs.1 static_inputs.2]
  change (envLoop global 1 1023 true).run (L0 EB, refused) = _
  rw [EnvironmentSteps.answer global 0 1023 true refused (.success [7]) (by rfl)]
  rfl

/-- All four credit-failure hypotheses hold together at the admitted boundary. -/
theorem admitted_inputs :
    global.callee rich.events = .reenter thisC ext (word 1) (selOf "cb()") false ∧
    (decide (1023 ≥ 1024) || (false && decide ((word 1).val ≠ 0))) = false ∧
    (instanceAt global thisC : EM EB [] _).run (L0 EB, attempted) =
      (.ok (some "C"), (L0 EB, attempted)) ∧
    (credit thisC (word 1) : EM EB [] Unit).run (L0 EB, attempted) =
      (.error (.revert []), (L0 EB, attempted)) :=
  ⟨rfl, by decide, rfl, rfl⟩

/-- At the adjacent admitted depth, credit actually fails before completion. -/
theorem admitted_credit_failure :
    (envLoop global 2 1023 false).run (L0 EB, rich) =
      (.error (.revert []), (L0 EB, attempted)) := by
  exact EnvironmentCredit.callback_credit_failed global 1 1023 false false
    rich attempted thisC ext (word 1) (selOf "cb()") "C" (.revert [])
    admitted_inputs.1 admitted_inputs.2.1 admitted_inputs.2.2.1 admitted_inputs.2.2.2

/-- A refused attempt completes and continues, unlike admitted credit failure. -/
theorem observed_events :
    finished.events = [.reenter thisC ext (word 1) (selOf "cb()") false,
      .reentered (.revert []), .answer (.success [7]) none] ∧
    attempted.events = [.reenter thisC ext (word 1) (selOf "cb()") false] :=
  ⟨rfl, rfl⟩

theorem refusal_keeps_balance :
    (finished.ex.world.accounts thisC).balance = (rich.ex.world.accounts thisC).balance := rfl

end Solidity.H62.ReadonlyBind.CallbackBoundaryControls
