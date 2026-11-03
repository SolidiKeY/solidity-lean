import Solidity.Lowering.Readonly.EnvironmentCredit
import Solidity.Lowering.Readonly.Controls

/-! Actual source credit controls. Static storage preservation is distinct
from balance preservation. Explicit saturated-balance inputs inhabit real
credit-refusal branches; no constructor reachability/native claim is made. -/
namespace Solidity.Lowering.Readonly.EnvironmentCreditControls
open Solidity.Source Solidity.Source.SemanticsExamples
open EnvironmentCredit EnvironmentSteps

def strategy (target : Solidity.Roadmap.Address) (value : Solidity.Roadmap.Word) : Solidity.Roadmap.Strategy :=
  fun events => if events.any (fun event => match event with | .credit _ _ => true | _ => false)
    then .answer (.success [7]) else .credit target value

def funded : St EB := {recorded sB thisC (word 5) with
  ex := sB.ex.apply (.account thisC fun old => old.withBalance (word 5))}
def fundedFinal : St EB := {funded with events := funded.events ++ [.answer (.success [7]) none]}

theorem static_credit_finishes :
    (envLoop (GB (strategy thisC (word 5))) 2 1 true).run (L0 EB, sB) =
      (.ok (.success [7]), (L0 EB, fundedFinal)) := by
  rw [known (GB (strategy thisC (word 5))) 1 1 true sB funded thisC (word 5) "C"
    (by rfl) (by rfl) (by rfl)]
  rw [answer _ 0 1 true _ (.success [7]) (by rfl)]
  rfl

theorem static_balance_changes :
    (fundedFinal.ex.world.accounts thisC).balance.val = 5 ∧
      (fundedFinal.ex.world.accounts thisC).balance ≠ (sB.ex.world.accounts thisC).balance := by
  decide +kernel

theorem storage_kept :
    (fundedFinal.ex.world.accounts thisC).storage = (sB.ex.world.accounts thisC).storage := by rfl

def skippedFinal : St EB := {sB with events := [.credit ext (word 5), .answer (.success [7]) none]}
theorem unknown_credit_skipped :
    (envLoop (GB (strategy ext (word 5))) 2 1 true).run (L0 EB, sB) =
      (.ok (.success [7]), (L0 EB, skippedFinal)) := by
  rw [unknown _ 1 1 true sB ext (word 5) (by rfl) (by rfl)]
  rw [answer _ 0 1 true _ (.success [7]) (by rfl)]
  rfl

/-- An explicit typed initial balance, not an assertion of constructor reachability. -/
def rich : St EB := {sB with ex := {sB.ex with world := (sB.ex.world.set thisC ((sB.ex.world.accounts thisC).withBalance (word (2 ^ 256 - 1))))}}

theorem overflow_halts :
    (envLoop (GB (strategy thisC (word 1))) 2 1 true).run (L0 EB, rich) =
      (.error (.revert []), (L0 EB, recorded rich thisC (word 1))) :=
  failed _ 1 1 true rich _ thisC (word 1) "C" (.revert []) (by rfl) (by rfl) (by rfl)

def callbackGlobal : Glob EB := {GB answerOnly with
  callee := fun _ => .reenter thisC ext (word 1) (selOf "cb()") false}

theorem callback_overflow_halts :
    (envLoop callbackGlobal 2 1 false).run (L0 EB, rich) =
      (.error (.revert []), (L0 EB, entered rich thisC ext (word 1) (selOf "cb()") false)) :=
  callback_credit_failed _ 1 1 false false rich _ thisC ext (word 1) (selOf "cb()") "C"
    (.revert []) (by rfl) (by decide) (by rfl) (by rfl)

theorem callback_failure_has_only_attempt :
    (entered rich thisC ext (word 1) (selOf "cb()") false).events =
      [.reenter thisC ext (word 1) (selOf "cb()") false] := by rfl

end Solidity.Lowering.Readonly.EnvironmentCreditControls
