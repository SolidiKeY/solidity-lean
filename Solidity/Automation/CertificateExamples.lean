import Solidity.Automation.CertificateTactic
import Solidity.Typing.Constructibility
import Solidity.Calculus.Closers
import Solidity.Calculus.Surface

/-! Regression proofs for leaf checking, certificate production, and verified fallback. -/

namespace Solidity.Automation
open Decide
variable {C : Contract}

example : Leaf.spine (C := C) (.eq .tt .tt) = true := rfl
example : Leaf.spine (C := C) (.eq (.lit (p := .bool) false) .tt) = false := rfl
example : Leaf.spine (C := C) (.eq (p := .uint) (.var 0) (.var 0)) = false := rfl
example : Leaf.spine (C := C) (.not .tt) = false := rfl
example : Leaf.spine (C := C) (.and .tt (.not .tt)) = false := rfl
example : Leaf.spine (C := C) (.imp (.not .tt) (.not .tt)) = false := rfl
example : Leaf.prefer (some false) (fun _ => some true) = some true := rfl
example : Leaf.prefer none (fun _ => some true) = some true := rfl
example : Leaf.prefer (some true) (fun _ => none) = some true := rfl

/-- A real conditional-join step, followed by a structural local leaf witness.
No walk search, general closer, or `verified` certificate constructor is used. -/
def joinedBranch : Certificate C .all .nil
    (.all (.user "b") .bool
      (.modal .box (.cons (.ite (.simple (.local .here)) .nil .nil) .nil) .nil .tt)) :=
  .allIntro (.update rfl rfl (.leaf _ rfl (.spine rfl) rfl))

theorem joinedBranch_proved : Proves C .all [] .nil
    (.all (.user "b") .bool
      (.modal .box (.cons (.ite (.simple (.local .here)) .nil .nil) .nil) .nil .tt)) :=
  joinedBranch.proves

def trueLeaf : Certificate C .all .nil (.tt : Fml C []) :=
  .leaf .tt rfl (.spine rfl) rfl

example : Proves C .all [] .nil (.tt : Fml C []) :=
  Certificate.useOr (some trueLeaf) (fun _ => trueLeaf.proves)

example : Proves C .all [] .nil (.tt : Fml C []) :=
  Certificate.useOr none (fun _ => trueLeaf.proves)

/-- Production must succeed without using the fallback. -/
theorem producedConjunction : Proves C .all [] .nil (.and .tt .tt : Fml C []) := by
  sol_certificate_or (fail "unexpected certificate refusal")

/-- Unsupported symbolic leaves retain their original verified proof. -/
example {φ : Fml C []} (h : Proves C .all [] .nil φ) :
    Proves C .all [] .nil φ := by
  sol_certificate_or (exact h)

open Lean Meta Elab Tactic in
/-- A failed attempt must undo its assignments and preserve local hypotheses. -/
example {φ : Fml C []} (h : Proves C .all [] .nil φ) :
    Proves C .all [] .nil φ := by
  run_tac do
    certificateOr
      (do evalTactic (← `(tactic| assumption)); throwError "refused after assignment")
      (evalTactic (← `(tactic| assumption)))

open Lean Meta Elab Tactic in
/-- Kernel rejection is caught before the original goal is assigned. -/
example {φ : Fml C []} (h : Proves C .all [] .nil φ) :
    Proves C .all [] .nil φ := by
  run_tac do
    certificateOr
      (do (← getMainGoal).assign (mkConst ``True.intro); setGoals [])
      (evalTactic (← `(tactic| assumption)))

/-- The attempt may solve only the selected goal, leaving its sibling intact. -/
example : Proves C .all [] .nil (.tt : Fml C []) ∧ True := by
  constructor
  sol_certificate_or (fail "unexpected certificate refusal")
  trivial

/-- Selected updates may refuse within the budget; the verified path remains. -/
theorem joinedBranchWithFallback : Proves C .all [] .nil
    (.all (.user "b") .bool
      (.modal .box (.cons (.ite (.simple (.local .here)) .nil .nil) .nil) .nil .tt)) := by
  sol_certificate_or (exact joinedBranch_proved)

open Lean Meta Elab Tactic in
/-- A real bounded timeout must reach the original verified fallback. -/
example {φ : Fml C []} (h : Proves C .all [] .nil φ) :
    Proves C .all [] .nil φ := by
  run_tac do
    let exhausted ← IO.mkRef false
    certificateOr
      (tryCatchRuntimeEx
        (Budget.within 1 do
          for _ in [:1000000] do Lean.Core.checkMaxHeartbeats "certificate regression")
        (fun ex => do exhausted.set true; throw ex))
      (do
        unless ← exhausted.get do throwError "timeout attempt was not exercised"
        evalTactic (← `(tactic| assumption)))

/-- Closure expands dependent local lets before synchronous checking. -/
example : Proves C .all [] .nil (.tt : Fml C []) := by
  let φ : Fml C [] := .tt
  change Proves C .all [] .nil φ
  sol_certificate_or (fail "unexpected local-let refusal")

section CleanTailFallback
local instance : InContract := ⟨Tokens⟩
open scoped Scoped

/-- The established clean-tail push/read obligation retains its original premise
and verified strategy when the certificate producer refuses. -/
theorem cleanTailFallback : Proves Tokens .all [] .nil
    (dl!{ cleanTail(storage) = true →
      [ tokens.push(); ] tokens[tokens.length - 1].value == 0 } : Fml Tokens []) := by
  sol_certificate_or (sol_prove)

end CleanTailFallback
end Solidity.Automation
