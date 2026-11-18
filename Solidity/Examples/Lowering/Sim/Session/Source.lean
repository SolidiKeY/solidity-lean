import Solidity.Correctness.Lowering.Sim.Session.Source
import Solidity.Source.SessionExamples

/-! The source session machine on two small programs from
`Solidity.Source.SessionExamples`: `spin`, whose one request never completes,
and the same contract with no requests, whose session completes at deployment.
Coverage and realization are applied to both; the explicit paths below are
checked by `#guard` (compiled code) to observe the session's prefix. -/
namespace Solidity.Examples.Lowering.Sim.Session.Source

open Solidity.Source Solidity.Source.SessionExamples
open Solidity.Correctness.Lowering.Sim.Session
open Solidity.Roadmap (Outcome SessionEnv)

/-- `envSpin` without requests: the session ends after the deployment. -/
def envIdle : SessionEnv := { envSpin with requests := fun _ _ => none }

/-- Deploy at horizon `n`, then issue up to one action. -/
def twoSteps (el : Elaborated) (env : SessionEnv) (n : Nat) : SourceState el.res.env :=
  match deployStep (progSpin el) env n with
  | .run n (k + 1) i s last => actStep (progSpin el) env n k i s last
  | t => t

theorem twoSteps_reachable (el : Elaborated) (env : SessionEnv) (n : Nat) :
    (sourceMachine (progSpin el) env).Reachable (twoSteps el env n) := by
  have edge := SourceStep.deploy (P := progSpin el) (env := env) n
  unfold twoSteps
  split
  · rename_i n' k i s last h
    rw [h] at edge
    exact (Solidity.Correctness.Sim.Star.single edge).tail (SourceStep.act n' k i s last)
  · exact .single edge

/-- Coverage, at every bound, for `spin` under any environment. -/
theorem spin_covers (el : Elaborated) (r : Nat) :
    ∃ s, (sourceMachine (progSpin el) envSpin).Reachable s ∧
      s.observe = sessionAtEvents (progSpin el) envSpin r :=
  sourceMachine_reaches _ _ r

/-- Realization of the explicit path, at an admissible bound. -/
theorem twoSteps_realized (el : Elaborated) (env : SessionEnv) (n : Nat) :
    ∃ r, ((twoSteps el env n).observe).Le (sessionAtEvents (progSpin el) env r) := by
  obtain ⟨r, -, -, -, le⟩ := sourceMachine_realized _ _ (twoSteps_reachable el env n)
  exact ⟨r, le⟩

/-- A reachable completed state is exactly the session at some bound. -/
theorem completed_is_session (el : Elaborated) (env : SessionEnv) (n : Nat) {o : Outcome}
    (done : (twoSteps el env n).observe.final = some o) :
    ∃ r, (twoSteps el env n).observe = sessionAtEvents (progSpin el) env r := by
  obtain ⟨r, le⟩ := twoSteps_realized el env n
  exact ⟨r, (le.final_eq done).symm⟩

/-- Events and final observation of the explicit path and of the session. -/
def compare (env : SessionEnv) (n : Nat) : Option (Bool × Nat × Bool) :=
  elabSpin.map fun el =>
    let t := (twoSteps el env n).observe
    let p := sessionAtEvents (progSpin el) env n
    (t.events == p.events && t.final == p.final, t.events.length, t.final.isSome)

-- `spin`: two steps observe the session at horizon 30 exactly: the
-- deployment, then the pending transaction's calls and answers, no outcome.
#guard ((compare envSpin 30).map fun (eq, len, fin) => (eq, decide (len > 1), fin)) ==
  some (true, true, false)
-- With no requests the session completes after the deployment receipt, and
-- the machine reaches that completed prefix.
#guard compare envIdle 30 == some (true, 1, true)

end Solidity.Examples.Lowering.Sim.Session.Source
