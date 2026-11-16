import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Source.SemanticsExamples

/-!
Guarded regression: session consistency must preserve completed observations,
not merely extend event lists. Full telescopes reuse the resolved deployment and
request fixture; the always-unfinished observation is refused by its actual
completion. These are source-session clients, not compiler totality or EVM gas
claims. Frozen header fidelity does not establish old/new dependent semantics.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceSessionWitness
open Solidity.Source
open Solidity.Source.SemanticsExamples
open Solidity.Roadmap (Outcome)

theorem append_full : hypotheses_of% sessionGo_extends_app := by
  exact ⟨EB, PS, envS, 30, 2, 0, sB, .success [], [], [], rfl, True.intro⟩
#verify_hypotheses append_full for Solidity.Source.sessionGo_extends_app
#print axioms append_full

theorem extends_full : hypotheses_of% sessionGo_extends := by
  exact ⟨EB, PS, envS, 30, 2, 0, sB, .success [], True.intro⟩
#verify_hypotheses extends_full for Solidity.Source.sessionGo_extends
#print axioms extends_full

theorem monotone_full : hypotheses_of% sessionGo_mono := by
  exact ⟨EB, PS, envS, 2, 3, 30, 40, 0, sB, .success [], by decide, by decide, True.intro⟩
#verify_hypotheses monotone_full for Solidity.Source.sessionGo_mono
#print axioms monotone_full

theorem from_full : hypotheses_of% sessionFrom_consistent := by
  exact ⟨EB, PS, envS, addr 0, True.intro⟩
#verify_hypotheses from_full for Solidity.Source.sessionFrom_consistent
#print axioms from_full

theorem at_full : hypotheses_of% sessionAt_consistent := by
  exact ⟨EB, PS, envS, True.intro⟩
#verify_hypotheses at_full for Solidity.Source.sessionAt_consistent
#print axioms at_full

/-- Once complete, every larger source horizon retains the entire prefix. -/
theorem completed_session_stable {E : Env} (P : SrcProg E)
    (env : Solidity.Roadmap.SessionEnv) (a : Solidity.Roadmap.Address)
    (n m : Nat) (o : Outcome) (bound : n ≤ m)
    (completed : (sessionFrom P env a n).final = some o) :
    sessionFrom P env a m = sessionFrom P env a n :=
  (sessionFrom_consistent P env a n m bound).final_eq completed

/-- The concrete deployment/request completion persists at every larger bound. -/
theorem fixture_stable (m : Nat) (bound : 30 ≤ m) :
    sessionFrom PS envS (addr 0) m = sessionFrom PS envS (addr 0) 30 :=
  completed_session_stable PS envS (addr 0) 30 m _ bound session_runs.1

/-- Reject an observation that erases completion at every horizon. -/
theorem always_unfinished_refused :
    ¬ (∀ n, (sessionFrom PS envS (addr 0) n).final = none) := by
  intro unfinished
  have impossible := unfinished 30
  rw [session_runs.1] at impossible
  cases impossible

#print axioms completed_session_stable
#print axioms fixture_stable
#print axioms always_unfinished_refused
end Solidity.H62.AuditLanguage.SourceSessionWitness
