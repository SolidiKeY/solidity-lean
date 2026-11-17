import Solidity.Correctness.IntrinsicSession.Laws.Common
import Solidity.Examples.IntrinsicSession.Spec

/-! The shared boundary lemmas on the one-contract session of `Spec.lean`, resumed at `w`
with the first action `q`. -/
namespace Solidity.Examples.IntrinsicSession.Laws.Common

open Solidity.Roadmap Solidity.Semantics.IntrinsicSession Solidity.Examples.IntrinsicSession.Spec
open Solidity.Goals.IntrinsicSession (Code Good Observed)

variable {C : Contract} {code : Code} {w : ContractWorld.World code.catalog} {F : Fixed}
  {r : Bound} {e : SessionEnv} (s : OneRequest C code w F r e) (good : Good (spec F) r)

/-- The start is a boundary: observed, a walk, listed first at every good bound. -/
example : Observed (spec F) s.start e [] ∧ Walks F s.start e [] 0 w ∧
    r = Bound.upto r.horizon ∧ (s.start.boundaries (runOf F s.start e r).worlds)[0]? = some w :=
  have b : (view F).Boundary s.start e [] 0 ⟨code, w⟩ := Boundary.resume F ⟨code, w⟩ e
  ⟨Boundary.observed b, boundary_mk.1 b, good_eq good, (Boundary.reached b good (Nat.zero_le _)).1⟩

/-- **The request completes**: one transaction, then a listed boundary at its world. -/
example (done : (act F s.start e [] 0 w (.request s.q)).stops = false)
    (pre : [] <+: ((spec F).lang.sem s.start e r).events) :
    (∃ out, (act F s.start e [] 0 w (.request s.q)).events =
      [.tx s.q.sender s.q.target s.q.value s.q.timestamp s.q.input out]) ∧
    (∃ ω ∈ (spec F).worlds s.start e r,
      (view F).typed ω = ⟨code, (act F s.start e [] 0 w (.request s.q)).world⟩) ∧
    (((spec F).lang.sem s.start e r).events = [] ∨
      (act F s.start e [] 0 w (.request s.q)).events <+: ((spec F).lang.sem s.start e r).events) :=
  have b := Boundary.resume F ⟨code, w⟩ e
  ⟨request_events s.funded done, Boundary.listed (Boundary.next b s.next done) good s.room,
    Boundary.events_cases b s.next done good pre⟩

/-- Drops, credits, ends and stops at any boundary of the session. -/
example {h n q t v} (b : (view F).Boundary s.start e h n ⟨code, w⟩) (le : n ≤ r.horizon) :
    (e.requests h n = some (.request q) → ¬ Funded F e h q →
      (view F).Boundary s.start e h (n + 1) ⟨code, w⟩) ∧
    (e.requests h n = some (.credit t v) →
      (view F).Boundary s.start e (h ++ [.credit t v]) (n + 1) ⟨code, (credit w t v).world⟩) ∧
    (e.requests h n = none → ((spec F).lang.sem s.start e r).events = h) ∧
    ∀ a, e.requests h n = some a → (act F s.start e h n w a).stops = true →
      ((spec F).lang.sem s.start e r).events = h :=
  ⟨Boundary.dropped b, Boundary.credited b, fun i => (Boundary.idle b i good le).1,
    fun _ a st => Boundary.stops b a st good le⟩

/-- The deployment of the code; listed worlds resume as themselves and are boundaries. -/
example {ω} (mem : ω ∈ (spec F).worlds s.start e r) (stop : (deployed F code e).stops = true) :
    (spec F).worlds (Start.initial code) e r = [] ∧ ω = (view F).resume ((view F).typed ω) ∧
    ∃ h n, (view F).Boundary s.start e h n ((view F).typed ω) ∧
      h <+: ((spec F).lang.sem s.start e r).events :=
  ⟨(deploy_stops stop good).2, (listed_resume mem).1, listed_boundary good mem⟩

end Solidity.Examples.IntrinsicSession.Laws.Common
