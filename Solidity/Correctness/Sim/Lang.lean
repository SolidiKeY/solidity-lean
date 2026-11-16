import Solidity.Correctness.Sim.Observation
import Solidity.Roadmap.G49Final.PassCorrectAdapters

/-! Instantiate the simulation framework with the existing Lang adapter.
No concrete lowering producer or session lift is constructed here. -/
namespace Solidity.Correctness.Sim
open Solidity.Roadmap Solidity.Roadmap.G49Final

/-- Two diagrams and their resource/coverage proofs yield the existing
PassCorrect for specified typed programs of existing roadmap languages. -/
def lang_passCorrect (A B : Lang Event Outcome) (p : A.Prog) (q : B.Prog)
    (S : A.Env → Machine) (T : B.Env → Machine) (envAbs : B.Env → A.Env)
    (envSound : ∀ e, B.Allowed e → A.Allowed (envAbs e))
    (envOnto : ∀ e, A.Allowed e → ∃ e', B.Allowed e' ∧ envAbs e' = e)
    (forward : ∀ e, Diagram (S (envAbs e)) (T e))
    (reverse : ∀ e, Diagram (T e) (S (envAbs e)))
    (F : ForwardResources (Behaviour.ofLang A p) (Behaviour.ofLang B q) S T envAbs forward)
    (R : BackwardResources (Behaviour.ofLang A p) (Behaviour.ofLang B q) S T envAbs reverse) :
    PassCorrect (Behaviour.ofLang A p) (Behaviour.ofLang B q) :=
  passCorrect_of_simulations envAbs envSound envOnto forward reverse F R

/-- The resulting certificate preserves completed source runs exactly. -/
theorem completed_forward {a b : Behaviour} (certificate : PassCorrect a b)
    {e : b.Env} {r : a.Res} (allowed : b.Allowed e)
    (ready : a.Ready (certificate.envAbs e) r) {o : Outcome}
    (done : (a.observe (certificate.envAbs e) r).final = some o) :
    b.observe e (certificate.need e r) = a.observe (certificate.envAbs e) r :=
  (certificate.need_ok e r allowed ready).2.final_eq done

/-- Completed target runs have matching source completions under the frozen
backward premises, with no Forward requirement on either run. -/
theorem completed_backward {a b : Behaviour} (certificate : PassCorrect a b)
    {e : b.Env} {r : b.Res} (allowed : b.Allowed e)
    (admissible : b.Admissible r) (guard : b.Guard e r) {o : Outcome}
    (done : (b.observe e r).final = some o) :
    ∃ rs, a.Admissible rs ∧ a.Guard (certificate.envAbs e) rs ∧
      a.observe (certificate.envAbs e) rs = b.observe e r := by
  obtain ⟨rs, ha, hg, le⟩ := certificate.back e r allowed admissible guard
  exact ⟨rs, ha, hg, le.final_eq done⟩

end Solidity.Correctness.Sim
