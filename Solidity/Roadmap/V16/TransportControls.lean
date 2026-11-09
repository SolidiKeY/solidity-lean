import Solidity.Roadmap.V16.Transport
import Solidity.Roadmap.Controls

/-!
# V16 transport controls

Reuse G07's existing toy semantics and certificate unchanged. These controls
are not a source compiler or an EVM agreement theorem. In particular, the
failure-bound control prevents interpreting no-failure looping as divergence
at every admissible resource bound.
-/

namespace Solidity.Roadmap.V16.Checks
open Solidity.Roadmap.Controls

/-- Actual singleton-hash success, using the existing certificate and bound. -/
theorem success_at_need :
    (toyLang.sem (idPass.run (.succeed [7]) trivial) quietEnv
      (idCert.need (.succeed [7]) trivial quietEnv ⟨1, false⟩)).final =
      some (.success [7]) := by
  have h := completion_at_need idCert (.succeed [7]) trivial quietEnv quietEnv_allowed
    ⟨1, false⟩ trivial (toy_forward _ _ _).1 (toy_forward _ _ _).2 (o := .success [7]) rfl
  exact congrArg Prefix.final h.2

/-- Revert data is transported exactly through the same certificate. -/
theorem revert_at_need :
    (toyLang.sem (idPass.run (.fail [9]) trivial) quietEnv
      (idCert.need (.fail [9]) trivial quietEnv ⟨1, false⟩)).final =
      some (.revert [9]) := by
  have h := completion_at_need idCert (.fail [9]) trivial quietEnv quietEnv_allowed
    ⟨1, false⟩ trivial (toy_forward _ _ _).1 (toy_forward _ _ _).2 (o := .revert [9]) rfl
  exact congrArg Prefix.final h.2

/-- Looping at non-exhausted bounds is inhabited in the existing semantics. -/
theorem loop_without_failure (n : Nat) :
    (toyLang.sem .loop quietEnv ⟨n, false⟩).final = none := rfl

/-- An admissible failure bound of that same loop observes a revert. -/
theorem loop_failure_bound :
    (toyLang.sem .loop quietEnv ⟨1, true⟩).final = some (.revert []) := rfl

/-- Non-exhausted looping cannot be promoted to divergence over all bounds. -/
theorem not_unconditional_loop_divergence :
    ¬ (toyLang.sem .loop quietEnv).Diverges toyLang.Admissible := by
  intro h
  have hf := h ⟨1, true⟩ trivial
  cases hf

/-- Success and failure observations cannot be identified. -/
theorem success_not_revert :
    (toyLang.sem (.succeed [7]) quietEnv ⟨1, false⟩).final ≠ some (.revert [7]) := by
  intro h
  cases h

/-- Erasing revert data changes the observed outcome. -/
theorem revert_data_not_erased :
    (toyLang.sem (.fail [9]) quietEnv ⟨1, false⟩).final ≠ some (.revert []) := by
  intro h
  cases h

/-- Two actual certificates compose on their full existing domains. -/
def twoPass : Cert (idPass.comp idPass (fun _ _ => trivial)) :=
  idCert.comp idCert (fun _ _ => trivial)

/-- Composition retains the concrete non-failure resource, without choice. -/
theorem combination_need :
    twoPass.need (.succeed [7]) trivial quietEnv ⟨1, false⟩ = ⟨1, false⟩ := rfl

/-- Completion transport works through the composed certificate. -/
theorem combination_success :
    (toyLang.sem (.succeed [7]) quietEnv
      (twoPass.need (.succeed [7]) trivial quietEnv ⟨1, false⟩)).final =
      some (.success [7]) := by
  have h := completion_at_need twoPass (.succeed [7]) trivial quietEnv quietEnv_allowed
    ⟨1, false⟩ trivial (toy_forward _ _ _).1 (toy_forward _ _ _).2
    (o := .success [7]) rfl
  exact congrArg Prefix.final h.2

/-- info: 'Solidity.Roadmap.V16.completed_stable' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.V16.completed_stable
/-- info: 'Solidity.Roadmap.V16.completion_at_need' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.V16.completion_at_need
/-- info: 'Solidity.Roadmap.V16.event_at_need' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.V16.event_at_need
/-- info: 'Solidity.Roadmap.V16.event_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.V16.event_invariant
/-- info: 'Solidity.Roadmap.V16.decoded_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Roadmap.V16.decoded_invariant
/-- info: 'Solidity.Roadmap.V16.Checks.success_at_need' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.V16.Checks.success_at_need
/-- info: 'Solidity.Roadmap.V16.Checks.revert_at_need' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.V16.Checks.revert_at_need
/-- info: 'Solidity.Roadmap.V16.Checks.not_unconditional_loop_divergence' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.V16.Checks.not_unconditional_loop_divergence
/-- info: 'Solidity.Roadmap.V16.Checks.combination_success' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.V16.Checks.combination_success
end Solidity.Roadmap.V16.Checks
