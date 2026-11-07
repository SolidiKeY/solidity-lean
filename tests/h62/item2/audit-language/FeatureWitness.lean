import Solidity.Language.FeatureInfo

/-! Additive audit witnesses for the frozen feature-catalog interface.
These are catalog feasibility checks, not compiler correctness or progress.
The same input supplies the complete hypothesis telescope in each case. -/
namespace Solidity.H62.AuditLanguage
open Language

/-- Simultaneous instance of `Feature.exclusion_complete`, including its
feature argument and the exclusion hypothesis for that exact argument. -/
theorem exclusion_complete_hypotheses :
    ∃ f : Feature, f.info.scope = .exclude := by
  exact ⟨.txOrigin, rfl⟩

/-- Apply the unchanged statement to the exact witnessed input. -/
theorem exclusion_complete_client :
    ∃ u : Unmodelled, Feature.unmodelled? .txOrigin = some u ∧
      u.feature = .txOrigin := by
  exact Feature.exclusion_complete .txOrigin rfl

/-- The diagnostic structure is inhabited globally without any source run. -/
theorem unmodelled_hypotheses : Nonempty Unmodelled := by
  exact ⟨.txOrigin⟩

/-- Concrete importing client for the unchanged diagnostic theorem. -/
theorem unmodelled_client : (.txOrigin : Unmodelled).feature.info.scope = .exclude := by
  exact Unmodelled.excluded .txOrigin

#print axioms exclusion_complete_hypotheses
#print axioms exclusion_complete_client
#print axioms unmodelled_hypotheses
#print axioms unmodelled_client
end Solidity.H62.AuditLanguage
