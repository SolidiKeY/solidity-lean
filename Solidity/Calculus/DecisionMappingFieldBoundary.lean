import Solidity.Calculus.Decision
import Solidity.Calculus.DecisionMappingFieldReason

/-! # Target boundary for the mapping-bearing reversed-field class
Admission is independent of the producer map-free realization guard.
No global coverage, countermodel or unknown theorem is asserted.
-/
namespace Solidity.Decide.ResidueReason

theorem MappingReversedFreshField.target {C : Contract} {φ : Fml C []}
    (w : MappingReversedFreshField φ) (waivers : Waivers) : φ.inTarget waivers = true := by
  rcases w with ⟨x, s, f, p, value, hf, hm, heq⟩
  subst φ
  cases p <;> rfl

end Solidity.Decide.ResidueReason
