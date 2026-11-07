import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Language.FixedPoint.Laws

/-!
Guarded regression: separate range and nonzero-divisor witnesses must not be
credited as a simultaneous hypothesis tuple for a fixed-point agreement law.
Reuse imported telescope reflection so every current parameter and hypothesis
is jointly instantiated. Signed division uses a nonzero divisor and a nontrivial
remainder; checked-result and division-agreement tuples carry their actual range
proofs. This is reference-semantics feasibility, not compiler success or solc
code-generation support. Historical ownership replay remains unverifiable.
-/
set_option autoImplicit false

namespace Solidity.H62.AuditLanguage.FixedPointLawWitness
open Solidity.Language.FixedPoint

def ty : FxTy := ⟨false, 8, 0, by decide⟩
def seven : Fx ty := ⟨7, by decide⟩
def two : Fx ty := ⟨2, by decide⟩

theorem truncation_full : hypotheses_of% tdiv_trunc := by
  exact ⟨-7, 3, by decide, True.intro⟩
#verify_hypotheses truncation_full for Solidity.Language.FixedPoint.tdiv_trunc

theorem remainder_full : hypotheses_of% tdiv_rem := by
  exact ⟨-7, -3, by decide, True.intro⟩
#verify_hypotheses remainder_full for Solidity.Language.FixedPoint.tdiv_rem

theorem iterated_division_full : hypotheses_of% tdiv_tdiv := by
  exact ⟨-7, 3, -2, by decide, True.intro⟩
#verify_hypotheses iterated_division_full for Solidity.Language.FixedPoint.tdiv_tdiv

theorem checked_success_full : hypotheses_of% Fx.result_unchecked_of_checked := by
  exact ⟨ty, 7, seven, rfl, True.intro⟩
#verify_hypotheses checked_success_full for Solidity.Language.FixedPoint.Fx.result_unchecked_of_checked

theorem range_agreement_full : hypotheses_of% Fx.result_agree := by
  exact ⟨ty, 7, by decide, True.intro⟩
#verify_hypotheses range_agreement_full for Solidity.Language.FixedPoint.Fx.result_agree

theorem division_agreement_full : hypotheses_of% Fx.div_agree_of_inRange := by
  exact ⟨ty, seven, two, (by intro _; decide), True.intro⟩
#verify_hypotheses division_agreement_full for Solidity.Language.FixedPoint.Fx.div_agree_of_inRange

/-- The chosen division tuple exercises the nonzero, in-range branch. -/
theorem division_branch : two.val ≠ 0 ∧ ty.inRange ((seven.val * ty.scale).tdiv two.val) = true := by
  decide

#print axioms truncation_full
#print axioms remainder_full
#print axioms iterated_division_full
#print axioms checked_success_full
#print axioms range_agreement_full
#print axioms division_agreement_full
#print axioms division_branch
end Solidity.H62.AuditLanguage.FixedPointLawWitness
