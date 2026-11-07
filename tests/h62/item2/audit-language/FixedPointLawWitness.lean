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

/-- Signed input exercises negation away from the unsigned zero-only success. -/
def signedTy : FxTy := ⟨true, 8, 0, by decide⟩
def negativeSeven : Fx signedTy := ⟨-7, by decide⟩

theorem add_range_full : hypotheses_of% Fx.add_agree_of_inRange := by
  exact ⟨ty, seven, two, by decide, True.intro⟩
#verify_hypotheses add_range_full for Solidity.Language.FixedPoint.Fx.add_agree_of_inRange
#print axioms add_range_full

theorem sub_range_full : hypotheses_of% Fx.sub_agree_of_inRange := by
  exact ⟨ty, seven, two, by decide, True.intro⟩
#verify_hypotheses sub_range_full for Solidity.Language.FixedPoint.Fx.sub_agree_of_inRange
#print axioms sub_range_full

theorem neg_range_full : hypotheses_of% Fx.neg_agree_of_inRange := by
  exact ⟨signedTy, negativeSeven, by decide, True.intro⟩
#verify_hypotheses neg_range_full for Solidity.Language.FixedPoint.Fx.neg_agree_of_inRange
#print axioms neg_range_full

theorem mul_range_full : hypotheses_of% Fx.mul_agree_of_inRange := by
  exact ⟨ty, seven, two, by decide, True.intro⟩
#verify_hypotheses mul_range_full for Solidity.Language.FixedPoint.Fx.mul_agree_of_inRange
#print axioms mul_range_full

theorem inc_range_full : hypotheses_of% Fx.inc_agree_of_inRange := by
  exact ⟨ty, seven, by decide, True.intro⟩
#verify_hypotheses inc_range_full for Solidity.Language.FixedPoint.Fx.inc_agree_of_inRange
#print axioms inc_range_full

theorem dec_range_full : hypotheses_of% Fx.dec_agree_of_inRange := by
  exact ⟨ty, seven, by decide, True.intro⟩
#verify_hypotheses dec_range_full for Solidity.Language.FixedPoint.Fx.dec_agree_of_inRange
#print axioms dec_range_full

theorem mod_modes_full : hypotheses_of% Fx.mod_agree' := by
  exact ⟨ty, seven, two, True.intro⟩
#verify_hypotheses mod_modes_full for Solidity.Language.FixedPoint.Fx.mod_agree'
#print axioms mod_modes_full

theorem add_success_full : hypotheses_of% Fx.add_agree := by
  exact ⟨ty, seven, two, ⟨9, by decide⟩, rfl, True.intro⟩
#verify_hypotheses add_success_full for Solidity.Language.FixedPoint.Fx.add_agree
#print axioms add_success_full

theorem sub_success_full : hypotheses_of% Fx.sub_agree := by
  exact ⟨ty, seven, two, ⟨5, by decide⟩, rfl, True.intro⟩
#verify_hypotheses sub_success_full for Solidity.Language.FixedPoint.Fx.sub_agree
#print axioms sub_success_full

theorem neg_success_full : hypotheses_of% Fx.neg_agree := by
  exact ⟨signedTy, negativeSeven, ⟨7, by decide⟩, rfl, True.intro⟩
#verify_hypotheses neg_success_full for Solidity.Language.FixedPoint.Fx.neg_agree
#print axioms neg_success_full

theorem mul_success_full : hypotheses_of% Fx.mul_agree := by
  exact ⟨ty, seven, two, ⟨14, by decide⟩, rfl, True.intro⟩
#verify_hypotheses mul_success_full for Solidity.Language.FixedPoint.Fx.mul_agree
#print axioms mul_success_full

theorem inc_success_full : hypotheses_of% Fx.inc_agree := by
  exact ⟨ty, seven, ⟨8, by decide⟩, rfl, True.intro⟩
#verify_hypotheses inc_success_full for Solidity.Language.FixedPoint.Fx.inc_agree
#print axioms inc_success_full

theorem dec_success_full : hypotheses_of% Fx.dec_agree := by
  exact ⟨ty, seven, ⟨6, by decide⟩, rfl, True.intro⟩
#verify_hypotheses dec_success_full for Solidity.Language.FixedPoint.Fx.dec_agree
#print axioms dec_success_full

theorem div_success_full : hypotheses_of% Fx.div_agree := by
  exact ⟨ty, seven, two, ⟨3, by decide⟩, rfl, True.intro⟩
#verify_hypotheses div_success_full for Solidity.Language.FixedPoint.Fx.div_agree
#print axioms div_success_full

theorem mod_success_full : hypotheses_of% Fx.mod_agree := by
  exact ⟨ty, seven, two, ⟨1, by decide⟩, rfl, True.intro⟩
#verify_hypotheses mod_success_full for Solidity.Language.FixedPoint.Fx.mod_agree
#print axioms mod_success_full

end Solidity.H62.AuditLanguage.FixedPointLawWitness
