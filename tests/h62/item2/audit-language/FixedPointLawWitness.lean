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


/-- One decimal digit makes product truncation exercise a genuine remainder. -/
def decimalTy : FxTy := ⟨false, 8, 1, by decide⟩

theorem pow_width_full : hypotheses_of% pow_two_le := by
  exact ⟨8, 16, by decide, True.intro⟩
#verify_hypotheses pow_width_full for Solidity.Language.FixedPoint.pow_two_le
#print axioms pow_width_full

theorem decimal_power_full : hypotheses_of% pow_ten_ne := by
  exact ⟨2, True.intro⟩
#verify_hypotheses decimal_power_full for Solidity.Language.FixedPoint.pow_ten_ne
#print axioms decimal_power_full

theorem wrapped_result_full : hypotheses_of% Fx.result_val := by
  exact ⟨ty, .checked, 7, seven, rfl, True.intro⟩
#verify_hypotheses wrapped_result_full for Solidity.Language.FixedPoint.Fx.result_val
#print axioms wrapped_result_full

theorem checked_result_value_full : hypotheses_of% Fx.result_checked_val := by
  exact ⟨ty, 7, seven, rfl, True.intro⟩
#verify_hypotheses checked_result_value_full for Solidity.Language.FixedPoint.Fx.result_checked_val
#print axioms checked_result_value_full

theorem unsigned_negation_full : hypotheses_of% Fx.neg_unsigned := by
  exact ⟨ty, rfl, seven, True.intro⟩
#verify_hypotheses unsigned_negation_full for Solidity.Language.FixedPoint.Fx.neg_unsigned
#print axioms unsigned_negation_full

theorem product_truncation_full : hypotheses_of% Fx.mul_trunc := by
  exact ⟨decimalTy, ⟨7, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, rfl, True.intro⟩
#verify_hypotheses product_truncation_full for Solidity.Language.FixedPoint.Fx.mul_trunc
#print axioms product_truncation_full

theorem product_exact_full : hypotheses_of% Fx.mul_exact := by
  exact ⟨decimalTy, ⟨15, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, rfl, by decide, True.intro⟩
#verify_hypotheses product_exact_full for Solidity.Language.FixedPoint.Fx.mul_exact
#print axioms product_exact_full

theorem quotient_truncation_full : hypotheses_of% Fx.div_trunc := by
  exact ⟨ty, seven, two, ⟨3, by decide⟩, rfl, True.intro⟩
#verify_hypotheses quotient_truncation_full for Solidity.Language.FixedPoint.Fx.div_trunc
#print axioms quotient_truncation_full

theorem quotient_exact_full : hypotheses_of% Fx.div_exact := by
  exact ⟨decimalTy, ⟨6, by decide⟩, ⟨2, by decide⟩, ⟨30, by decide⟩, rfl, by decide, True.intro⟩
#verify_hypotheses quotient_exact_full for Solidity.Language.FixedPoint.Fx.div_exact
#print axioms quotient_exact_full

theorem increment_value_full : hypotheses_of% Fx.inc_val := by
  exact ⟨ty, seven, ⟨8, by decide⟩, rfl, True.intro⟩
#verify_hypotheses increment_value_full for Solidity.Language.FixedPoint.Fx.inc_val
#print axioms increment_value_full

theorem decrement_value_full : hypotheses_of% Fx.dec_val := by
  exact ⟨ty, seven, ⟨6, by decide⟩, rfl, True.intro⟩
#verify_hypotheses decrement_value_full for Solidity.Language.FixedPoint.Fx.dec_val
#print axioms decrement_value_full

theorem rescale_truncation_full : hypotheses_of% Fx.rescale_down_trunc := by
  exact ⟨2, 0, by decide, -789, True.intro⟩
#verify_hypotheses rescale_truncation_full for Solidity.Language.FixedPoint.Fx.rescale_down_trunc
#print axioms rescale_truncation_full

theorem rescale_exact_full : hypotheses_of% Fx.rescale_down_exact := by
  exact ⟨2, 0, 300, (by intro _; decide), True.intro⟩
#verify_hypotheses rescale_exact_full for Solidity.Language.FixedPoint.Fx.rescale_down_exact
#print axioms rescale_exact_full

theorem rescale_composition_full : hypotheses_of% Fx.rescale_rescale_down := by
  exact ⟨3, 2, 0, by decide, by decide, -1789, True.intro⟩
#verify_hypotheses rescale_composition_full for Solidity.Language.FixedPoint.Fx.rescale_rescale_down
#print axioms rescale_composition_full

theorem rescale_order_full : hypotheses_of% Fx.rescale_mono := by
  exact ⟨2, 0, -789, 123, by decide, True.intro⟩
#verify_hypotheses rescale_order_full for Solidity.Language.FixedPoint.Fx.rescale_mono
#print axioms rescale_order_full

theorem rescale_roundtrip_full : hypotheses_of% Fx.rescale_up_down := by
  exact ⟨0, 2, by decide, -123, True.intro⟩
#verify_hypotheses rescale_roundtrip_full for Solidity.Language.FixedPoint.Fx.rescale_up_down
#print axioms rescale_roundtrip_full

/-- The product example drops nonzero fractional digits rather than dividing by one. -/
theorem product_truncation_branch : decimalTy.scale = 10 ∧ (7 * 2 : Int) % decimalTy.scale ≠ 0 := by
  decide
#print axioms product_truncation_branch

/-- Widening changes both bit width and decimal precision, not only a type name. -/
def widenedTy : FxTy := ⟨false, 16, 1, by decide⟩
def signedDecimalTy : FxTy := ⟨true, 8, 1, by decide⟩

theorem explicit_value_full : hypotheses_of% Fx.explicit_sameValue := by
  exact ⟨decimalTy, ty, ⟨30, by decide⟩, (by intro _; decide), by decide, True.intro⟩
#verify_hypotheses explicit_value_full for Solidity.Language.FixedPoint.Fx.explicit_sameValue
#print axioms explicit_value_full

theorem explicit_roundtrip_full : hypotheses_of% Fx.explicit_explicit := by
  exact ⟨decimalTy, ty, ⟨30, by decide⟩, (by intro _; decide), by decide, True.intro⟩
#verify_hypotheses explicit_roundtrip_full for Solidity.Language.FixedPoint.Fx.explicit_explicit
#print axioms explicit_roundtrip_full

theorem implicit_roundtrip_full : hypotheses_of% Fx.explicit_implicit := by
  exact ⟨ty, widenedTy, by decide, seven, True.intro⟩
#verify_hypotheses implicit_roundtrip_full for Solidity.Language.FixedPoint.Fx.explicit_implicit
#print axioms implicit_roundtrip_full

theorem integer_to_fixed_full : hypotheses_of% Fx.toIntTrunc_ofIntegerExplicit := by
  exact ⟨decimalTy, 7, by decide, True.intro⟩
#verify_hypotheses integer_to_fixed_full for Solidity.Language.FixedPoint.Fx.toIntTrunc_ofIntegerExplicit
#print axioms integer_to_fixed_full

theorem fixed_to_integer_full : hypotheses_of% Fx.ofIntegerExplicit_toIntTrunc := by
  exact ⟨decimalTy, ⟨70, by decide⟩, by decide, True.intro⟩
#verify_hypotheses fixed_to_integer_full for Solidity.Language.FixedPoint.Fx.ofIntegerExplicit_toIntTrunc
#print axioms fixed_to_integer_full

theorem integer_truncation_full : hypotheses_of% Fx.toIntTrunc_trunc := by
  exact ⟨signedDecimalTy, ⟨-17, by decide⟩, True.intro⟩
#verify_hypotheses integer_truncation_full for Solidity.Language.FixedPoint.Fx.toIntTrunc_trunc
#print axioms integer_truncation_full

theorem bits_to_value_full : hypotheses_of% Fx.toBits_ofBits := by
  exact ⟨signedTy, 249, by decide, by decide, True.intro⟩
#verify_hypotheses bits_to_value_full for Solidity.Language.FixedPoint.Fx.toBits_ofBits
#print axioms bits_to_value_full

theorem value_to_bits_full : hypotheses_of% Fx.ofBits_toBits := by
  exact ⟨signedTy, negativeSeven, True.intro⟩
#verify_hypotheses value_to_bits_full for Solidity.Language.FixedPoint.Fx.ofBits_toBits
#print axioms value_to_bits_full

theorem explicit_order_full : hypotheses_of% Fx.explicit_le := by
  exact ⟨decimalTy, ty, ⟨15, by decide⟩, ⟨25, by decide⟩, by decide, by decide, by decide, True.intro⟩
#verify_hypotheses explicit_order_full for Solidity.Language.FixedPoint.Fx.explicit_le
#print axioms explicit_order_full

theorem implicit_order_full : hypotheses_of% Fx.implicit_le := by
  exact ⟨ty, widenedTy, by decide, two, seven, True.intro⟩
#verify_hypotheses implicit_order_full for Solidity.Language.FixedPoint.Fx.implicit_le
#print axioms implicit_order_full

theorem implicit_injection_full : hypotheses_of% Fx.implicit_injective := by
  exact ⟨ty, widenedTy, by decide, seven, seven, rfl, True.intro⟩
#verify_hypotheses implicit_injection_full for Solidity.Language.FixedPoint.Fx.implicit_injective
#print axioms implicit_injection_full

theorem solc_conversion_full : hypotheses_of% FxTy.solcImplicit_of_subsumes := by
  exact ⟨ty, widenedTy, by decide, True.intro⟩
#verify_hypotheses solc_conversion_full for Solidity.Language.FixedPoint.FxTy.solcImplicit_of_subsumes
#print axioms solc_conversion_full

theorem implicit_test_full : hypotheses_of% FxTy.implicitOK_iff := by
  exact ⟨ty, widenedTy, True.intro⟩
#verify_hypotheses implicit_test_full for Solidity.Language.FixedPoint.FxTy.implicitOK_iff
#print axioms implicit_test_full

theorem lower_endpoint_full : hypotheses_of% FxTy.lo_inRange := by
  exact ⟨signedTy, True.intro⟩
#verify_hypotheses lower_endpoint_full for Solidity.Language.FixedPoint.FxTy.lo_inRange
#print axioms lower_endpoint_full

theorem upper_endpoint_full : hypotheses_of% FxTy.hi_inRange := by
  exact ⟨decimalTy, True.intro⟩
#verify_hypotheses upper_endpoint_full for Solidity.Language.FixedPoint.FxTy.hi_inRange
#print axioms upper_endpoint_full

theorem range_containment_full : hypotheses_of% FxTy.subsumes_iff := by
  exact ⟨ty, widenedTy, True.intro⟩
#verify_hypotheses range_containment_full for Solidity.Language.FixedPoint.FxTy.subsumes_iff
#print axioms range_containment_full

theorem reflexive_conversion_full : hypotheses_of% FxTy.subsumes_refl := by
  exact ⟨ty, True.intro⟩
#verify_hypotheses reflexive_conversion_full for Solidity.Language.FixedPoint.FxTy.subsumes_refl
#print axioms reflexive_conversion_full

theorem common_type_subsumes_full : hypotheses_of% FxTy.common?_subsumes := by
  exact ⟨ty, widenedTy, widenedTy, by decide, True.intro⟩
#verify_hypotheses common_type_subsumes_full for Solidity.Language.FixedPoint.FxTy.common?_subsumes
#print axioms common_type_subsumes_full

theorem implicit_preservation_full : hypotheses_of% Fx.implicit_preserves := by
  exact ⟨ty, widenedTy, by decide, two, seven, True.intro⟩
#verify_hypotheses implicit_preservation_full for Solidity.Language.FixedPoint.Fx.implicit_preserves
#print axioms implicit_preservation_full

theorem common_type_preservation_full : hypotheses_of% Fx.common?_preserves := by
  exact ⟨ty, widenedTy, widenedTy, by decide, seven, ⟨20, by decide⟩, True.intro⟩
#verify_hypotheses common_type_preservation_full for Solidity.Language.FixedPoint.Fx.common?_preserves
#print axioms common_type_preservation_full

theorem addition_associativity_full : hypotheses_of% Fx.add_assoc := by
  exact ⟨ty, ⟨1, by decide⟩, two, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, rfl, rfl, rfl, rfl, True.intro⟩
#verify_hypotheses addition_associativity_full for Solidity.Language.FixedPoint.Fx.add_assoc
#print axioms addition_associativity_full

/-- The selected implicit conversion exercises genuine width and scale growth. -/
theorem widening_branch : ty.bits < widenedTy.bits ∧ ty.digits < widenedTy.digits ∧ ty.subsumes widenedTy = true := by
  decide
#print axioms widening_branch
end Solidity.H62.AuditLanguage.FixedPointLawWitness
