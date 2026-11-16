import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Language.FixedPoint.Literals

/-!
Guarded regression: a nonzero denominator alone must not be credited as a full
literal-conversion tuple, or implicit exactness conflated with explicit
truncation. Joint witnesses retain every spelling-equality, range and conversion
success premise. Equivalent fractions and negative truncation are exercised;
1/3 at one decimal digit distinguishes the two conversions. These are selected
reference-semantics interfaces, not compiler code generation. Standalone ABI
constants retain the reference extension beyond pinned solc acceptance. Historical
ownership replay remains unverifiable.
-/
set_option autoImplicit false

namespace Solidity.H62.AuditLanguage.FixedPointLiteralWitness
open Solidity.Language.FixedPoint

def ty : FxTy := ⟨false, 8, 1, by decide⟩
def signedTy : FxTy := ⟨true, 8, 1, by decide⟩

theorem implicit_exact_full : hypotheses_of% Fx.ofLiteral?_eq_some_iff := by
  exact ⟨ty, 3, 2, by decide, ⟨15, by decide⟩, True.intro⟩
#verify_hypotheses implicit_exact_full for Solidity.Language.FixedPoint.Fx.ofLiteral?_eq_some_iff
#print axioms implicit_exact_full

theorem implicit_spelling_full : hypotheses_of% Fx.ofLiteral?_congr := by
  exact ⟨ty, 3, 6, 2, 4, by decide, by decide, by decide, True.intro⟩
#verify_hypotheses implicit_spelling_full for Solidity.Language.FixedPoint.Fx.ofLiteral?_congr
#print axioms implicit_spelling_full

theorem truncation_spelling_full : hypotheses_of% Fx.literalTrunc_congr := by
  exact ⟨signedTy, -1, -2, 3, 6, by decide, by decide, by decide, True.intro⟩
#verify_hypotheses truncation_spelling_full for Solidity.Language.FixedPoint.Fx.literalTrunc_congr
#print axioms truncation_spelling_full

theorem rational_spelling_full : hypotheses_of% Fx.ofRat?_mkRat := by
  exact ⟨ty, 3, 2, by decide, True.intro⟩
#verify_hypotheses rational_spelling_full for Solidity.Language.FixedPoint.Fx.ofRat?_mkRat
#print axioms rational_spelling_full

theorem rational_exact_full : hypotheses_of% Fx.ofRat?_eq_some_iff := by
  exact ⟨ty, mkRat 3 2, ⟨15, by decide⟩, True.intro⟩
#verify_hypotheses rational_exact_full for Solidity.Language.FixedPoint.Fx.ofRat?_eq_some_iff
#print axioms rational_exact_full

theorem explicit_value_full : hypotheses_of% Fx.explicitConst?_eq_some_iff := by
  exact ⟨signedTy, -1, 3, by decide, ⟨-3, by decide⟩, True.intro⟩
#verify_hypotheses explicit_value_full for Solidity.Language.FixedPoint.Fx.explicitConst?_eq_some_iff
#print axioms explicit_value_full

theorem explicit_rejection_full : hypotheses_of% Fx.explicitConst?_eq_none_iff := by
  exact ⟨ty, 100, 1, by decide, True.intro⟩
#verify_hypotheses explicit_rejection_full for Solidity.Language.FixedPoint.Fx.explicitConst?_eq_none_iff
#print axioms explicit_rejection_full

theorem implicit_to_explicit_full : hypotheses_of% Fx.explicitConst?_of_ofLiteral? := by
  exact ⟨ty, 3, 2, by decide, ⟨15, by decide⟩, rfl, True.intro⟩
#verify_hypotheses implicit_to_explicit_full for Solidity.Language.FixedPoint.Fx.explicitConst?_of_ofLiteral?
#print axioms implicit_to_explicit_full

theorem negative_truncation_full : hypotheses_of% Fx.explicitConst?_trunc := by
  exact ⟨signedTy, -1, 3, by decide, ⟨-3, by decide⟩, rfl, True.intro⟩
#verify_hypotheses negative_truncation_full for Solidity.Language.FixedPoint.Fx.explicitConst?_trunc
#print axioms negative_truncation_full

theorem explicit_rational_full : hypotheses_of% Fx.explicitRat?_mkRat := by
  exact ⟨ty, 3, 2, by decide, True.intro⟩
#verify_hypotheses explicit_rational_full for Solidity.Language.FixedPoint.Fx.explicitRat?_mkRat
#print axioms explicit_rational_full

theorem solc_literal_test_full : hypotheses_of% Fx.ofLiteral?_isSome_iff_solc := by
  exact ⟨ty, 3, 2, by decide, True.intro⟩
#verify_hypotheses solc_literal_test_full for Solidity.Language.FixedPoint.Fx.ofLiteral?_isSome_iff_solc
#print axioms solc_literal_test_full

/-- A nonterminating decimal is implicitly refused but explicitly truncated. -/
theorem conversion_boundary : Fx.ofLiteral? ty 1 3 = none ∧
    Fx.explicitConst? ty 1 3 = some (⟨3, by decide⟩ : Fx ty) ∧
    Fx.ofLiteral? signedTy (-3) 2 = some (⟨-15, by decide⟩ : Fx signedTy) := by
  decide
#print axioms conversion_boundary

def ratio : Rat := mkRat 3 2
def tooLarge : Rat := mkRat ((2 ^ 256 : Nat) : Int) 1
def wholeTy : FxTy := ⟨false, 8, 0, by decide⟩

/-- A concrete successful mobile type; reused instead of assumed at each tuple. -/
theorem mobile_success : Fx.mobileFx? ratio = some ty := by
  decide

/-- A magnitude already beyond the bound cannot become admissible by scaling. -/
theorem no_mobile_of_magnitude (q : Rat)
    (h : Fx.maxMag q * q.den < q.num.natAbs) : Fx.mobileFx? q = none := by
  have hp : 0 < 10 ^ Fx.mobDigits q := Nat.pow_pos (by decide)
  have hm : q.num.natAbs ≤ q.num.natAbs * 10 ^ Fx.mobDigits q :=
    Nat.le_mul_of_pos_right _ hp
  have bad : ¬ q.num.natAbs * 10 ^ Fx.mobDigits q ≤ Fx.maxMag q * q.den := by
    omega
  unfold Fx.mobileFx?
  rw [if_neg bad]

/-- A magnitude beyond the unsigned 256-bit maximum has no mobile type. -/
theorem no_mobile_type : Fx.mobileFx? tooLarge = none := by
  apply no_mobile_of_magnitude
  decide

theorem digit_loop_bound_full : hypotheses_of% Fx.digitsGo_le := by
  exact ⟨3, 2, 255, 8, 0, True.intro⟩
#verify_hypotheses digit_loop_bound_full for Solidity.Language.FixedPoint.Fx.digitsGo_le
#print axioms digit_loop_bound_full

theorem byte_width_bound_full : hypotheses_of% Fx.byteLen_spec := by
  exact ⟨2, 4660, by decide, True.intro⟩
#verify_hypotheses byte_width_bound_full for Solidity.Language.FixedPoint.Fx.byteLen_spec
#print axioms byte_width_bound_full

theorem mobile_digit_bound_full : hypotheses_of% Fx.mobDigits_le := by
  exact ⟨ratio, True.intro⟩
#verify_hypotheses mobile_digit_bound_full for Solidity.Language.FixedPoint.Fx.mobDigits_le
#print axioms mobile_digit_bound_full

theorem mobile_width_bound_full : hypotheses_of% Fx.mobBytes_le := by
  exact ⟨ratio, by decide, True.intro⟩
#verify_hypotheses mobile_width_bound_full for Solidity.Language.FixedPoint.Fx.mobBytes_le
#print axioms mobile_width_bound_full

theorem mobile_spec_full : hypotheses_of% Fx.mobileFx?_spec := by
  exact ⟨ratio, ty, mobile_success, True.intro⟩
#verify_hypotheses mobile_spec_full for Solidity.Language.FixedPoint.Fx.mobileFx?_spec
#print axioms mobile_spec_full

theorem mobile_truncation_full : hypotheses_of% Fx.literalTrunc_mob := by
  exact ⟨ratio, ty, by decide, True.intro⟩
#verify_hypotheses mobile_truncation_full for Solidity.Language.FixedPoint.Fx.literalTrunc_mob
#print axioms mobile_truncation_full

theorem mobile_range_full : hypotheses_of% Fx.mobileFx?_inRange := by
  exact ⟨ratio, ty, mobile_success, True.intro⟩
#verify_hypotheses mobile_range_full for Solidity.Language.FixedPoint.Fx.mobileFx?_inRange
#print axioms mobile_range_full

theorem mobile_exact_full : hypotheses_of% Fx.mobileFx?_exact := by
  exact ⟨ratio, ty, mobile_success, True.intro⟩
#verify_hypotheses mobile_exact_full for Solidity.Language.FixedPoint.Fx.mobileFx?_exact
#print axioms mobile_exact_full

theorem loop_exact_bound_full : hypotheses_of% Fx.digitsGo_le_of_exact := by
  exact ⟨3, 2, 255, 1, by decide, 8, 0, by decide, True.intro⟩
#verify_hypotheses loop_exact_bound_full for Solidity.Language.FixedPoint.Fx.digitsGo_le_of_exact
#print axioms loop_exact_bound_full

theorem loop_exact_full : hypotheses_of% Fx.digitsGo_exact := by
  exact ⟨3, 2, 255, 1, by decide, by decide, 8, 0, by decide, by decide, True.intro⟩
#verify_hypotheses loop_exact_full for Solidity.Language.FixedPoint.Fx.digitsGo_exact
#print axioms loop_exact_full

theorem mobile_exact_digits_full : hypotheses_of% Fx.mobileFx?_exact_of_digits := by
  exact ⟨ratio, ty, mobile_success, 1, by decide, by decide, by decide, True.intro⟩
#verify_hypotheses mobile_exact_digits_full for Solidity.Language.FixedPoint.Fx.mobileFx?_exact_of_digits
#print axioms mobile_exact_digits_full

theorem literal_rescale_full : hypotheses_of% Fx.literalTrunc_rescale := by
  exact ⟨wholeTy, ty, 3, 2, by decide, by decide, True.intro⟩
#verify_hypotheses literal_rescale_full for Solidity.Language.FixedPoint.Fx.literalTrunc_rescale
#print axioms literal_rescale_full

theorem mobile_route_full : hypotheses_of% Fx.explicit_mobile_route := by
  exact ⟨ratio, ty, wholeTy, mobile_success, by decide, True.intro⟩
#verify_hypotheses mobile_route_full for Solidity.Language.FixedPoint.Fx.explicit_mobile_route
#print axioms mobile_route_full

theorem mobile_fold_route_full : hypotheses_of% Fx.explicitRat?_mobile_route := by
  exact ⟨ratio, ty, wholeTy, mobile_success, by decide, ⟨1, by decide⟩, rfl, True.intro⟩
#verify_hypotheses mobile_fold_route_full for Solidity.Language.FixedPoint.Fx.explicitRat?_mobile_route
#print axioms mobile_fold_route_full

theorem common_solc_full : hypotheses_of% Fx.litCommon?_solc := by
  exact ⟨ty, ty, ratio, rfl, True.intro⟩
#verify_hypotheses common_solc_full for Solidity.Language.FixedPoint.Fx.litCommon?_solc
#print axioms common_solc_full

theorem reverse_common_solc_full : hypotheses_of% Fx.litCommonRev?_eq_solc := by
  exact ⟨ratio, ty, True.intro⟩
#verify_hypotheses reverse_common_solc_full for Solidity.Language.FixedPoint.Fx.litCommonRev?_eq_solc
#print axioms reverse_common_solc_full

theorem common_exact_full : hypotheses_of% Fx.litCommon?_exact := by
  exact ⟨ty, ty, ratio, rfl, True.intro⟩
#verify_hypotheses common_exact_full for Solidity.Language.FixedPoint.Fx.litCommon?_exact
#print axioms common_exact_full

theorem reverse_common_exact_full : hypotheses_of% Fx.litCommonRev?_exact := by
  exact ⟨ty, ty, mkRat 2 1, rfl, True.intro⟩
#verify_hypotheses reverse_common_exact_full for Solidity.Language.FixedPoint.Fx.litCommonRev?_exact
#print axioms reverse_common_exact_full

theorem standalone_value_full : hypotheses_of% Fx.mobileConst?_eq := by
  exact ⟨ratio, ty, mobile_success, True.intro⟩
#verify_hypotheses standalone_value_full for Solidity.Language.FixedPoint.Fx.mobileConst?_eq
#print axioms standalone_value_full

theorem standalone_refusal_full : hypotheses_of% Fx.mobileConst?_eq_none := by
  exact ⟨tooLarge, no_mobile_type, True.intro⟩
#verify_hypotheses standalone_refusal_full for Solidity.Language.FixedPoint.Fx.mobileConst?_eq_none
#print axioms standalone_refusal_full

theorem standalone_explicit_full : hypotheses_of% Fx.mobileConst?_explicit := by
  exact ⟨ratio, ty, mobile_success, True.intro⟩
#verify_hypotheses standalone_explicit_full for Solidity.Language.FixedPoint.Fx.mobileConst?_explicit
#print axioms standalone_explicit_full

theorem standalone_truncation_full : hypotheses_of% Fx.mobileConst?_trunc := by
  exact ⟨ratio, ty, mobile_success, True.intro⟩
#verify_hypotheses standalone_truncation_full for Solidity.Language.FixedPoint.Fx.mobileConst?_trunc
#print axioms standalone_truncation_full

theorem standalone_exact_full : hypotheses_of% Fx.mobileConst?_exact := by
  exact ⟨ratio, ty, mobile_success, ⟨15, by decide⟩, rfl, True.intro⟩
#verify_hypotheses standalone_exact_full for Solidity.Language.FixedPoint.Fx.mobileConst?_exact
#print axioms standalone_exact_full

theorem abi_constant_full : hypotheses_of% Fx.abiConst?_eq := by
  exact ⟨ratio, ty, mobile_success, True.intro⟩
#verify_hypotheses abi_constant_full for Solidity.Language.FixedPoint.Fx.abiConst?_eq
#print axioms abi_constant_full

theorem abi_constant_decode_full : hypotheses_of% Fx.abiConst?_decode := by
  exact ⟨ratio, ty, mobile_success, True.intro⟩
#verify_hypotheses abi_constant_decode_full for Solidity.Language.FixedPoint.Fx.abiConst?_decode
#print axioms abi_constant_decode_full

theorem abi_constant_refusal_full : hypotheses_of% Fx.abiConst?_eq_none := by
  exact ⟨tooLarge, no_mobile_type, True.intro⟩
#verify_hypotheses abi_constant_refusal_full for Solidity.Language.FixedPoint.Fx.abiConst?_eq_none
#print axioms abi_constant_refusal_full

/-- Precision and operand order both matter for mobile literal admission. -/
theorem mobile_boundary : Fx.mobDigits ratio = 1 ∧ Fx.litCommonRev? ratio ty = none := by
  decide
#print axioms mobile_success
#print axioms no_mobile_of_magnitude
#print axioms no_mobile_type
#print axioms mobile_boundary
end Solidity.H62.AuditLanguage.FixedPointLiteralWitness
