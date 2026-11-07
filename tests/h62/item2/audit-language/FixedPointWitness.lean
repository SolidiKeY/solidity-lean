import Lean
import Solidity.Language.FixedPoint

/-! Complete imported hypothesis tuples for each fixed-point statement with
leading arguments. Concrete overflow and nonzero-divisor cases retain all
range constraints. These are reference-semantics feasibility certificates,
not source/compiler totality or solc code generation claims. -/
open Lean Meta Elab Term

private partial def fixedTelescopeExists (type : Expr) : MetaM Expr := do
  match type with
  | .forallE name domain body info =>
    withLocalDecl name info domain fun x => do
      let rest ← fixedTelescopeExists (body.instantiate1 x)
      mkAppM ``Exists #[← mkLambdaFVars #[x] rest]
  | _ => pure (mkConst ``True)

elab "fixed_hypotheses_of% " target:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo target
  let info ← getConstInfo name
  unless info.levelParams.isEmpty do
    throwError "universe-polymorphic target needs explicit level handling"
  fixedTelescopeExists info.type

elab "#verify_fixed_hypotheses " witness:ident " for " target:ident : command => do
  Lean.Elab.Command.liftTermElabM do
    let witnessName ← realizeGlobalConstNoOverloadWithInfo witness
    let targetName ← realizeGlobalConstNoOverloadWithInfo target
    let wi ← getConstInfo witnessName
    let ti ← getConstInfo targetName
    unless ti.levelParams.isEmpty && wi.levelParams.isEmpty do
      throwError "universe-polymorphic association requires explicit handling"
    unless (← isDefEq wi.type (← fixedTelescopeExists ti.type)) do
      throwError "hypothesis telescope mismatch"
    logInfo m!"H62_WITNESS {witnessName} FOR {targetName}"

namespace Solidity.H62.AuditLanguage.FixedWitness
open Solidity.Language.FixedPoint

def ty : FxTy := ⟨false, 8, 0, by decide⟩
def zero : Fx ty := ⟨0, by decide⟩
def one : Fx ty := ⟨1, by decide⟩
def top : Fx ty := ⟨255, by decide⟩

theorem FxTy_bits_ge_full : fixed_hypotheses_of% FxTy.bits_ge := by
  exact ⟨ty, True.intro⟩

#print axioms FxTy_bits_ge_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.FxTy_bits_ge_full for Solidity.Language.FixedPoint.FxTy.bits_ge

theorem FxTy_bits_le_full : fixed_hypotheses_of% FxTy.bits_le := by
  exact ⟨ty, True.intro⟩

#print axioms FxTy_bits_le_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.FxTy_bits_le_full for Solidity.Language.FixedPoint.FxTy.bits_le

theorem FxTy_scale_pos_full : fixed_hypotheses_of% FxTy.scale_pos := by
  exact ⟨ty, True.intro⟩

#print axioms FxTy_scale_pos_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.FxTy_scale_pos_full for Solidity.Language.FixedPoint.FxTy.scale_pos

theorem FxTy_pow_bits_full : fixed_hypotheses_of% FxTy.pow_bits := by
  exact ⟨ty, True.intro⟩

#print axioms FxTy_pow_bits_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.FxTy_pow_bits_full for Solidity.Language.FixedPoint.FxTy.pow_bits

theorem FxTy_half_pos_full : fixed_hypotheses_of% FxTy.half_pos := by
  exact ⟨ty, True.intro⟩

#print axioms FxTy_half_pos_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.FxTy_half_pos_full for Solidity.Language.FixedPoint.FxTy.half_pos

theorem FxTy_lo_le_zero_full : fixed_hypotheses_of% FxTy.lo_le_zero := by
  exact ⟨ty, True.intro⟩

#print axioms FxTy_lo_le_zero_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.FxTy_lo_le_zero_full for Solidity.Language.FixedPoint.FxTy.lo_le_zero

theorem FxTy_hi_nonneg_full : fixed_hypotheses_of% FxTy.hi_nonneg := by
  exact ⟨ty, True.intro⟩

#print axioms FxTy_hi_nonneg_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.FxTy_hi_nonneg_full for Solidity.Language.FixedPoint.FxTy.hi_nonneg

theorem Fx_wrapInt_inRange_full : fixed_hypotheses_of% Fx.wrapInt_inRange := by
  exact ⟨ty, 0, True.intro⟩

#print axioms Fx_wrapInt_inRange_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_wrapInt_inRange_full for Solidity.Language.FixedPoint.Fx.wrapInt_inRange

theorem Fx_wrapInt_of_inRange_full : fixed_hypotheses_of% Fx.wrapInt_of_inRange := by
  exact ⟨ty, 0, by decide, True.intro⟩

#print axioms Fx_wrapInt_of_inRange_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_wrapInt_of_inRange_full for Solidity.Language.FixedPoint.Fx.wrapInt_of_inRange

theorem Fx_wrapInt_emod_full : fixed_hypotheses_of% Fx.wrapInt_emod := by
  exact ⟨ty, 0, True.intro⟩

#print axioms Fx_wrapInt_emod_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_wrapInt_emod_full for Solidity.Language.FixedPoint.Fx.wrapInt_emod

theorem Fx_result_of_inRange_full : fixed_hypotheses_of% Fx.result_of_inRange := by
  exact ⟨ty, .checked, 0, by decide, True.intro⟩

#print axioms Fx_result_of_inRange_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_result_of_inRange_full for Solidity.Language.FixedPoint.Fx.result_of_inRange

theorem Fx_result_checked_overflow_full : fixed_hypotheses_of% Fx.result_checked_overflow := by
  exact ⟨ty, 256, by decide, True.intro⟩

#print axioms Fx_result_checked_overflow_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_result_checked_overflow_full for Solidity.Language.FixedPoint.Fx.result_checked_overflow

theorem Fx_add_eq_full : fixed_hypotheses_of% Fx.add_eq := by
  exact ⟨ty, .checked, zero, one, by decide, True.intro⟩

#print axioms Fx_add_eq_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_add_eq_full for Solidity.Language.FixedPoint.Fx.add_eq

theorem Fx_add_overflow_full : fixed_hypotheses_of% Fx.add_overflow := by
  exact ⟨ty, top, one, by decide, True.intro⟩

#print axioms Fx_add_overflow_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_add_overflow_full for Solidity.Language.FixedPoint.Fx.add_overflow

theorem Fx_add_unchecked_full : fixed_hypotheses_of% Fx.add_unchecked := by
  exact ⟨ty, top, one, True.intro⟩

#print axioms Fx_add_unchecked_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_add_unchecked_full for Solidity.Language.FixedPoint.Fx.add_unchecked

theorem Fx_add_comm_full : fixed_hypotheses_of% Fx.add_comm := by
  exact ⟨ty, .checked, zero, one, True.intro⟩

#print axioms Fx_add_comm_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_add_comm_full for Solidity.Language.FixedPoint.Fx.add_comm

theorem Fx_mul_comm_full : fixed_hypotheses_of% Fx.mul_comm := by
  exact ⟨ty, .checked, zero, one, True.intro⟩

#print axioms Fx_mul_comm_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_mul_comm_full for Solidity.Language.FixedPoint.Fx.mul_comm

theorem Fx_sub_eq_full : fixed_hypotheses_of% Fx.sub_eq := by
  exact ⟨ty, .checked, one, zero, by decide, True.intro⟩

#print axioms Fx_sub_eq_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_sub_eq_full for Solidity.Language.FixedPoint.Fx.sub_eq

theorem Fx_add_zero_full : fixed_hypotheses_of% Fx.add_zero := by
  exact ⟨ty, .checked, one, True.intro⟩

#print axioms Fx_add_zero_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_add_zero_full for Solidity.Language.FixedPoint.Fx.add_zero

theorem Fx_mul_one_full : fixed_hypotheses_of% Fx.mul_one := by
  exact ⟨ty, .checked, one, by decide, True.intro⟩

#print axioms Fx_mul_one_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_mul_one_full for Solidity.Language.FixedPoint.Fx.mul_one

theorem Fx_div_zero_full : fixed_hypotheses_of% Fx.div_zero := by
  exact ⟨ty, .checked, one, True.intro⟩

#print axioms Fx_div_zero_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_div_zero_full for Solidity.Language.FixedPoint.Fx.div_zero

theorem Fx_mod_zero_full : fixed_hypotheses_of% Fx.mod_zero := by
  exact ⟨ty, .checked, one, True.intro⟩

#print axioms Fx_mod_zero_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_mod_zero_full for Solidity.Language.FixedPoint.Fx.mod_zero

theorem Fx_tmod_between_full : fixed_hypotheses_of% Fx.tmod_between := by
  exact ⟨0, 1, True.intro⟩

#print axioms Fx_tmod_between_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_tmod_between_full for Solidity.Language.FixedPoint.Fx.tmod_between

theorem Fx_mod_inRange_full : fixed_hypotheses_of% Fx.mod_inRange := by
  exact ⟨ty, one, one, True.intro⟩

#print axioms Fx_mod_inRange_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_mod_inRange_full for Solidity.Language.FixedPoint.Fx.mod_inRange

theorem Fx_mod_eq_full : fixed_hypotheses_of% Fx.mod_eq := by
  exact ⟨ty, .checked, one, one, by decide, True.intro⟩

#print axioms Fx_mod_eq_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_mod_eq_full for Solidity.Language.FixedPoint.Fx.mod_eq

theorem Fx_div_eq_full : fixed_hypotheses_of% Fx.div_eq := by
  exact ⟨ty, .checked, one, one, by decide, by decide, True.intro⟩

#print axioms Fx_div_eq_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_div_eq_full for Solidity.Language.FixedPoint.Fx.div_eq

theorem Fx_lt_iff_full : fixed_hypotheses_of% Fx.lt_iff := by
  exact ⟨ty, zero, one, True.intro⟩

#print axioms Fx_lt_iff_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_lt_iff_full for Solidity.Language.FixedPoint.Fx.lt_iff

theorem Fx_inRange_mul_of_subsumes_full : fixed_hypotheses_of% Fx.inRange_mul_of_subsumes := by
  exact ⟨ty, ty, by decide, one, True.intro⟩

#print axioms Fx_inRange_mul_of_subsumes_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_inRange_mul_of_subsumes_full for Solidity.Language.FixedPoint.Fx.inRange_mul_of_subsumes

theorem Fx_implicit_sameValue_full : fixed_hypotheses_of% Fx.implicit_sameValue := by
  exact ⟨ty, ty, by decide, one, True.intro⟩

#print axioms Fx_implicit_sameValue_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_implicit_sameValue_full for Solidity.Language.FixedPoint.Fx.implicit_sameValue

theorem Fx_implicit_lt_full : fixed_hypotheses_of% Fx.implicit_lt := by
  exact ⟨ty, ty, by decide, zero, one, True.intro⟩

#print axioms Fx_implicit_lt_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_implicit_lt_full for Solidity.Language.FixedPoint.Fx.implicit_lt

theorem Fx_explicit_of_subsumes_full : fixed_hypotheses_of% Fx.explicit_of_subsumes := by
  exact ⟨ty, ty, by decide, one, True.intro⟩

#print axioms Fx_explicit_of_subsumes_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_explicit_of_subsumes_full for Solidity.Language.FixedPoint.Fx.explicit_of_subsumes

theorem Fx_ofInteger_inRange_full : fixed_hypotheses_of% Fx.ofInteger_inRange := by
  exact ⟨ty, 0, 1, 1, by decide, ⟨by decide, by decide⟩, True.intro⟩

#print axioms Fx_ofInteger_inRange_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_ofInteger_inRange_full for Solidity.Language.FixedPoint.Fx.ofInteger_inRange

theorem Fx_ofIntegerExplicit_of_implicit_full : fixed_hypotheses_of% Fx.ofIntegerExplicit_of_implicit := by
  exact ⟨ty, 0, 1, 1, by decide, ⟨by decide, by decide⟩, True.intro⟩

#print axioms Fx_ofIntegerExplicit_of_implicit_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_ofIntegerExplicit_of_implicit_full for Solidity.Language.FixedPoint.Fx.ofIntegerExplicit_of_implicit

theorem Fx_pow_bits_le_full : fixed_hypotheses_of% Fx.pow_bits_le := by
  exact ⟨ty, True.intro⟩

#print axioms Fx_pow_bits_le_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_pow_bits_le_full for Solidity.Language.FixedPoint.Fx.pow_bits_le

theorem Fx_toWord_range_full : fixed_hypotheses_of% Fx.toWord_range := by
  exact ⟨ty, one, True.intro⟩

#print axioms Fx_toWord_range_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_toWord_range_full for Solidity.Language.FixedPoint.Fx.toWord_range

theorem Fx_ofWord_toWord_full : fixed_hypotheses_of% Fx.ofWord_toWord := by
  exact ⟨ty, one, True.intro⟩

#print axioms Fx_ofWord_toWord_full
#verify_fixed_hypotheses Solidity.H62.AuditLanguage.FixedWitness.Fx_ofWord_toWord_full for Solidity.Language.FixedPoint.Fx.ofWord_toWord

/-- error: hypothesis telescope mismatch -/
#guard_msgs in
#verify_fixed_hypotheses Fx_div_zero_full for Solidity.Language.FixedPoint.Fx.div_eq
end Solidity.H62.AuditLanguage.FixedWitness
