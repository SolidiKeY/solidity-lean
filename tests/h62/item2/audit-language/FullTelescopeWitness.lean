import Lean
import Solidity.Language.FeatureInfo
import Solidity.KeySort
import Solidity.Syntax.CheckedExact

/-! Kernel-checked feasibility of the entire leading telescope of each named
frozen theorem. The type is computed from the imported constant, so dropping
an argument or a dependent hypothesis makes the witness fail to elaborate.
This elaboration helper neither proves the original conclusions nor changes
their types. Only the explicitly listed statements receive certificates. -/
open Lean Meta Elab Term

private partial def telescopeExists (type : Expr) : MetaM Expr := do
  match type with
  | .forallE name domain body info =>
    withLocalDecl name info domain fun x => do
      let rest ← telescopeExists (body.instantiate1 x)
      mkAppM ``Exists #[← mkLambdaFVars #[x] rest]
  | _ => pure (mkConst ``True)

elab "hypotheses_of% " target:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo target
  let info ← getConstInfo name
  unless info.levelParams.isEmpty do
    throwError "universe-polymorphic target needs explicit level handling"
  telescopeExists info.type

elab "#verify_hypotheses " witness:ident " for " target:ident : command => do
  Lean.Elab.Command.liftTermElabM do
    let witnessName ← realizeGlobalConstNoOverloadWithInfo witness
    let targetName ← realizeGlobalConstNoOverloadWithInfo target
    let wi ← getConstInfo witnessName
    let ti ← getConstInfo targetName
    unless ti.levelParams.isEmpty && wi.levelParams.isEmpty do
      throwError "universe-polymorphic association requires explicit handling"
    unless (← isDefEq wi.type (← telescopeExists ti.type)) do
      throwError "hypothesis telescope mismatch"
    logInfo m!"H62_WITNESS {witnessName} FOR {targetName}"

namespace Solidity.H62.AuditLanguage

theorem feature_exclusion_full : hypotheses_of% Language.Feature.exclusion_complete := by
  exact ⟨.txOrigin, rfl, True.intro⟩

theorem diagnostic_full : hypotheses_of% Language.Unmodelled.excluded := by
  exact ⟨.txOrigin, True.intro⟩

theorem sort_name_full : hypotheses_of% KeySort.ofName_name := by
  exact ⟨.bool, rfl, True.intro⟩

theorem sort_trans_full : hypotheses_of% KeySort.le_trans := by
  exact ⟨.bool, .prim, .any, rfl, rfl, True.intro⟩

theorem emod_full : hypotheses_of% Checked.emod_of_ge := by
  exact ⟨130, 128, by decide, by decide, True.intro⟩

theorem add_uint_full : hypotheses_of% Checked.add_uint_exact := by
  exact ⟨256, 250, 7, by decide, by decide, by decide, by decide, True.intro⟩

theorem mul_uint_full : hypotheses_of% Checked.mul_uint_exact := by
  exact ⟨256, 17, 16, by decide, by decide, by decide, by decide, True.intro⟩

theorem add_int_full : hypotheses_of% Checked.add_int_exact := by
  exact ⟨128, 127, 1, ⟨by decide, by decide⟩, True.intro⟩

theorem sub_int_full : hypotheses_of% Checked.sub_int_exact := by
  exact ⟨128, -128, 1, ⟨by decide, by decide⟩, True.intro⟩

theorem neg_int_full : hypotheses_of% Checked.neg_int_exact := by
  exact ⟨128, -128, ⟨by decide, by decide⟩, True.intro⟩

theorem div_int_full : hypotheses_of% Checked.div_int_exact := by
  exact ⟨128, -128, -1, by decide, ⟨by decide, by decide⟩, by decide, True.intro⟩

theorem mul_int_full : hypotheses_of% Checked.mul_int_exact := by
  exact ⟨128, -128, -1, by decide, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, True.intro⟩

#print axioms feature_exclusion_full
#print axioms diagnostic_full
#print axioms sort_name_full
#print axioms sort_trans_full
#print axioms emod_full
#print axioms add_uint_full
#print axioms mul_uint_full
#print axioms add_int_full
#print axioms sub_int_full
#print axioms neg_int_full
#print axioms div_int_full
#print axioms mul_int_full
#verify_hypotheses Solidity.H62.AuditLanguage.feature_exclusion_full for Solidity.Language.Feature.exclusion_complete
#verify_hypotheses Solidity.H62.AuditLanguage.diagnostic_full for Solidity.Language.Unmodelled.excluded
#verify_hypotheses Solidity.H62.AuditLanguage.sort_name_full for Solidity.KeySort.ofName_name
#verify_hypotheses Solidity.H62.AuditLanguage.sort_trans_full for Solidity.KeySort.le_trans
#verify_hypotheses Solidity.H62.AuditLanguage.emod_full for Solidity.Checked.emod_of_ge
#verify_hypotheses Solidity.H62.AuditLanguage.add_uint_full for Solidity.Checked.add_uint_exact
#verify_hypotheses Solidity.H62.AuditLanguage.mul_uint_full for Solidity.Checked.mul_uint_exact
#verify_hypotheses Solidity.H62.AuditLanguage.add_int_full for Solidity.Checked.add_int_exact
#verify_hypotheses Solidity.H62.AuditLanguage.sub_int_full for Solidity.Checked.sub_int_exact
#verify_hypotheses Solidity.H62.AuditLanguage.neg_int_full for Solidity.Checked.neg_int_exact
#verify_hypotheses Solidity.H62.AuditLanguage.div_int_full for Solidity.Checked.div_int_exact
#verify_hypotheses Solidity.H62.AuditLanguage.mul_int_full for Solidity.Checked.mul_int_exact

/-- error: hypothesis telescope mismatch -/
#guard_msgs in
#verify_hypotheses feature_exclusion_full for KeySort.le_trans
end Solidity.H62.AuditLanguage
