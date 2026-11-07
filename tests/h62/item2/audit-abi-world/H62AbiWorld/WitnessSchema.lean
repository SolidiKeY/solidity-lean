import Lean

/-! Audit tooling only. Derive a simultaneous existential package from EVERY
binder of the unchanged theorem's elaborated type. Even proof binders are
existentially quantified, so the package cannot discard contradictory premises.
The original conclusion is deliberately replaced by True: this checks premise
feasibility, independently of the original theorem's proof or conclusion.
No core module imports this tooling. -/
open Lean Meta Elab Term

private def packageBinders (type : Expr) : MetaM Expr :=
  forallTelescope type fun binders _ => do
    let mut result := Lean.mkConst ``True
    for binder in binders.reverse do
      result ← mkAppM ``Exists #[← mkLambdaFVars #[binder] result]
    return result

elab "hypotheses% " theoremName:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo theoremName
  let type ← inferType (← mkConstWithFreshMVarLevels name)
  packageBinders type

namespace H62.AbiWorld.SchemaControls
private theorem dependent (n : Nat) (positive : 0 < n) (bounded : n < 3) : n < 4 := by omega
private theorem impossible (n : Nat) (positive : 0 < n) (zero : n = 0) : False := by omega

/-- Both inequalities hold of the SAME input; independent inhabitants do not suffice. -/
theorem simultaneous : hypotheses% dependent := ⟨1,by decide,by decide,True.intro⟩

/-- A contradictory full premise package is rejected. -/
theorem contradictory : ¬ (hypotheses% impossible) := by
  rintro ⟨n,positive,zero,_⟩
  omega
end H62.AbiWorld.SchemaControls
#print axioms H62.AbiWorld.SchemaControls.simultaneous
#print axioms H62.AbiWorld.SchemaControls.contradictory
