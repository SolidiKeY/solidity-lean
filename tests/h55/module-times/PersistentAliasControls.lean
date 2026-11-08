import Lean

/-! Guard regression: a speculative cross-checkpoint alias reuse must not accept
an open, changed, unsafe, polymorphic or non-definition declaration. This isolated
control does not install a cache or establish replay correctness or speed. An
actual caller must inspect a declaration retrieved by exact name from the current
kernel-checked environment; a fabricated ConstantInfo proves nothing. -/
namespace ModuleTimes.PersistentAliasControls
open Lean

/-- Conservative structural check for an exploratory alias candidate. -/
def accepts (ty value : Expr) (info : ConstantInfo) : Bool :=
  if ty.hasFVar || ty.hasMVar || ty.hasLooseBVars || ty.hasLevelParam ||
     value.hasFVar || value.hasMVar || value.hasLooseBVars || value.hasLevelParam then
    false
  else
    match info with
    | .defnInfo d => d.safety == .safe && d.levelParams.isEmpty && d.type == ty && d.value == value
    | _ => false

private def ty : Expr := mkConst ``Nat
private def value : Expr := mkNatLit 2
private def good : DefinitionVal := {
  name := `testAlias, levelParams := [], type := ty, value := value,
  hints := .opaque, safety := .safe }

#guard accepts ty value (.defnInfo good)
#guard !(accepts ty (mkNatLit 3) (.defnInfo good))
#guard !(accepts (mkConst ``Bool) value (.defnInfo good))
#guard !(accepts ty value (.defnInfo { good with safety := .unsafe }))
#guard !(accepts ty value (.defnInfo { good with levelParams := [`u] }))
#guard !(accepts ty value (.axiomInfo { name := `bad, levelParams := [], type := ty, isUnsafe := false }))
#guard !(accepts ty (.bvar 0) (.defnInfo { good with value := .bvar 0 }))
#guard !(accepts (.sort (.param `u)) value (.defnInfo { good with type := .sort (.param `u) }))
#guard !(accepts ty (.fvar ⟨`x⟩) (.defnInfo { good with value := .fvar ⟨`x⟩ }))
#guard !(accepts ty (.mvar ⟨`x⟩) (.defnInfo { good with value := .mvar ⟨`x⟩ }))
#guard !(accepts (.sort (.mvar ⟨`u⟩)) value (.defnInfo { good with type := .sort (.mvar ⟨`u⟩) }))
private def closedBinder : Expr := .lam `x ty (.bvar 0) .default
#guard accepts ty closedBinder (.defnInfo { good with value := closedBinder })

private def checkedValue : Nat := 2

-- Exercise the structural guard on a declaration actually retrieved from the
-- current elaboration environment; this does not test checkpoint persistence.
run_cmd do
  let info ← Lean.getConstInfo ``checkedValue
  match info with
  | .defnInfo d =>
    unless accepts d.type d.value info do
      throwError "actual checked declaration was rejected"
    if accepts d.type (mkNatLit 3) info then
      throwError "changed value was accepted"
  | _ => throwError "expected a definition"
end ModuleTimes.PersistentAliasControls
