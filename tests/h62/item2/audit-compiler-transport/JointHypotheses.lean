import Lean

/-! Audit-only metaprogramming. The generated propositions existentially bind
ALL parameters of a False-conclusion declaration, in dependency order. The
proof terms use only the original theorem, lambda abstraction and Exists.elim.
This is not an inhabitation claim about any individual premise structure. -/
namespace H62.CompilerTransport
open Lean Meta Elab Term

private def joint (name : Name) (wantProof : Bool) : TermElabM Expr := do
  let constant ← mkConstWithFreshMVarLevels name
  forallTelescope (← inferType constant) fun xs conclusion => do
    unless conclusion.isConstOf ``False do
      throwError "joint impossibility requires a literal False conclusion"
    let mut body := Lean.mkConst ``True
    let mut proof ← withLocalDeclD `trivial body fun h =>
      mkLambdaFVars #[h] (mkAppN constant xs)
    for x in xs.reverse do
      let predicate ← mkLambdaFVars #[x] body
      let existential ← mkAppM ``Exists #[predicate]
      let branch ← mkLambdaFVars #[x] proof
      proof ← withLocalDeclD `witness existential fun witness => do
        mkLambdaFVars #[witness] (← mkAppM ``Exists.elim #[witness, branch])
      body := existential
    return if wantProof then proof else body

syntax "jointHypotheses% " ident : term
syntax "jointImpossible% " ident : term
elab_rules : term
  | `(jointHypotheses% $name:ident) => joint name.getId false
  | `(jointImpossible% $name:ident) => joint name.getId true
end H62.CompilerTransport
