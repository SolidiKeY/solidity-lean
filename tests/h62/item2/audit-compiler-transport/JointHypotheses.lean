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
    if !wantProof then
      let mut body := Lean.mkConst ``True
      for x in xs.reverse do
        body ← mkAppM ``Exists #[← mkLambdaFVars #[x] body]
      return body
    unless conclusion.consumeMData.isConstOf ``False do
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
    return proof

syntax "jointHypotheses% " ident : term
syntax "jointImpossible% " ident : term
elab_rules : term
  | `(jointHypotheses% $name:ident) => joint name.getId false
  | `(jointImpossible% $name:ident) => joint name.getId true
end H62.CompilerTransport

namespace H62.CompilerTransport
open Lean Meta Elab Term
private def dottedConstant (text : String) : Name :=
  (text.splitOn ".").foldl (fun accumulated part =>
    match part.toNat? with
    | some number => .num accumulated number
    | none => .str accumulated part) .anonymous

syntax "jointHypothesesStr% " str : term
syntax "jointImpossibleStr% " str : term
syntax "emptyJoint% " str : term
elab_rules : term
  | `(jointHypothesesStr% $name:str) => joint (dottedConstant name.getString) false
  | `(jointImpossibleStr% $name:str) => joint (dottedConstant name.getString) true
  | `(emptyJoint% $name:str) => do
    let constant ← mkConstWithFreshMVarLevels (dottedConstant name.getString)
    forallTelescope (← inferType constant) fun xs _ => do
      unless xs.isEmpty do throwError "empty joint witness requires zero external parameters"
      pure (Lean.mkConst ``True.intro)
end H62.CompilerTransport
