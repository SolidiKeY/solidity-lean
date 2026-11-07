import Lean

/-! Construct checked negated existential packages for H69 classifications.
The original constant is applied to every forall binder, including Type-valued
certificates and dependent proof arguments. Only an explicit terminal False is
accepted. Every generated declaration passes Lean.addDecl kernel checking.
Intentionality is separately reviewed metadata, never inferred by this command. -/
namespace Solidity.H62.EvmCompilerAudit.Tool
open Lean Meta Elab Command

def jointPackage : List Expr → MetaM Expr
  | [] => pure (mkConst ``True)
  | x :: xs => do
    let tail ← jointPackage xs
    let predicate ← mkLambdaFVars #[x] tail
    mkAppM ``Exists #[predicate]

def eliminatePackage (xs : List Expr) (jointProof terminalProof : Expr) : MetaM Expr := do
  match xs with
  | [] => pure terminalProof
  | x :: rest =>
    let tailType ← jointPackage rest
    withLocalDeclD `remaining tailType fun remaining => do
      let body ← eliminatePackage rest remaining terminalProof
      let step ← mkLambdaFVars #[x, remaining] body
      mkAppM ``Exists.elim #[jointProof, step]

def proveImpossible (original : Name) (target : Name) : MetaM Unit := do
  let ci ← getConstInfo original
  let levels := ci.levelParams.map Level.param
  forallTelescope ci.type fun xs conclusion => do
    unless conclusion.isConstOf ``False do
      throwError "audit_joint_impossible requires an explicit terminal False"
    let joint ← jointPackage xs.toList
    let proof ← withLocalDeclD `joint joint fun h => do
      let terminal := mkAppN (mkConst original levels) xs
      mkLambdaFVars #[h] (← eliminatePackage xs.toList h terminal)
    let type := mkApp (mkConst ``Not) joint
    if type.hasFVar || type.hasMVar || proof.hasFVar || proof.hasMVar then
      throwError "audit_joint_impossible produced an open expression"
    let previous ← getEnv
    addDecl <| .thmDecl { name := target, levelParams := ci.levelParams, type, value := proof }
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    unless (← collectAxioms target).all (allowed.contains ·) do
      setEnv previous
      throwError "audit_joint_impossible requires only standard axioms"

syntax (name := jointImpossibleCmd) "#audit_joint_impossible " str " as " ident : command
elab_rules : command
  | `(#audit_joint_impossible $original:str as $target:ident) => liftTermElabM do
    let requested := original.getString
    let candidates := (← getEnv).constants.toList.filter fun entry => entry.1.toString == requested || (privateToUserName entry.1).toString == requested
    unless candidates.length == 1 do throwError "expected exactly one original constant"
    proveImpossible candidates.head!.1 target.getId
    logInfo m!"H69: {candidates.head!.1} => {target.getId}"

/-- error: audit_joint_impossible requires an explicit terminal False -/
#guard_msgs in
#audit_joint_impossible "Nat.zero_le" as rejectedOrdinaryTheorem
end Solidity.H62.EvmCompilerAudit.Tool
