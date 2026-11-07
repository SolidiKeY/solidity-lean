import tests.h62.item2.«audit-evm-compiler».JointImpossible

/-! H69 refutation packages with definition-hidden hypotheses exposed.
Intentionality is separately justified for each audited original statement. -/
namespace Solidity.H62.EvmCompilerAudit.Tool
open Lean Meta Elab Command

def proveRefutation (original target : Name) : MetaM Unit := do
  let ci ← getConstInfo original
  unless ci matches .thmInfo _ do throwError "expected an original theorem"
  forallTelescopeReducing ci.type (whnfType := true) fun xs conclusion => do
    unless conclusion.isConstOf ``False do
      throwError "audit_refutation requires a terminal False"
    let joint ← jointPackage xs.toList
    let proof ← withLocalDeclD `joint joint fun h => do
      let terminal := mkAppN (mkConst original (ci.levelParams.map Level.param)) xs
      mkLambdaFVars #[h] (← eliminatePackage xs.toList h terminal)
    let type := mkApp (mkConst ``Not) joint
    if type.hasFVar || type.hasMVar || proof.hasFVar || proof.hasMVar then
      throwError "audit_refutation produced an open expression"
    let previous ← getEnv
    addDecl <| .thmDecl {name := target, levelParams := ci.levelParams, type, value := proof}
    unless (← collectAxioms target).all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      setEnv previous
      throwError "audit_refutation requires only standard axioms"

syntax (name := jointRefutationCmd) "#audit_refutation " str " as " ident : command
elab_rules : command
  | `(#audit_refutation $original:str as $target:ident) => liftTermElabM do
    let requested := original.getString
    let candidates := (← getEnv).constants.toList.filter fun entry =>
      entry.1.toString == requested || (privateToUserName entry.1).toString == requested
    unless candidates.length == 1 do throwError "expected exactly one original constant"
    proveRefutation candidates.head!.1 target.getId
    logInfo m!"REFUTATION: {candidates.head!.1} => {target.getId}"

/-- error: audit_refutation requires a terminal False -/
#guard_msgs in
#audit_refutation "Nat.zero_le" as rejectedNonRefutation

-- Positive regression: Not hides the impossible input n < 0.
#audit_refutation "Nat.not_lt_zero" as Solidity.H62.EvmCompilerAudit.Tool.refutationControl
#print axioms Solidity.H62.EvmCompilerAudit.Tool.refutationControl
end Solidity.H62.EvmCompilerAudit.Tool
