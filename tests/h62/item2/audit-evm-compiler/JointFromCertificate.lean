import tests.h62.item2.«audit-evm-compiler».JointWitness

/-! Infer an exact joint input tuple from an existing closed certificate.
Only the final original proof input is matched. No original conclusion is used,
no defaults fill remaining inputs, and unresolved data rejects the command. -/
namespace Solidity.H62.EvmCompilerAudit.Tool
open Lean Meta Elab Command

def packClosedValues (type : Expr) : List Expr → MetaM Expr
  | [] => do
    unless (← whnf type).isConstOf ``True do throwError "joint package did not end in True"
    return mkConst ``True.intro
  | value :: rest => do
    let expected ← whnf type
    unless expected.isAppOfArity ``Exists 2 do throwError "joint package expected Exists"
    let args := expected.getAppArgs
    let tail ← packClosedValues (mkApp args[1]! value) rest
    mkAppOptM ``Exists.intro #[some args[0]!, some args[1]!, some value, some tail]

def proveFromCertificate (original evidence target : Name) : MetaM Unit := do
  let ci ← getConstInfo original
  let certificate ← getConstInfo evidence
  unless ci matches .thmInfo _ do throwError "expected an original theorem"
  unless certificate matches .thmInfo _ do throwError "expected a certificate theorem"
  unless certificate.levelParams.isEmpty do throwError "certificate must be concrete"
  forallTelescopeReducing certificate.type fun xs _ => do
    unless xs.isEmpty do throwError "certificate must have no leading inputs"
  let (arguments, _, _) ← forallMetaTelescopeReducing ci.type
  unless !arguments.isEmpty do throwError "original has no input to match"
  let last := arguments.back!
  unless (← isProp (← inferType last)) do throwError "last original input must be a proof"
  unless ← isDefEq (← inferType last) certificate.type do
    throwError "certificate does not match the last original input"
  unless ← isDefEq last (mkConst evidence) do throwError "could not assign certificate"
  let values ← arguments.toList.mapM instantiateMVars
  if values.any (fun value => value.hasMVar || value.hasFVar) then
    throwError "certificate did not determine every original input"
  let type ← forallTelescopeReducing ci.type fun xs _ => jointPackage xs.toList
  let proof ← instantiateMVars (← packClosedValues type values)
  if type.hasFVar || type.hasMVar || proof.hasFVar || proof.hasMVar then
    throwError "certificate produced an open joint package"
  let previous ← getEnv
  addDecl <| .thmDecl {name := target, levelParams := ci.levelParams, type, value := proof}
  unless (← collectAxioms target).all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    setEnv previous
    throwError "certificate joint witness requires only standard axioms"

syntax (name := jointCertificateCmd) "#audit_joint_from " str " using " str " as " ident : command
elab_rules : command
  | `(#audit_joint_from $original:str using $evidence:str as $target:ident) => liftTermElabM do
    let resolve (s : String) := do
      let candidates := (← getEnv).constants.toList.filter fun entry =>
        entry.1.toString == s || (privateToUserName entry.1).toString == s
      unless candidates.length == 1 do throwError "expected exactly one theorem identity"
      return candidates.head!.1
    let originalName ← resolve original.getString
    let evidenceName ← resolve evidence.getString
    proveFromCertificate originalName evidenceName target.getId
    logInfo m!"JOINT-CERTIFICATE: {originalName} <= {evidenceName} => {target.getId}"

private theorem zeroCertificate : (0 : Nat) = 0 := rfl
private theorem conditional (n : Nat) (_h : n = 0) : n = n := rfl
private theorem unusedData (n _k : Nat) (_h : n = 0) : n = n := rfl
#audit_joint_from "Solidity.H62.EvmCompilerAudit.Tool.conditional" using "Solidity.H62.EvmCompilerAudit.Tool.zeroCertificate" as Solidity.H62.EvmCompilerAudit.Tool.certificateControl

/-- error: certificate must have no leading inputs -/
#guard_msgs in
#audit_joint_from "Solidity.H62.EvmCompilerAudit.Tool.conditional" using "Nat.zero_le" as rejectedConditionalCertificate

/-- error: certificate did not determine every original input -/
#guard_msgs in
#audit_joint_from "Solidity.H62.EvmCompilerAudit.Tool.unusedData" using "Solidity.H62.EvmCompilerAudit.Tool.zeroCertificate" as rejectedUndeterminedData

#print axioms zeroCertificate
#print axioms conditional
#print axioms unusedData
#print axioms Solidity.H62.EvmCompilerAudit.Tool.certificateControl
end Solidity.H62.EvmCompilerAudit.Tool
