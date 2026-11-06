import tests.h62.item2.«audit-calculus».ExprDagCensus

/-! Same-format verification for exact DAG exports. The joint proposition is
created by the unchanged nonreducing #joint_premises command; this command
only checks it and serializes the original type with the DAG exporter. -/
namespace H62.AuditCalculus.DagJoint
open Lean Meta Elab Command H62.AuditCalculus.ExprDagCensus

elab "#verify_joint_dag " original:ident " with " witness:ident : command => do
  let originalInfo ← getConstInfo original.getId
  unless originalInfo matches .thmInfo _ do throwError "original must be a theorem"
  let witnessName ← resolveGlobalConstNoOverload witness
  let witnessInfo ← getConstInfo witnessName
  unless witnessInfo matches .thmInfo _ do throwError "witness must be a checked theorem"
  let target ← liftCoreM <| mkFreshUserName (Name.mkSimple "_h62DagExpected")
  let targetName := (← getCurrNamespace) ++ target
  let targetId := mkIdent target
  elabCommand (← `(command| #joint_premises $original:ident as $targetId:ident))
  let expectedInfo ← getConstInfo targetName
  let expected ← match expectedInfo with
    | .defnInfo info => pure info.value
    | _ => throwError "joint extractor did not create its proposition"
  liftTermElabM do
    unless ← isDefEq expected witnessInfo.type do
      throwError "witness does not match the exact unchanged joint telescope"
  let env ← getEnv
  let originalModule := (env.getModuleIdxFor? original.getId).map
    (fun idx => env.header.moduleNames[idx.toNat]!.toString)
  let axioms ← collectAxioms witnessName
  for axiomName in axioms do
    unless #["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains axiomName do
      throwError "unapproved axiom {axiomName}"
  logInfo m!"H62_JOINT_VERIFIED {Json.mkObj [
    ("original", toJson original.getId.toString),
    ("original_module", toJson originalModule),
    ("witness", toJson witnessName.toString),
    ("original_type_expression_format", toJson "expr-dag-v1"),
    ("original_type_expression", expressionDag originalInfo.type),
    ("axioms", toJson (axioms.toList.map Name.toString))] |>.compress}"

end H62.AuditCalculus.DagJoint
