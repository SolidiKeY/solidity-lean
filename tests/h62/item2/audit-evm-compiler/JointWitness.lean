import tests.h62.item2.«audit-evm-compiler».JointImpossible

/-! Elaborate a supplied witness against the complete original forall telescope.
All dependent data, certificates and proof hypotheses are packaged together.
The original conclusion is never used to manufacture a premise. Kernel checking,
closed-expression checks and standard-axiom checks guard every declaration. -/
namespace Solidity.H62.EvmCompilerAudit.Tool
open Lean Meta Elab Command Term

syntax (name := jointWitnessCmd) "#audit_joint_witness " str " as " ident " := " term : command
elab_rules : command
  | `(#audit_joint_witness $original:str as $target:ident := $value:term) => liftTermElabM do
    let requested := original.getString
    let candidates := (← getEnv).constants.toList.filter fun entry =>
      entry.1.toString == requested || (privateToUserName entry.1).toString == requested
    unless candidates.length == 1 do throwError "expected exactly one original constant"
    let (originalName, ci) := candidates.head!
    unless ci matches .thmInfo _ do throwError "expected an original theorem"
    forallTelescope ci.type fun xs _ => do
      let type ← jointPackage xs.toList
      let proof ← elabTermEnsuringType value type
      synthesizeSyntheticMVarsNoPostponing
      let type ← instantiateMVars type
      let proof ← instantiateMVars proof
      if type.hasFVar || type.hasMVar || proof.hasFVar || proof.hasMVar then
        throwError "audit_joint_witness produced an open expression"
      let previous ← getEnv
      addDecl <| .thmDecl { name := target.getId, levelParams := ci.levelParams, type, value := proof }
      let allowed := [``propext, ``Classical.choice, ``Quot.sound]
      unless (← collectAxioms target.getId).all (allowed.contains ·) do
        setEnv previous
        throwError "audit_joint_witness requires only standard axioms"
    logInfo m!"JOINT: {originalName} => {target.getId}"
/-- Intentional impossible fixture exercises rejection of ambient assumptions. -/
private theorem closureControl (n : Nat) (h : n < 0) : False := Nat.not_lt_zero n h

/-- error: audit_joint_witness produced an open expression -/
#guard_msgs in
#audit_joint_witness "Solidity.H62.EvmCompilerAudit.Tool.closureControl" as rejectedAmbientWitness := by
  exact ⟨n, h, True.intro⟩

#print axioms closureControl
end Solidity.H62.EvmCompilerAudit.Tool
