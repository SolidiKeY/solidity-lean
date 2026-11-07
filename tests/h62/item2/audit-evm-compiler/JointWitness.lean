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
    forallTelescopeReducing ci.type fun xs _ => do
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
/-- Check closed equalities without manufacturing a new proof declaration.
Opening reducible telescope tails prevents Not/abbreviation-hidden hypotheses
from being classified as closed. The caller still checks identity and axioms. -/
def ensureClosedEquality (ci : ConstantInfo) : MetaM Unit := do
  forallTelescopeReducing ci.type fun xs conclusion => do
    unless xs.isEmpty do throwError "closed equality audit found hypotheses"
    unless (← whnf conclusion).isAppOfArity ``Eq 3 do
      throwError "closed equality audit requires an equality proposition"

syntax (name := closedEqualityCmd) "#audit_closed_eq " str : command
elab_rules : command
  | `(#audit_closed_eq $original:str) => liftTermElabM do
    let candidates := (← getEnv).constants.toList.filter fun entry =>
      entry.1.toString == original.getString ||
        (privateToUserName entry.1).toString == original.getString
    unless candidates.length == 1 do throwError "expected exactly one original constant"
    let (name, ci) := candidates.head!
    unless ci matches .thmInfo _ do throwError "expected an original theorem"
    ensureClosedEquality ci
    unless (← collectAxioms name).all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "closed equality has nonstandard axioms"

/-- Intentional impossible fixture exercises rejection of ambient assumptions. -/
private theorem closureControl (n : Nat) (h : n < 0) : False := Nat.not_lt_zero n h

/-- error: audit_joint_witness produced an open expression -/
#guard_msgs in
#audit_joint_witness "Solidity.H62.EvmCompilerAudit.Tool.closureControl" as rejectedAmbientWitness := by
  exact ⟨n, h, True.intro⟩

private abbrev HiddenInputs := ∀ n : Nat, n < 0 → False
private theorem aliasControl : HiddenInputs := fun n h => Nat.not_lt_zero n h

/-- error: closed equality audit found hypotheses -/
#guard_msgs in
#audit_closed_eq "Solidity.H62.EvmCompilerAudit.Tool.aliasControl"

private abbrev PositiveInputs := ∀ n : Nat, n = 0 → n = n
private theorem aliasPositive : PositiveInputs := fun _ _ => rfl
#audit_joint_witness "Solidity.H62.EvmCompilerAudit.Tool.aliasPositive" as Solidity.H62.EvmCompilerAudit.Tool.aliasJoint := by
  exact ⟨0, rfl, True.intro⟩

#print axioms closureControl
#print axioms aliasControl
#print axioms aliasPositive
#print axioms aliasJoint
end Solidity.H62.EvmCompilerAudit.Tool
