import Solidity.Evm.Compiler
import Lean

/-! Audit-only correlated fixtures recovered from existing closed public Input
certificates. Every field and the complete proof travel together; no defaults
or assumptions are added and private identities are resolved from the environment. -/
namespace Solidity.H62.EvmCompilerAudit.Fixtures
open Lean Meta Elab Command

structure InputFixture where
  C : Contract
  b : Nat
  Γ : Ctx
  Δ : Ctx
  F : Evm.Frag Γ
  P : Solidity.Prog C Γ Δ
  result : Evm.Compiler.Compilation b F P
  L : Nat
  frame : Nat
  base : Nat → Fin Evm.W
  σ : State C Γ
  m : Evm.Machine
  input : result.Input L frame base σ m

syntax (name := inputFixtureCmd) "#audit_input_fixture " str " as " ident : command
elab_rules : command
  | `(#audit_input_fixture $certificate:str as $target:ident) => liftTermElabM do
    let candidates := (← getEnv).constants.toList.filter fun entry =>
      entry.1.toString == certificate.getString ||
        (privateToUserName entry.1).toString == certificate.getString
    unless candidates.length == 1 do throwError "expected exactly one certificate identity"
    let (name, ci) := candidates.head!
    unless ci matches .thmInfo _ do throwError "expected a certificate theorem"
    unless ci.levelParams.isEmpty do throwError "certificate must be concrete"
    forallTelescopeReducing ci.type fun xs _ => do
      unless xs.isEmpty do throwError "certificate must have no leading inputs"
    unless ci.type.isAppOfArity ``Evm.Compiler.Compilation.Input 12 do
      throwError "expected an exact public Input certificate"
    let value := mkAppN (mkConst ``InputFixture.mk) (ci.type.getAppArgs.push (mkConst name))
    if value.hasFVar || value.hasMVar then throwError "fixture must be closed"
    let previous ← getEnv
    addDecl <| .defnDecl {
      name := target.getId
      levelParams := []
      type := mkConst ``InputFixture
      value := value
      hints := .abbrev
      safety := .safe }
    unless (← collectAxioms target.getId).all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      setEnv previous
      throwError "fixture requires only standard axioms"
    logInfo m!"INPUT-FIXTURE: {name} => {target.getId}"

/-- error: certificate must have no leading inputs -/
#guard_msgs in
#audit_input_fixture "Nat.zero_le" as rejectedConditionalFixture

private theorem closedEquality : (0 : Nat) = 0 := rfl
/-- error: expected an exact public Input certificate -/
#guard_msgs in
#audit_input_fixture "Solidity.H62.EvmCompilerAudit.Fixtures.closedEquality" as rejectedNonInputFixture
#print axioms closedEquality
end Solidity.H62.EvmCompilerAudit.Fixtures
