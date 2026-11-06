import tests.h62.item2.«audit-calculus».FailureWitnesses
import tests.h62.item2.«audit-calculus».FailureAdditionalWitnesses
import tests.h62.item2.«audit-calculus».CreationWitnesses
import tests.h62.item2.«audit-calculus».CreationAdditionalWitnesses

/-!
Guarded regression: an empty inventory, omitted private/generated theorem or
unapproved transitive axiom must not make fixture validation appear successful.
This audit command prints and checks actual imported theorem axioms; it does not
construct a semantic proof or alter the core trust baseline. Public/private and
compiler-generated constants are selected by their actual imported module index.
-/
namespace H62.AuditCalculus.WitnessAxioms
open Lean Elab Command
set_option Elab.async false

elab "#audit_fixture_axioms " module:str : command => do
  let moduleName := module.getString.toName
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let .thmInfo _ := info then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == moduleName then
          names := names.push name
  if names.isEmpty then
    throwError "no theorem declarations for requested module {module.getString}"
  let sortedNames := names.qsort (fun a b => a.toString < b.toString)
  for name in sortedNames do
    let id := mkIdent name
    elabCommand (← `(command| #print axioms $id:ident))
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unapproved axiom {axiomName} in fixture theorem {name}"
    let info ← getConstInfo name
    logInfo m!"H62_OWNED_AXIOMS {Json.mkObj [
      ("module", toJson module.getString),
      ("name", toJson name.toString),
      ("user_name", toJson ((privateToUserName? name).getD name).toString),
      ("is_private", toJson (isPrivateName name)),
      ("signature", toJson (reprStr info.type)),
      ("axioms", toJson (axioms.toList.map Name.toString))] |>.compress}"
  logInfo m!"H62_OWNED_AXIOM_TOTAL {Json.mkObj [
    ("module", toJson module.getString), ("count", toJson sortedNames.size)] |>.compress}"

/-- error: no theorem declarations for requested module H62.NoSuchFixtureModule -/
#guard_msgs in
#audit_fixture_axioms "H62.NoSuchFixtureModule"

#audit_fixture_axioms "tests.h62.item2.«audit-calculus».FailureWitnesses"
#audit_fixture_axioms "tests.h62.item2.«audit-calculus».FailureAdditionalWitnesses"
#audit_fixture_axioms "tests.h62.item2.«audit-calculus».CreationWitnesses"
#audit_fixture_axioms "tests.h62.item2.«audit-calculus».CreationAdditionalWitnesses"
end H62.AuditCalculus.WitnessAxioms
