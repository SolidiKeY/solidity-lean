import tests.h62.item2.«audit-yul».Refutations
import Solidity.Lowering.P8.SourceRealization
import Lean
/-! Elaborated type equality, not merely individually inhabited arguments. -/
open Lean Elab Command
run_cmd do
  let pairs : Array (Name × Name) := #[
    (`Solidity.Frontend.YulJson.Words.declaration_impossible, `H62.AuditYul.Refutations.declaration_impossible),
    (`Solidity.Frontend.YulJson.Words.reference_impossible, `H62.AuditYul.Refutations.reference_impossible),
    (`Solidity.Yul.Checks.ClosedFunctions.no_empty_member, `H62.AuditYul.Refutations.no_empty_member),
    (`Solidity.Yul.Checks.ClosedFunctions.no_external_reference, `H62.AuditYul.Refutations.no_external_reference),
    (`Solidity.Yul.Checks.ClosedPure.no_memory_builtin, `H62.AuditYul.Refutations.no_memory_builtin),
    (`Solidity.Yul.ScopedExternalD.function_noWrites, `H62.AuditYul.Refutations.function_noWrites),
    (`Solidity.Yul.GlobalExternalD.noWrites, `H62.AuditYul.Refutations.global_noWrites),
    (`Solidity.Yul.ScalarRef.not_globals, `H62.AuditYul.Refutations.scalar_not_globals),
    (`Solidity.Yul.Views.FixedDeclaration.no_dynamic_array, `H62.AuditYul.Refutations.no_dynamic_array),
    (`Solidity.Yul.WordCell.not_globals, `H62.AuditYul.Refutations.wordCell_not_globals)]
  for (original, certificate) in pairs do
    let a ← getConstInfo original
    let b ← getConstInfo certificate
    unless a.levelParams == b.levelParams && a.type == b.type do
      throwError "refutation telescope drift: {original} versus {certificate}"
  let source ← getConstInfo `Solidity.Lowering.P8.SpecExecution.no_countable_resource
  let dependency ← getConstInfo `Solidity.Lowering.P8.ResourceContractLaw1.nat_encodable_resource_impossible
  unless source.levelParams == dependency.levelParams do throwError "resource universe drift"
  unless ← liftTermElabM (Lean.Meta.isDefEq source.type dependency.type) do
    throwError "resource refutation telescope drift"
  logInfo m!"H69_FROZEN_TYPE_FIDELITY_PASS: {pairs.size + 1} exact elaborated telescopes"
