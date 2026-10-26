import Solidity.Frontend.Testing
import Solidity.Tools.Run

/-!
# Declaration metadata from validated solc identities

The fixture exercises contract-name bytes, interface selectors without
inherited members, and canonical error/event signatures. Malformed selector
metadata and anonymous events are rejected at the importer boundary.
-/

namespace Solidity.Examples.Tactics.DeclarationMetadata

open Lean (Json toJson)
open Frontend
open scoped Scoped

solc_import "../../../tests/solc/DeclarationMetadata.ast.json" hash 0x22c417e9ab4111f1
  as Imported.DeclarationMetadata testing
solc_scoped_problems Imported.DeclarationMetadata decl

/-- Only the child's own method contributes to its interface ID. -/
theorem ownInterface : ⊢ Imported.DeclarationMetadata.interfaceOwnOnly.problem := by
  sol_prove

/-- Reading a selector still evaluates its receiver exactly once. -/
theorem evaluatesReceiver : ⊢ Imported.DeclarationMetadata.receiverEffects.problem := by
  sol_prove

/-- Selector receivers in skipped boolean/conditional arms stay skipped. -/
theorem lazyReceiver : ⊢ Imported.DeclarationMetadata.lazyReceiverEffects.problem := by
  sol_prove

/-- A generated receiver helper has no source-level internal function value. -/
example : (fnTag Imported.DeclarationMetadata "solcMetadataSelector239__").isOk = false := by
  decide +kernel

/-- Nor can an ABI function selector expose the implementation helper. -/
example : fnSelector? Imported.DeclarationMetadata "solcMetadataSelector239__" = none := by
  decide +kernel

private def event (anonymous : Bool) : Json := Json.mkObj [
  ("nodeType", .str "EventDefinition"), ("id", toJson (1 : Int)),
  ("anonymous", .bool anonymous),
  ("eventSelector", .str "0000000000000000000000000000000000000000000000000000000000000001")]

private def eventRef : Json := Json.mkObj [
  ("nodeType", .str "Identifier"), ("referencedDeclaration", toJson (1 : Int))]

/-- The full 32-byte event selector is retained. -/
example : (declarationMetadata [event false] eventRef "selector").toOption =
    some (some "bytes32(1)") := by decide +kernel

/-- Anonymous events have no selector, including in manually supplied fixtures. -/
example : (declarationMetadata [event true] eventRef "selector").isOk = false := by
  decide +kernel

/-- Truncated selector metadata cannot silently become zero. -/
example : (declarationSelector (Json.mkObj [("functionSelector", .str "123")])
    "functionSelector" 4).isOk = false := by decide +kernel

/-- Correct length alone does not admit a non-hexadecimal selector. -/
example : (declarationSelector (Json.mkObj [("errorSelector", .str "0000000g")])
    "errorSelector" 4).isOk = false := by decide +kernel

end Solidity.Examples.Tactics.DeclarationMetadata
