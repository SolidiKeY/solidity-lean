import Solidity.Frontend.Import
import Solidity.Tools.Run
import Solidity.Semantics.Deploy

/-!
# Inherited initialization

The compiled fixture checks virtual dispatch while evaluating the base
initializer and initializes the diamond in reverse C3 order. Every assertion
in its constructor is executed by the typed interpreter and checked in Lean.
-/

namespace Solidity.Examples.Tactics.Inheritance
open Semantics
open Lean (toJson)

solc_import "../../../tests/solc/Inheritance.ast.json" hash 0x41b63713787db6a0
  as Imported.InitDiamond testing

/-- The inherited initializers and all five constructor assertions succeed. -/
theorem diamond_initialization :
    (Contract.deployT Imported.InitDiamond
      sol[Imported.InitDiamond]{ constructor(); } {}).toOption.isSome = true := by
  decide +kernel

/--
info: ok
balance 0
counter = 2
initialized = 2
left = 3
right = 4
result = 34
-/
#guard_msgs in #deploy Imported.InitDiamond()

private def metadataContract (id : Int) (bases order : List Int) : Lean.Json :=
  Lean.Json.mkObj [
    ("nodeType", .str "ContractDefinition"), ("id", toJson id),
    ("baseContracts", toJson (bases.map fun base => Lean.Json.mkObj [
      ("baseName", Lean.Json.mkObj [("referencedDeclaration", toJson base)])])),
    ("linearizedBaseContracts", toJson order)]

private def metadataDiamond (order : List Int) : Except String (List Lean.Json) :=
  let root := metadataContract 1 [] [1]
  let left := metadataContract 2 [1] [2, 1]
  let right := metadataContract 3 [1] [3, 1]
  let leaf := metadataContract 4 [2, 3] order
  Frontend.contractLineage [root, left, right, leaf] leaf

/-- C3's sibling order matters even when both candidates are topological. -/
example : (metadataDiamond [4, 3, 2, 1]).isOk = true := by decide +kernel
example : (metadataDiamond [4, 2, 3, 1]).isOk = false := by decide +kernel
example : (metadataDiamond [4, 3, 2]).isOk = false := by decide +kernel
example : (metadataDiamond [4, 3, 2, 9]).isOk = false := by decide +kernel

example : (Frontend.mergeC3 4 [[1, 2], [2, 1]]).isOk = false := by
  decide +kernel

end Solidity.Examples.Tactics.Inheritance
