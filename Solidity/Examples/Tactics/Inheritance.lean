import Solidity.Frontend.Import
import Solidity.Tools.Run
import Solidity.Semantics.Deploy

/-!
# Inheritance: initialization, base constructors, `super`

The compiled fixture checks virtual dispatch while evaluating the base
initializer and initializes the diamond in reverse C3 order. Every assertion
in its constructor is executed by the typed interpreter and checked in Lean.
-/

namespace Solidity.Examples.Tactics.Inheritance
open Semantics
open Lean (toJson)

solc_import "../../../tests/solc/Inheritance.ast.json" hash 0x8282c171008eb988
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

/-! ## Base constructors

solc's legacy creation code runs every initializer (most base first), then
the base constructors' arguments (derived to base), then the bodies (base to
derived): `late` is already `9` when `CtorMid` passes `m + late` on, and
`CtorRoot`'s body dispatches `probe` to `CtorLeaf`, which reads `leaf`. The
import composes them into one constructor member. -/

solc_import "../../../tests/solc/Inheritance.ast.json" hash 0x8282c171008eb988
  as Imported.CtorLeaf testing

/-- The four assertions of `CtorLeaf`'s constructor hold on the deployment. -/
theorem base_constructors :
    (Contract.deployT Imported.CtorLeaf
      sol[Imported.CtorLeaf]{ constructor(); } {}).toOption.isSome = true := by
  decide +kernel

/--
info: ok
balance 0
root = 12
seen = 1107
early = 7
mid = 27
late = 9
leaf = 11
order = 2711
-/
#guard_msgs in #deploy Imported.CtorLeaf()

/-! The implicit constructor of `is CtorRoot(4)`; and a header argument for an
unnamed parameter, still evaluated. -/

solc_import "../../../tests/solc/Inheritance.ast.json" hash 0x8282c171008eb988
  as Imported.CtorImplicit testing

/--
info: ok
balance 0
root = 4
seen = 7
early = 7
next = 1
-/
#guard_msgs in #deploy Imported.CtorImplicit()

solc_import "../../../tests/solc/Inheritance.ast.json" hash 0x8282c171008eb988
  as Imported.CtorUnnamedChild testing

/--
info: ok
balance 0
got = 5
-/
#guard_msgs in #deploy Imported.CtorUnnamedChild(5)

/-! ## `super`

Each base version is its own member, and `super.name()` in a version names
the next one in `SuperDiamond`'s C3 order: `name` calls `SuperRight`'s
(`solcFunction445`), which calls `SuperLeft`'s (`427`), not its parent's. -/

solc_import "../../../tests/solc/Inheritance.ast.json" hash 0x8282c171008eb988
  as Imported.SuperDiamond testing

/--
info: [(solcFunction409, []), (solcFunction427, [solcFunction409]), (solcFunction445, [solcFunction427]), (name, [solcFunction445])]
-/
#guard_msgs in
#eval IO.println ((Imported.SuperDiamond.funs.take 4).map fun (n, f) =>
  (n, f.body.flatMap fun (s : RawStmt) => match s with
    | .ret (some (.binop _ (.binop _ (.call g _) _) _)) => [g]
    | _ => []))

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
