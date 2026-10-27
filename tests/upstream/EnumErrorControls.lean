import Solidity.Tools.Upstream
open Solidity Solidity.Frontend Lean
solc_import "EnumErrorControls.legacy.ast.json" hash 0xc5464bc885660a81 as Group10.EnumLegacy.EnumErrorControls testing
solc_import "EnumErrorControls.viaIR.ast.json" hash 0xdbaad1f2702dbbc6 as Group10.EnumIR.EnumErrorControls testing
example : Group10.EnumLegacy.EnumErrorControls.report.length = 7 := by decide +kernel
example : Group10.EnumIR.EnumErrorControls.report.length = 7 := by decide +kernel
example : Group10.EnumLegacy.EnumErrorControls.report.all (·.status == .unsupported) = true := by decide +kernel
example : Group10.EnumIR.EnumErrorControls.report.all (·.status == .unsupported) = true := by decide +kernel
#eval (do
  for report in [Group10.EnumLegacy.EnumErrorControls.report,Group10.EnumIR.EnumErrorControls.report] do
    for r in report do
      unless (r.reason.splitOn "custom error aggregate has nominal enum").length == 2 do
        throw (IO.userError s!"source enum refused at wrong boundary: {r.sourceSignature}: {r.reason}")
  let root := Json.mkObj [("nodeType",toJson "UserDefinedTypeName"),("referencedDeclaration",toJson (1 : Nat))]
  let empty := Json.mkObj [("nodeType",toJson "StructDefinition"),("id",toJson (1 : Nat)),("members",toJson ([] : List Json))]
  let enum := Json.mkObj [("nodeType",toJson "EnumDefinition"),("id",toJson (1 : Nat))]
  unless errorAggregateHasEnum [] root && errorAggregateHasEnum [empty,enum] root &&
      errorAggregateHasEnum [enum,empty] root do throw (IO.userError "missing/ambiguous type ID admitted")
  let missing := Json.mkObj [("nodeType",toJson "StructDefinition"),("id",toJson (1 : Nat))]
  let malformed := Json.mkObj [("nodeType",toJson "StructDefinition"),("id",toJson (1 : Nat)),("members",toJson (3 : Nat))]
  let incomplete := Json.mkObj [("nodeType",toJson "StructDefinition"),("id",toJson (1 : Nat)),
    ("members",toJson [Json.mkObj [("nodeType",toJson "VariableDeclaration")]])]
  unless errorAggregateHasEnum [missing] root && errorAggregateHasEnum [malformed] root &&
      errorAggregateHasEnum [incomplete] root do throw (IO.userError "incomplete struct metadata admitted")
  if errorAggregateHasEnum [empty] root then throw (IO.userError "valid enum-free source type refused")
  : IO Unit)

-- A require constructor cannot recover an erased error by spelling after
-- losing its actual declaration identity.
#eval (do
  let cases ← IO.ofExcept (Json.parse (← IO.FS.readFile "tests/upstream/EnumErrorControls.negative.json"))
  for c in (← IO.ofExcept cases.getArr?) do
    let ast ← IO.ofExcept (c.getObjVal? "ast")
    let C ← IO.ofExcept (Frontend.readContract ast "EnumErrorControls" [] true)
    let some f := C.funs.find? (·.name == "required") | throw (IO.userError "missing require control")
    let .error gap := f.body | throw (IO.userError "invalid constructor identity admitted")
    unless (gap.msg.splitOn "custom error").length > 1 do throw (IO.userError gap.msg)
  : IO Unit)
