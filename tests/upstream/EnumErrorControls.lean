import Solidity.Tools.Upstream
open Solidity Solidity.Frontend Lean
solc_import "EnumErrorControls.legacy.ast.json" hash 0x0513eb33a4904892 as Group10.EnumLegacy.EnumErrorControls testing
solc_import "EnumErrorControls.viaIR.ast.json" hash 0xfbe354de09729ef5 as Group10.EnumIR.EnumErrorControls testing
example : Group10.EnumLegacy.EnumErrorControls.report.length = 3 := by decide +kernel
example : Group10.EnumIR.EnumErrorControls.report.length = 3 := by decide +kernel
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
