import Solidity.Frontend.Testing
import Solidity.Calculus.Close
import Solidity.Calculus.Closers

/-! Exact-width numeric hex arguments at the source-import ABI boundary.
The raw Solidity DSL has no token-width evidence; this module tests the
retained compiler AST before numeric constant normalization. -/
solc_import "../../../tests/abi-0.8.38/HexCall.ast.json" hash 0xc66f97f9464f9fee
  as Imported.AbiHexCall testing

namespace Solidity.Examples.Tactics.AbiHexCall
open Lean Solidity.Frontend

private def literal (text : String) (ty : String := "int_const 43981") : Json :=
  Json.mkObj [("nodeType", .str "Literal"), ("kind", .str "number"),
    ("value", .str text), ("typeDescriptions", Json.mkObj [("typeString", .str ty)])]

private def tuple (xs : List Json) : Json :=
  Json.mkObj [("nodeType", .str "TupleExpression"), ("isInlineArray", .bool false),
    ("components", toJson xs)]

/- Leading zeros determine the source width, not the normalized integer.
Legal digit separators and scalar parentheses preserve the same evidence. -/
#guard
    (abiHexLiteral? 2 (literal "0xabcd")).map Fin.val = some 43981 ∧
    (abiHexLiteral? 2 (literal "0x00ab")).map Fin.val = some 171 ∧
    (abiHexLiteral? 2 (tuple [tuple [literal "0xAb_Cd"]])).map Fin.val = some 43981

/- Equal numeric values do not acquire the same implicit bytes conversion. -/
#guard
    (abiHexLiteral? 2 (literal "43981")).isNone = true ∧
    (abiHexLiteral? 2 (literal "0xab")).isNone = true ∧
    (abiHexLiteral? 2 (literal "0x00abcd")).isNone = true ∧
    (abiHexLiteral? 0 (literal "0x")).isNone = true ∧
    (abiHexLiteral? 33 (literal "0xabcd")).isNone = true

-- Address literals and expressions cannot masquerade as exact-width tokens.
#guard (abiHexLiteral? 20
  (literal "0x0000000000000000000000000000000000000000" "address")).isNone
#guard (abiHexLiteral? 2 (literal "0xabcd" "uint16")).isNone
#guard (abiHexLiteral? 2 (Json.mkObj [("nodeType", .str "BinaryOperation"),
  ("operator", .str "+"), ("leftExpression", literal "0xabcd"),
  ("rightExpression", literal "0"),
  ("typeDescriptions", Json.mkObj [("typeString", .str "int_const 43981")])])).isNone
#guard (abiHexLiteral? 2 (Json.mkObj [("nodeType", .str "Literal"),
  ("kind", .str "number"), ("value", .str "0xabcd")])).isNone
#guard ["0x_abcd", "0xab__cd", "0xabcd_", "0x", "0xgggg", "0Xabcd"].all fun s =>
  (abiHexDigits? s).isNone
#guard (abiUnparen? 0 (literal "0xabcd")).isNone

-- A tuple is one component when wrapped in another tuple. Do not flatten
-- source calls which the compiler rejects. Omitted JSON components fail closed.
#guard (abiCallComponents? (tuple [literal "0xabcd", literal "7"])).map List.length == some 2
#guard (abiCallComponents? (tuple [tuple [literal "0xabcd", literal "7"]])).map List.length == some 1
#guard (abiCallComponents? (tuple [Json.null])).isNone

private def parameters : Json := Json.mkObj [("parameters", toJson [
  Json.mkObj [("typeName", Json.mkObj [("nodeType", .str "ElementaryTypeName"),
    ("name", .str "bytes2")])],
  Json.mkObj [("typeName", Json.mkObj [("nodeType", .str "ElementaryTypeName"),
    ("name", .str "uint256")])]])]

private def declaration (id : Int) (visibility : String) : Json :=
  Json.mkObj [("nodeType", .str "FunctionDefinition"), ("id", toJson id),
    ("visibility", .str visibility), ("parameters", parameters)]

private def pointerDeclaration (visibility : String) : Json :=
  Json.mkObj [("nodeType", .str "VariableDeclaration"), ("id", toJson (23 : Int)),
    ("typeName", Json.mkObj [("nodeType", .str "FunctionTypeName"),
      ("visibility", .str visibility), ("parameterTypes", parameters)])]

private def target (id : Int) : Json :=
  Json.mkObj [("nodeType", .str "Identifier"), ("name", .str "sameName"),
    ("referencedDeclaration", toJson id)]

-- Identity, not a short name, chooses widths. Function variables need an
-- external signature; unretained/internal declarations supply no conversion.
#guard abiCallBytesParams? [declaration 21 "external"] (target 21) == some [some 2, none]
#guard abiCallBytesParams? [declaration 21 "public"] (tuple [target 21]) == some [some 2, none]
#guard abiCallBytesParams? [declaration 21 "external"] (target 22) == none
#guard abiCallBytesParams? [declaration 21 "internal"] (target 21) == none
#guard abiCallBytesParams? [pointerDeclaration "external"] (target 23) == some [some 2, none]
#guard abiCallBytesParams? [pointerDeclaration "internal"] (target 23) == none

#guard ["exactHex", "leadingZero", "mixedHex", "groupedMixed", "pointerHex",
    "selectorArgument", "fullWord", "numericHex", "falseHex"].all fun name =>
  (Imported.AbiHexCall.report.find? (·.name == name)).any fun r =>
    r.admissionChecked && r.status == .elaborated && r.sourceDiagnostic.isNone

/-- Imported source distinguishes exact-width byte alignment from the ordinary
numeric ABI word. The deliberately false source assertion is an execution failure. -/
theorem source_execution :
    (Prog.run (State.init Imported.AbiHexCall) Imported.AbiHexCall.exactHex).isOk = true ∧
    (Prog.run (State.init Imported.AbiHexCall) Imported.AbiHexCall.leadingZero).isOk = true ∧
    (Prog.run (State.init Imported.AbiHexCall) Imported.AbiHexCall.mixedHex).isOk = true ∧
    (Prog.run (State.init Imported.AbiHexCall) Imported.AbiHexCall.groupedMixed).isOk = true ∧
    (Prog.run (State.init Imported.AbiHexCall) Imported.AbiHexCall.pointerHex).isOk = true ∧
    (Prog.run (State.init Imported.AbiHexCall) Imported.AbiHexCall.selectorArgument).isOk = true ∧
    (Prog.run (State.init Imported.AbiHexCall) Imported.AbiHexCall.fullWord).isOk = true ∧
    (Prog.run (State.init Imported.AbiHexCall) Imported.AbiHexCall.numericHex).isOk = true ∧
    (Prog.run (State.init Imported.AbiHexCall) Imported.AbiHexCall.falseHex).isOk = false := by
  decide +kernel

open scoped Scoped
local instance : InContract := ⟨Imported.AbiHexCall⟩

/-- The imported exact-width source assertion holds in every admitted state. -/
theorem exact_hex_valid : ⊨ᶠ spec!{exactHex} := by
  sol_symex
  sol_decide

/-- Matching bytes are required: the false source assertion is not valid. -/
theorem false_hex_invalid : ¬ (⊨ᶠ spec!{falseHex}) :=
  fun h => Modality.afterRunTR_not_panic
    ((h (State.init _)) rfl) (by decide +kernel)

end Solidity.Examples.Tactics.AbiHexCall
