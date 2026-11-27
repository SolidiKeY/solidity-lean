import Solidity.Frontend.SolcJson.YulBuiltinUse
import Solidity.Frontend.SolcJson.YulWords

/-! Small literal controls for JSON grammar, metadata and closed Yul ingress.
Structural acceptance does not authenticate source attachment or execution. -/
namespace Solidity.Examples.FrontendValidation.SolcJson.YulIngress
open Lean Solidity.Frontend.YulJson

private def number : Json := Json.mkObj [
  ("nodeType", .str "YulLiteral"), ("type", .str ""),
  ("kind", .str "number"), ("value", .str "1")]
private def identifier (name : String) : Json :=
  Json.mkObj [("nodeType", .str "YulIdentifier"), ("name", .str name)]
private def typed : Json := Json.mkObj [
  ("nodeType", .str "YulTypedName"), ("type", .str ""), ("name", .str "v")]
private def emptyBlock : Json := Json.mkObj [
  ("nodeType", .str "YulBlock"), ("statements", .arr #[])]
private def defaultCase : Json := Json.mkObj [
  ("nodeType", .str "YulCase"), ("value", .str "default"), ("body", emptyBlock)]
private def env : Solidity.Yul.ExprEnv [] [] 0 := ⟨[], [], []⟩
private def table : DeclarationTable [] := ⟨[], by decide⟩
private def input : MetadataWords.Input table [] :=
  ⟨⟨by intro name present; cases present⟩⟩
private def assembly (safe : Bool) : Json := Json.mkObj [
  ("nodeType", .str "InlineAssembly"), ("evmVersion", .str "osaka"),
  ("externalReferences", .arr #[]),
  ("flags", .arr (if safe then #[.str "memory-safe"] else #[])),
  ("src", .str "0:0:0"), ("AST", emptyBlock)]
private def rawBlock : String := r#"{"nodeType":"YulBlock","statements":[]}"#
private def rawNumber : String :=
  r#"{"nodeType":"YulLiteral","type":"","kind":"number","value":"1"}"#
private def rawSafe : String :=
  r#"{"nodeType":"InlineAssembly","evmVersion":"osaka","externalReferences":[],"flags":["memory-safe"],"src":"0:0:0","AST":{"nodeType":"YulBlock","statements":[]}}"#
private def rawUnsafe : String :=
  r#"{"nodeType":"InlineAssembly","evmVersion":"osaka","externalReferences":[],"flags":[],"src":"0:0:0","AST":{"nodeType":"YulBlock","statements":[]}}"#

#guard (field (Json.mkObj [("x", .bool true)]) "x").isOk
#guard (field (Json.mkObj []) "x").toOption.isNone
#guard (string (Json.mkObj [("x", .str "v")]) "x").toOption == some "v"
#guard (string (Json.mkObj [("x", .bool true)]) "x").toOption.isNone
#guard (array (Json.mkObj [("x", .arr #[])]) "x").isOk
#guard (array (Json.mkObj [("x", .str "v")]) "x").toOption.isNone
#guard (requireNode number "YulLiteral").isOk
#guard (requireNode number "YulIdentifier").toOption.isNone
#guard (emptyAnnotation number).isOk
#guard (emptyAnnotation (number.setObjVal! "type" (.str "u256"))).toOption.isNone
#guard (finishLiteral (.dec 1)).isOk
#guard (finishLiteral (.hexStr [
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])).toOption.isNone
#guard (literal number).isOk
#guard (literal (number.setObjVal! "value" (.str "bad"))).toOption.isNone
#guard (identifierPath (identifier "v.slot")).isOk
#guard (identifierPath (identifier "v..slot")).toOption.isNone
#guard (functionName (identifier "f")).toOption == some "f"
#guard (functionName (identifier "f.g")).toOption.isNone
#guard (expressionAux 8 number).isOk
#guard (expressionAux 0 number).toOption.isNone
#guard (expression 8 number).isOk
#guard (expression 8 .null).toOption.isNone
#guard (checkExpression env 8 number).isOk
#guard (checkExpression env 8 (identifier "missing")).toOption.isNone
#guard (checkExpressionText env rawNumber).isOk
#guard (checkExpressionText env "{").toOption.isNone
#guard (typedName typed).toOption == some "v"
#guard (typedName (typed.setObjVal! "name" (.str "if"))).toOption.isNone
#guard (names (Json.mkObj [("variables", .arr #[typed])]) "variables").isOk
#guard (names (Json.mkObj [("variables", .arr #[.null])]) "variables").toOption.isNone
#guard (optionalNames (Json.mkObj []) "parameters").isOk
#guard (optionalNames (Json.mkObj [("parameters", .bool true)]) "parameters").toOption.isNone
#guard (switchCases (fun _ => .ok .nil) [defaultCase] []).isOk
#guard (switchCases (fun _ => .ok .nil) [defaultCase, defaultCase] []).toOption.isNone
#guard (blockAux 1 emptyBlock).isOk
#guard (blockAux 0 emptyBlock).toOption.isNone
#guard (statementAux 1 (Json.mkObj [("nodeType", .str "YulLeave")])).isOk
#guard (statementAux 0 (Json.mkObj [("nodeType", .str "YulLeave")])).toOption.isNone
#guard (parseBlock 8 emptyBlock).isOk
#guard (parseBlock 0 emptyBlock).toOption.isNone
#guard (parseBlockText rawBlock).isOk
#guard (parseBlockText "{").toOption.isNone
#guard (checkBlockShape 8 emptyBlock).isOk
#guard (checkBlockShape 0 emptyBlock).toOption.isNone
#guard (checkBlockShapeText rawBlock).isOk
#guard (checkBlockShapeText "{}").toOption.isNone

#guard decimal "12" == some 12
#guard (decimal "1_2").isNone
#guard (sourceSpan "0:1:-1").isOk
#guard (sourceSpan "0:-1:0").toOption.isNone
#guard (natural (Json.mkObj [("n", toJson (2 : Nat))]) "n").toOption == some 2
#guard (natural (Json.mkObj [("n", .str "2")]) "n").toOption.isNone
#guard (boolean (Json.mkObj [("b", .bool true)]) "b").toOption == some true
#guard (boolean (Json.mkObj [("b", .str "true")]) "b").toOption.isNone
#guard (references table (assembly true)).isOk
#guard (references table ((assembly true).setObjVal!
  "externalReferences" (.arr #[.null]))).toOption.isNone
#guard (metadata table (assembly true)).isOk
#guard (metadata table ((assembly true).setObjVal!
  "evmVersion" (.str "unknown"))).toOption.isNone
#guard spaceTab 32
#guard !spaceTab 0
#guard docWhitespace 13
#guard !docWhitespace 0
#guard tagSeparator 10
#guard !tagSeparator 13
#guard (docTagsAux 8 (bytes "@solidity memory-safe-assembly") [] none).isOk
#guard (docTagsAux 0 (bytes "@solidity memory-safe-assembly") [] none).toOption.isNone
#guard (checkMetadataSafety ["memory-safe"] none).isOk
#guard (checkMetadataSafety [] none).toOption.isNone
-- These also execute documentationTags on positive/negative safety input.
-- Its direct negative-case interpretation is pending F1B-DOC-TOTAL.
#guard (checkMetadataSafety [] (some "@solidity memory-safe-assembly")).isOk
#guard (checkMetadataSafety [] (some "@solidity other")).toOption.isNone

#guard (Words.check [] 8 (assembly true)).isOk
#guard (Words.check [] 8 (assembly false)).toOption.isNone
#guard (Words.checkText [] rawSafe).isOk
#guard (Words.checkText [] rawUnsafe).toOption.isNone
#guard (ScopedJson.check input [] [] 8 (assembly true)).isOk
#guard (ScopedJson.check input [] [] 8 (assembly false)).toOption.isNone
#guard (ScopedJson.checkText input [] [] rawSafe).isOk
#guard (ScopedJson.checkText input [] [] rawUnsafe).toOption.isNone
#guard (ForwardJson.check input [] [] 8 (assembly true)).isOk
#guard (ForwardJson.check input [] [] 8 (assembly false)).toOption.isNone
#guard (ForwardJson.checkText input [] [] rawSafe).isOk
#guard (ForwardJson.checkText input [] [] rawUnsafe).toOption.isNone
#guard (BuiltinGuard.checkJson input [] [] 8 (assembly true)).isOk
#guard (BuiltinGuard.checkJson input [] [] 8 (assembly false)).toOption.isNone
#guard (BuiltinGuard.checkJsonText input [] [] rawSafe).isOk
#guard (BuiltinGuard.checkJsonText input [] [] rawUnsafe).toOption.isNone
#guard (ScopedParse.check .closed .A [] [] none (bytes "assembly (\"memory-safe\") {}")).isOk
#guard (ScopedParse.check .closed .A [] [] none (bytes "assembly {}")).toOption.isNone
#guard (MetadataWords.check input [] [] none (bytes "assembly (\"memory-safe\") {}")).isOk
#guard (MetadataWords.check input [] [] none (bytes "assembly {}")).toOption.isNone
#guard (BuiltinGuard.parse .closed .A [] [] none (bytes "assembly (\"memory-safe\") {}")).isOk
#guard (BuiltinGuard.parse .closed .A [] [] none (bytes "assembly {}")).toOption.isNone

end Solidity.Examples.FrontendValidation.SolcJson.YulIngress
