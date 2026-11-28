import Solidity.Frontend.SolcJson.CallMetadataControls
import Solidity.Frontend.SolcJson.CallMetadataPath

/-! Synthetic structural metadata controls, not authenticated compiler output.
The provenance reader checks fields and pins; these literals make no claim
that a compiler produced this AST or that it corresponds to the source hash. -/
namespace Solidity.Examples.FrontendValidation.SolcJson.CallMetadata
open Lean Solidity.Frontend.CallMetadata

private def declarationNode : Json := Json.mkObj [
  ("id", toJson (1 : Int)), ("nodeType", .str "FunctionDefinition"),
  ("kind", .str "function"), ("name", .str "f"),
  ("visibility", .str "external"), ("stateMutability", .str "pure"),
  ("parameters", Json.mkObj [("parameters", .arr #[])])]

private def callNode : Json := Json.mkObj [
  ("id", toJson (2 : Int)), ("nodeType", .str "FunctionCall"),
  ("kind", .str "functionCall"), ("arguments", .arr #[]),
  ("expression", Json.mkObj [
    ("nodeType", .str "MemberAccess"), ("memberName", .str "f"),
    ("referencedDeclaration", toJson (1 : Int)),
    ("typeDescriptions", Json.mkObj [
      ("typeString", .str "function () pure external")]),
    ("expression", Json.mkObj [("typeDescriptions", Json.mkObj [
      ("typeString", .str "contract C")])])])]

private def astRoot : Json := Json.mkObj [
  ("nodeType", .str "SourceUnit"), ("nodes", .arr #[declarationNode, callNode])]

private def profileFixture (target : String) (modern : Bool := true) : Json :=
  Json.mkObj [("ast", astRoot), ("header", Json.mkObj ([
    ("solcVersion", .str "0.8.38+commit.1835d247.Emscripten.clang"),
    ("sourceSha256", .str
      "0000000000000000000000000000000000000000000000000000000000000000"),
    ("solkeyCommit", .str ""), ("source", .str "C.sol")] ++
    if modern then [
      ("provenanceVersion", toJson (1 : Nat)),
      ("compilerFile", .str "soljson-v0.8.38+commit.1835d247.js"),
      ("compilerSha256", .str
        "6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390"),
      ("validationStage", .str "analysis"), ("acceptedPragmas", .arr #[]),
      ("settings", Json.mkObj [
        ("viaIR", .bool false), ("evmVersion", .str target),
        ("optimizer", Json.mkObj [("enabled", .bool false), ("runs", toJson (0 : Nat))]),
        ("libraries", Json.mkObj []), ("remappings", .arr #[]),
        ("outputSelection", Json.mkObj [("*", Json.mkObj [("", .arr #[.str "ast"])])])])]
    else []))]

private def profile? (target : String := "osaka") (modern : Bool := true) : Option Profile :=
  (readProfile (profileFixture target modern)).toOption

#guard (readProfile (profileFixture "osaka")).isOk
#guard (readProfile (Json.mkObj [])).toOption.isNone
#guard (readProfile (profileFixture "osaka" false)).isOk
#guard (profile? "osaka").map staticTarget? == some (some true)
#guard (profile? "osaka" false).map staticTarget? == some none

#guard (outerQualifiers? "function () pure external").isSome
#guard (outerQualifiers? "function () internal").isNone
#guard (inspect (profile? "osaka") [declarationNode] callNode).isOk
#guard (inspect (profile? "osaka") [] callNode).toOption.isNone
#guard (check (profile? "osaka") [declarationNode] callNode).isOk
#guard (check none [declarationNode] callNode).toOption.isNone
#guard ((inspect (profile? "osaka") [declarationNode] callNode).toOption.map
  Info.isStatic) == some true
#guard ((inspect (profile? "homestead") [declarationNode] callNode).toOption.map
  Info.isStatic) == some false

#guard (Controls.profile (profileFixture "osaka")).isSome
#guard (Controls.profile .null).isNone
#guard (Controls.summary (profile? "osaka") [declarationNode] callNode).toOption ==
  some (true, 2, 1)
#guard (Controls.summary (profile? "osaka") [] callNode).toOption.isNone

private def declarationPath : Path := [.field "nodes", .index 0]
private def callPath : Path := [.field "nodes", .index 1]
private def missingPath : Path := [.field "nodes", .index 9]

#guard walk astRoot callPath == some callNode
#guard (walk astRoot missingPath).isNone
#guard ((locate astRoot callPath).map (·.node)) == some callNode
#guard (locate astRoot missingPath).isNone
#guard ((locate astRoot []).bind fun parent => parent.descend callPath).isSome
#guard ((locate astRoot []).bind fun parent => parent.descend missingPath).isNone
#guard (locateDeclarations astRoot [declarationPath]).isOk
#guard (locateDeclarations astRoot [missingPath]).toOption.isNone

private def attachAt (path : Path) : Option (Option Bool) :=
  (profile? "osaka").map fun p =>
    (locate p.ast declarationPath).bind fun declaration =>
      (locate p.ast path).map fun call => (attach p [declaration] call).isOk

-- Both paths resolve in each case; only the metadata call shape differs.
#guard attachAt callPath == some (some true)
#guard attachAt declarationPath == some (some false)
#guard ((profile? "osaka").map fun p =>
  (attachPaths p [declarationPath] callPath).isOk) == some true
#guard ((profile? "osaka").map fun p =>
  (attachPaths p [declarationPath] missingPath).isOk) == some false

end Solidity.Examples.FrontendValidation.SolcJson.CallMetadata
