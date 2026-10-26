import Solidity.Frontend.Testing

/-! Admission distinguishes unused declarations, executed bodies, specifications,
compiler modes, malformed metadata and deliberate profile exclusions. -/
solc_import "../../../tests/solc/SourceAdmission.ast.json" hash 0x8d25db399f7c6231
  as Imported.SourceAdmission testing
solc_import "../../../tests/solc/SourceAdmission.ast.json" hash 0x8d25db399f7c6231
  as Imported.PaymentFallback testing
solc_import "../../../tests/solc/SourceAdmission.ast.json" hash 0x8d25db399f7c6231
  as Imported.ConstructorArguments testing
solc_import "../../../tests/solc/SourceAdmission.ast.json" hash 0x8d25db399f7c6231
  as Imported.InvariantOwner testing
solc_import "../../../tests/solc/SourceAdmission.ast.json" hash 0x8d25db399f7c6231
  as Imported.InheritedPayment testing
solc_import "../../../tests/solc/SourceAdmission.ast.json" hash 0x8d25db399f7c6231
  as Imported.VirtualOwner testing
solc_import "../../../tests/solc/SourceAdmission.ast.json" hash 0x8d25db399f7c6231
  as Imported.LoopOwner testing
solc_import "../../../tests/solc/SourceAdmission.ast.json" hash 0x8d25db399f7c6231
  as Imported.InvariantParameter testing
solc_import "../../../tests/solc/SourceAdmission.ast.json" hash 0x8d25db399f7c6231
  as Imported.ConstructorLoopOwner testing

solc_import "../../../tests/solc/SourceCoder.ast.json" hash 0xd8dc007becc019e4
  as Imported.SourceCoder testing
solc_import "../../../tests/solc/SourceCoderIR.ast.json" hash 0xcc2d282d719f2d57
  as Imported.IR.SourceCoder testing

namespace Solidity.Examples.Tactics.SourceAdmissionImport
open Lean Solidity.Frontend

private def row (name : String) : Option ImportRow :=
  Imported.SourceAdmission.report.find? (·.name == name)

#guard ["clean", "selectorOnly", "quantified", "rethrow", "quantifiedLoop"].all fun name =>
  (row name).any fun r => r.admissionChecked && r.status == .elaborated && r.sourceDiagnostic.isNone
#guard ["constructor", "bad", "calledBad", "castSelf", "aliasSelf", "modified",
    "emitted", "encoded", "specified", "loopExcluded"].all fun name =>
  (row name).any fun r => r.status == .excluded &&
    (r.sourceDiagnostic.map (·.name)) == some `solidity.blockField.number
#guard (row "badRethrow").any fun r =>
  (r.sourceDiagnostic.map (·.name)) == some `solidity.inlineAssembly
#guard (row "quoted").any fun r => (r.sourceDiagnostic.map (·.kind)) != some .excluded
#guard (Imported.PaymentFallback.report.find? (·.name == "pay")).any fun r =>
  r.status == .unsupported && (r.sourceDiagnostic.map (·.name)) == some `solidity.selfPayment
#guard (row "modifierDispatch").any fun r =>
  r.status == .unsupported && (r.sourceDiagnostic.map (·.name)) == some `solidity.functionDispatch
#guard (row "storedFunctionKind").any fun r =>
  r.status == .unsupported && (r.sourceDiagnostic.map (·.name)) == some `solidity.functionMemberKind
#guard (Imported.ConstructorArguments.report.find? (·.name == "clean")).any (·.status == .elaborated)
#guard (Imported.InvariantOwner.report.find? (·.name == "clean")).any fun r =>
  (r.sourceDiagnostic.map (·.name)) == some `solidity.rawCalldata
#guard (Imported.InheritedPayment.report.find? (·.name == "pay")).any fun r =>
  (r.sourceDiagnostic.map (·.name)) == some `solidity.selfPayment
#guard (Imported.VirtualOwner.report.find? (·.name == "callBaseType")).any fun r =>
  (r.sourceDiagnostic.map (·.name)) == some `solidity.blockField.number
#guard (Imported.LoopOwner.report.find? (·.name == "callLoop")).any fun r =>
  (r.sourceDiagnostic.map (·.name)) == some `solidity.lexicalSpecification
#guard (Imported.InvariantParameter.report.find? (·.name == "parameterShadow")).any fun r =>
  (r.sourceDiagnostic.map (·.name)) == some `solidity.lexicalSpecification
#guard (Imported.ConstructorLoopOwner.report.find? (·.name == "constructor")).any fun r =>
  (r.sourceDiagnostic.map (·.name)) == some `solidity.blockField.number

#guard Imported.SourceCoder.report.all fun r =>
  r.status == .unsupported && (r.sourceDiagnostic.map (·.name)) == some `solidity.abiCoderV1
#guard Imported.IR.SourceCoder.report.all (·.status == .elaborated)
#guard Imported.IR.SourceCoder.evalOrder.binaryLeftToRight
#guard Imported.IR.SourceCoder.report.provenance.requestedCoder == .v1
#guard Imported.IR.SourceCoder.report.provenance.effectiveCoder == some .v2

private def put (json : Json) (key : String) (value : Json) : Json :=
  Json.mkObj ((key, value) :: ((json.getObj?.toOption.map (·.toList)).getD []).filter (·.1 != key))

run_cmd do
  let fixture ← ofExcept (Json.parse (← IO.FS.readFile "tests/solc/SourceAdmission.ast.json"))
  let ast ← ofExcept (fixture.getObjVal? "ast")
  let provenance ← ofExcept (Source.read fixture ast)
  let check (node : Json) (expected : Source.DiagnosticKind) := do
    let result := Admission.scan ast provenance { entry := node, evaluatedRoots := [node] }
    unless (result.diagnostic?.map (·.kind)) == some expected do
      throwError "source admission did not reject {node.compress}: {repr result.diagnostic?}"
  check (Json.mkObj [("nodeType", .str "FutureSyntax")]) .unknownNode
  check (Json.mkObj [("nodeType", .bool true)]) .unknownNode
  check (Json.mkObj [("nodeType", .str "Conditional")]) .invalidAst
  check (Json.mkObj [("nodeType", .str "UnaryOperation"), ("operator", .str "++"),
    ("typeDescriptions", Json.mkObj [("typeString", .str "uint256")])]) .invalidAst
  check (Json.mkObj [("nodeType", .str "Identifier"), ("name", .str "missing"),
    ("referencedDeclaration", toJson (999999 : Int)),
    ("typeDescriptions", Json.mkObj [("typeString", .str "uint256")])]) .unresolvedReference
  let header ← ofExcept (fixture.getObjVal? "header")
  let badHeader := put header "compilerSha256" (.str (String.mk (List.replicate 64 '0')))
  unless !(Source.read (put fixture "header" badHeader) ast).isOk do
    throwError "accepted a compiler digest mismatch"
  let downgraded := Json.mkObj ((header.getObj?.toOption.map (·.toList)).getD [] |>.filter (·.1 != "provenanceVersion"))
  unless !(Source.read (put fixture "header" downgraded) ast).isOk do
    throwError "modern metadata silently became a legacy fixture"

end Solidity.Examples.Tactics.SourceAdmissionImport
