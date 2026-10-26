import Solidity.Frontend.Testing
import Solidity.Tools.Run

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
-- Finite dispatch follows the modifier's dynamically called target body.
#guard (row "modifierDispatch").any fun r =>
  r.status == .excluded && (r.sourceDiagnostic.map (·.name)) == some `solidity.blockField.number
-- Admission accepts the typed address projection; its assertion is false
-- (packed addresses occupy 20 bytes), so this makes no proof claim.
#guard (row "storedFunctionKind").any fun r =>
  r.status == .elaborated && r.sourceDiagnostic.isNone
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

-- Declaration identity, rather than the function-shaped compiler type or
-- a matching short name, distinguishes static error/event selector metadata.
run_cmd do
  let fixture ← ofExcept (Json.parse (← IO.FS.readFile "tests/solc/SourceAdmission.ast.json"))
  let provenance ← ofExcept (Source.read fixture (← ofExcept (fixture.getObjVal? "ast")))
  let metadata ← ofExcept (Json.parse (← IO.FS.readFile "tests/solc/DeclarationMetadata.ast.json"))
  let ast ← ofExcept (metadata.getObjVal? "ast")
  let nodes := J.nodes ast
  let declaration (receiver : Json) := (J.ref? receiver).bind fun id =>
    nodes.find? (J.id? · == some id)
  let members := nodes.filter fun node => J.kind node == "MemberAccess" &&
    J.str? node "memberName" == some "selector"
  let declared := members.filter fun node =>
    ((J.opt node "expression").bind declaration).any fun d =>
      ["ErrorDefinition", "EventDefinition"].contains (J.kind d)
  unless declared.length == 3 do
    throwError "expected unqualified/qualified errors and a non-anonymous event selector"
  let scan (node : Json) : Source.ScopeScan :=
    Admission.scan ast provenance {entry := node, evaluatedRoots := [node]}
  let memberGap (node : Json) (feature : Solidity.Language.Feature) : Elab.Command.CommandElabM Unit := do
    let diagnostic : Option Source.Diagnostic := (scan node).diagnostic?
    unless (diagnostic.map (·.name)) == some `solidity.functionMemberKind &&
        (diagnostic.map (·.kind)) == some .missingImplementation &&
        (diagnostic.bind (·.feature)) == some feature do
      throwError "function-member admission lost its typed ABI boundary: {repr diagnostic}"
  for node in declared do
    unless (scan node).diagnostic?.isNone do
      throwError "a resolved declaration selector was refused: {repr (scan node).diagnostic?}"
    let receiver ← ofExcept (node.getObjVal? "expression")
    unless (← Lean.ofExcept ((declarationMetadata nodes receiver "selector").mapError (·.msg))).isSome do
      throwError "an admitted declaration selector lacks checked metadata"
    memberGap (put node "memberName" (.str "address")) .functionAddress
    -- Missing, malformed and unresolved IDs must not acquire a name-based
    -- metadata exemption, even with the original declaration's spelling.
    for changed in [put receiver "referencedDeclaration" .null,
        put receiver "referencedDeclaration" (.str "64"),
        put receiver "referencedDeclaration" (toJson (999999 : Int)),
        put receiver "referencedDeclaration" (toJson (-1 : Int))] do
      memberGap (put node "expression" changed) .functionSelector
      unless (declarationMetadata nodes changed "selector").toOption == some none do
        throwError "unresolved selector metadata acquired a literal"
  let some stored := members.find? fun node =>
      ((J.opt node "expression").bind declaration).any (J.kind · == "VariableDeclaration")
    | throwError "expected a stored function selector in the metadata fixture"
  -- Stable stored external projections are now admitted by the upstream
  -- checked ABI-kind path, but must not fold as declaration metadata.
  unless storedFunctionMemberType? stored == some "bytes4" &&
      (scan stored).diagnostic?.isNone do
    throwError "a typed stored selector lost its checked projection admission"
  let storedReceiver ← ofExcept (stored.getObjVal? "expression")
  let some storedAddress := nodes.find? fun node =>
      J.kind node == "MemberAccess" && J.str? node "memberName" == some "address" &&
        ((J.opt node "expression").bind J.ref?) == J.ref? storedReceiver
    | throwError "expected the same stored function's address projection"
  unless storedFunctionMemberType? storedAddress == some "address" &&
      (scan storedAddress).diagnostic?.isNone do
    throwError "a typed stored address lost its checked projection admission"
  let renamed := put storedReceiver "name" (.str "Problem")
  let renamedMember := put stored "expression" renamed
  unless (scan renamedMember).diagnostic?.isNone do
    throwError "a renamed stored selector lost its checked projection admission"
  unless (declarationMetadata nodes renamed "selector").toOption == some none do
    throwError "a stored value was mistaken for a same-named error declaration"
  unless ((expr renamedMember).run' { declarations := nodes }).toOption ==
      some "bytes4(«Problem».selector)" do
    throwError "a stored selector lost its ABI kind or acquired a metadata literal"
  let some directFunction := members.find? fun node =>
      ((J.opt node "expression").bind declaration).any (J.kind · == "FunctionDefinition")
    | throwError "expected a direct function declaration selector"
  unless (scan directFunction).diagnostic?.isNone do
    throwError "direct function metadata lost its existing admission"


/-- Projection syntax is typed before the native function-value erasure. -/
private def functionValue (kind : String := "t_function_external_pure$_t_uint256_$returns$_t_uint256_$") : Json :=
  Json.mkObj [("nodeType", .str "Identifier"), ("name", .str "h"),
    ("referencedDeclaration", toJson (123 : Int)),
    ("typeDescriptions", Json.mkObj [("typeString", .str "function (uint256) pure external returns (uint256)"),
      ("typeIdentifier", .str kind)])]

private def functionMember (member result : String) (receiver : Json := functionValue) : Json :=
  Json.mkObj [("nodeType", .str "MemberAccess"), ("memberName", .str member),
    ("expression", receiver), ("typeDescriptions", Json.mkObj [("typeString", .str result)])]

#guard storedFunctionMemberType? (functionMember "address" "address") == some "address"
#guard storedFunctionMemberType? (functionMember "selector" "bytes4") == some "bytes4"
#guard ((expr (functionMember "address" "address")).run' default).toOption ==
  some "address(«h».address)"
#guard ((expr (functionMember "selector" "bytes4")).run' default).toOption ==
  some "bytes4(«h».selector)"
-- The projection stays in its lazy expression position: no source prelude is
-- introduced while adding the ABI-kind cast.
#guard ((expr (functionMember "selector" "bytes4")).run default).toOption.any fun (_, state) =>
  state.pre.isEmpty && state.fresh == 0
-- Normalized compiler fixtures retain typeString but omit typeIdentifier.
#guard storedFunctionMemberType? (functionMember "address" "address"
  (put functionValue "typeDescriptions" (Json.mkObj [("typeString", .str "function () external")])) ) ==
  some "address"
-- A nested external parameter does not make its enclosing function external.
#guard (storedFunctionMemberType? (functionMember "address" "address"
  (put functionValue "typeDescriptions" (Json.mkObj
    [("typeString", .str "function (function () external) internal")])))).isNone
-- Metadata disagreement and internal functions remain refused.
#guard (storedFunctionMemberType? (functionMember "selector" "uint256")).isNone
#guard (storedFunctionMemberType? (functionMember "address" "address"
  (functionValue "t_function_internal_pure$_t_uint256_$returns$_t_uint256_$"))).isNone
-- Calling a producer could call back or change storage. The selector lowering
-- must never duplicate it, even under a conditional or short-circuit operator.
#guard (storedFunctionMemberType? (functionMember "selector" "bytes4"
  (put functionValue "nodeType" (.str "FunctionCall")))).isNone

/-- `h.address` is packed as 20 bytes, `h.selector` as four left-aligned
bytes. Casts supplied by the source reader preserve both kinds at ABI sites. -/
def FunctionMemberKinds : Contract := contract!{
  function f(uint x) returns (uint y) { y = x; }
  function layout() returns (bool ok) {
    function (uint) external returns (uint) h = this.f;
    bytes memory ap = abi.encodePacked(address(h.address));
    bytes memory sp = abi.encodePacked(bytes4(h.selector));
    bytes memory aw = abi.encode(address(h.address));
    bytes memory sw = abi.encode(bytes4(h.selector));
    bytes memory sc = bytes.concat(bytes4(h.selector));
    ok = ap.length == 20 && sp.length == 4 && aw.length == 32 && sw.length == 32 &&
      sc.length == 4 && aw[12] == ap[0] && aw[31] == ap[19] &&
      sw[0] == sp[0] && sw[1] == sp[1] && sw[2] == sp[2] && sw[3] == sp[3] &&
      uint8(sw[4]) == 0 && uint8(sw[31]) == 0 && sc[0] == sp[0];
  }
}

/-- info: ok
returns true -/
#guard_msgs in #run FunctionMemberKinds.layout()


/- The core intentionally admits wider native transaction fields. Source
obligations restrict their initial domain instead of erasing address casts. -/
private def selfState (a : PrimTy.uint.Denote) : State FunctionMemberKinds [] :=
  { State.init FunctionMemberKinds with tx := { selfAddress := a } }

set_option maxRecDepth 2048 in
private theorem boundSelf_iff {C : Contract} (σ : State C []) :
    holds σ (Problem.callPre C [] false [] false [] true) ↔
      σ.tx.selfAddress.val < 2^160 := by
  change ((some (decide (σ.tx.selfAddress.val < 2^160)) : Option Bool) = some true) ↔ _
  simp only [Option.some.injEq, decide_eq_true_eq]

-- Existing direct callPre callers keep their previous (unbounded) meaning.
example : Problem.callPre FunctionMemberKinds [] false [] = .tt := rfl

example : holds (selfState ⟨0, by decide +kernel⟩)
    (Problem.callPre FunctionMemberKinds [] false [] false [] true) := by
  rw [boundSelf_iff]
  decide +kernel
example : holds (selfState ⟨2^160 - 1, by decide +kernel⟩)
    (Problem.callPre FunctionMemberKinds [] false [] false [] true) := by
  rw [boundSelf_iff]
  decide +kernel
example : ¬ holds (selfState ⟨2^160, by decide +kernel⟩)
    (Problem.callPre FunctionMemberKinds [] false [] false [] true) := by
  rw [boundSelf_iff]
  decide +kernel
example : ¬ holds (selfState ⟨2^200, by decide +kernel⟩)
    (Problem.callPre FunctionMemberKinds [] false [] false [] true) := by
  rw [boundSelf_iff]
  decide +kernel

-- This reproduces the source reader's genuine address cast. The native
-- out-of-EVM state is a countermodel to omitting the source input premise.
private def projectedAddress := sol[FunctionMemberKinds]{
  function (uint) external returns (uint) h = this.f;
  assert(address(h.address) == address(this));
}
example : (Prog.run (selfState ⟨2^200, by decide +kernel⟩) projectedAddress).halt? =
    some .panic := by decide +kernel
example : (Prog.run (selfState ⟨2^160 - 1, by decide +kernel⟩) projectedAddress).isOk =
    true := by decide +kernel

-- Even a function with no address read receives the explicit EVM domain;
-- hidden callees and synthesized dispatch bodies cannot evade the premise.
run_cmd do
  let some r := row "clean" | throwError "missing clean source row"
  let .ok (some φ) := obligation (← getEnv) ``Imported.SourceAdmission r
    | throwError "missing clean obligation"
  unless (φ.find? fun e => e.isAppOfArity ``Problem.callPre 7 &&
      e.appArg! == Lean.toExpr true).isSome do
    throwError "source obligation omitted the EVM address premise"

/-- error: self address must fit 160 bits -/
#guard_msgs in
solc_scoped_problems Imported.SourceAdmission decl self 1461501637330902918203684832716283019655932542976

-- The lower-level obligation API also rejects an impossible self equality.
run_cmd do
  let some r := row "clean" | throwError "missing clean source row"
  match obligation (← getEnv) ``Imported.SourceAdmission r (some (2^160)) with
  | .error "self address must fit 160 bits" => pure ()
  | _ => throwError "out-of-EVM self address reached the source obligation"

end Solidity.Examples.Tactics.SourceAdmissionImport
