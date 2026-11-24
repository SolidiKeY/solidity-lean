import Solidity.Examples.ExecutableGoalBinding
import Solidity.Examples.ExecutableRequestData
import Solidity.Frontend.ExecutableCounterexampleMetadataV2

/-! Synthetic named-theorem candidate preparation and true/false executable checks.
No authenticated source certificate or span is admitted here. -/
open Lean Elab Command Meta Solidity Solidity.Tools
namespace ExecutableBindingControls

/- Synthetic NAMED retained proof, not one of the four source certificates. -/
theorem preparationCertificate : ¬ Fml.Valid (.ff : Fml C []) :=
  Fml.not_valid_of_eval3Peel candidate.sourceValuesV1 (candidate.tstate C)
    (show Fml.eval3Peel (poolDom candidate.argInts) candidate.sourceValuesV1
      (candidate.tstate C) (.ff : Fml C []) = .ff from rfl)

def otherLayoutCandidate : Cand quotationContract :=
  { st := SFields.dflt quotationContract.vars, args := [] }
theorem preparationOtherLayout : ¬ Fml.Valid (.ff : Fml quotationContract []) :=
  Fml.not_valid_of_eval3Peel otherLayoutCandidate.sourceValuesV1 (otherLayoutCandidate.tstate quotationContract)
    (show Fml.eval3Peel (poolDom otherLayoutCandidate.argInts) otherLayoutCandidate.sourceValuesV1
      (otherLayoutCandidate.tstate quotationContract) (.ff : Fml quotationContract []) = .ff from rfl)
theorem preparationWrongShape : True := True.intro

def freshSpellingCandidate : Cand C := { candidate with args := [("se1", .bool true)] }
theorem preparationFreshSpelling : ¬ Fml.Valid (.ff : Fml C []) :=
  Fml.not_valid_of_eval3Peel freshSpellingCandidate.sourceValuesV1 (freshSpellingCandidate.tstate C)
    (show Fml.eval3Peel (poolDom freshSpellingCandidate.argInts) freshSpellingCandidate.sourceValuesV1
      (freshSpellingCandidate.tstate C) (.ff : Fml C []) = .ff from rfl)
def checkCandidatePreparation : CommandElabM Unit := do
  if (← getOptions).getBool `debug.skipKernelTC false then
    throwError "kernel checking must be enabled"
  let .ok fixture := invocationFixture | throwError "invocation fixture JSON"
  let request := fixture.setObjVal! "listing" (toJson false)
  let root := `ExecutableBindingControls.invocationPrimary
  let .ok report ← Solidity.Frontend.ExecutableMetadataV2.Internal.retainInvocationV2 root request
    | throwError "first invocation failed"
  let .ok rows := report.getArr? | throwError "missing invocation rows"
  unless rows.size == 2 do throwError "invocation lost rows"
  for (id, functionName, index) in [(1, "first", 0), (2, "second", 1)] do
    let some selected ← Solidity.Frontend.ExecutableMetadataV2.Internal.selectedInvocationGoalV2?
      root request id functionName | throwError "actual retained terminal goal missing"
    unless selected.captureIndex == index && selected.goal.sourceId == id &&
        selected.goal.functionName == functionName && selected.goal.retryRequired? == some false do
      throwError "actual retained terminal goal changed identity"
  for (id, functionName) in [(1, "second"), (2, "first"), (99, "first")] do
    if (← Solidity.Frontend.ExecutableMetadataV2.Internal.selectedInvocationGoalV2?
        root request id functionName).isSome then throwError "foreign terminal goal selected"
  if (← Solidity.Frontend.ExecutableMetadataV2.Internal.selectedInvocationGoalV2?
      root fixture 1 "first").isSome then throwError "changed request selected"
  let preparationEnv ← getEnv
  let .ok prepared ← Solidity.Frontend.ExecutableMetadataV2.Internal.prepareRetainedCandidateV2
    root request 1 "first" ``preparationCertificate Json.null
    | throwError "named candidate preparation failed"
  unless prepared.selection.captureIndex == 0 && prepared.certificateDeclaration == ``preparationCertificate &&
      prepared.imported.original.report == Json.null do throwError "preparation changed retained identity"
  unless ((← getEnv).constants.toList.map Prod.fst) == (preparationEnv.constants.toList.map Prod.fst) do
    throwError "temporary candidate preparation declarations leaked"
  for (name, reason) in [(``preparationOtherLayout, "storage layout mismatch"),
      (``preparationWrongShape, "retained theorem goal shape refused"),
      (``C, "retained theorem unavailable"), (`MissingPreparationCertificate, "retained theorem unavailable")] do
    let result ← Solidity.Frontend.ExecutableMetadataV2.Internal.prepareRetainedCandidateV2
      root request 1 "first" name (Json.mkObj [("certified", toJson true)])
    match result with
    | .error actual => unless actual == reason do throwError "unrelated preparation refusal: {actual}"
    | .ok _ => throwError "invalid retained candidate preparation accepted"
  let .error wrongRequestReason ← Solidity.Frontend.ExecutableMetadataV2.Internal.prepareRetainedCandidateV2
    root fixture 1 "first" ``preparationCertificate Json.null
    | throwError "changed request admitted to candidate preparation"
  unless wrongRequestReason == "actual invocation unavailable" do throwError "wrong preparation refusal stage"
  -- The empty executable target is independently checked as TRUE at this candidate.
  liftTermElabM do
    let evaluated ← Solidity.Frontend.ExecutableMetadataV2.Internal.preparedExecutableEvaluationV2 prepared
    let type ← mkEq evaluated (mkConst ``Tri.tt)
    let proof ← mkEqRefl (mkConst ``Tri.tt)
    let base ← getEnv
    let name ← mkFreshUserName `_executable_true_control
    let checked ← Solidity.Frontend.ExecutableMetadataV2.Internal.installDeclarationsV2 #[(name, type, proof)]
    setEnv base
    unless checked.isOk do throwError "true executable evaluation control failed"
  let some receipt ← Solidity.Frontend.ExecutableMetadataV2.Internal.invocationReceiptV2? root
    | throwError "actual invocation receipt missing"
  unless (receipt.getObjValAs? Bool "retained").toOption == some true do
    throwError "candidate preparation changed invocation retention"
  unless ((← getEnv).constants.toList.map Prod.fst) == (preparationEnv.constants.toList.map Prod.fst) do
    throwError "candidate refusals or true-target control leaked declarations"
  let trueResult ← Solidity.Frontend.ExecutableMetadataV2.Internal.checkRetainedExecutableFailureV2
    root request 1 "first" ``preparationCertificate Json.null
  match trueResult with
  | .error reason => unless reason.startsWith "executable failure proof refused:" do
      throwError "true target failed at an unrelated stage: {reason}"
  | .ok _ => throwError "true executable target refuted"
  let .ok source := request.getObjVal? "contract" | throwError "missing injected source"
  let .ok members := source.getObjValAs? (Array Json) "nodes" | throwError "missing injected members"
  let some first := members[0]? | throwError "missing injected member"
  let falseMember := first.setObjVal! "documentation"
    (Json.mkObj [("nodeType", toJson "StructuredDocumentation"), ("text", toJson "@custom:key ensures false;")])
  let falseRequest := request.setObjVal! "contract" (source.setObjVal! "nodes" (toJson #[falseMember]))
  let falseRoot := `ExecutableBindingControls.invocationFalsePost
  let .ok falseReport ← Solidity.Frontend.ExecutableMetadataV2.Internal.retainInvocationV2 falseRoot falseRequest
    | throwError "injected false-post first invocation refused"
  logInfo m!"EXECUTABLE_FAILURE before proof: injected false-post report: {falseReport.compress}"
  let falseReceipt ← Solidity.Frontend.ExecutableMetadataV2.Internal.invocationReceiptV2? falseRoot
  logInfo m!"EXECUTABLE_FAILURE before proof: injected false-post capture: {(falseReceipt.map Json.compress).getD "missing"}"
  -- Preserve the unsupported semicolon observation. Do not normalize its input.
  let suffixResult ← Solidity.Frontend.ExecutableMetadataV2.Internal.checkRetainedExecutableFailureV2
    falseRoot falseRequest 1 "first" ``preparationCertificate Json.null
  match suffixResult with
  | .error reason => unless reason == "actual invocation unavailable" do
      throwError "unsupported suffix had unrelated refusal: {reason}"
  | .ok _ => throwError "unsupported suffix acquired a certificate"
  let .ok suffixRows := falseReport.getArr? | throwError "missing unsupported suffix report"
  let some suffixRow := suffixRows[0]? | throwError "missing unsupported suffix row"
  unless (suffixRow.getObjValAs? String "status").toOption == some "unsupported" &&
      (suffixRow.getObjValAs? String "reason").toOption == some "unsupported specification suffix" do
    throwError "unsupported suffix observation changed"
  -- A SEPARATE fixture in the existing parser's grammar, not an adapter or edit
  -- to any original compiler fixture. The failed earlier positive remains archived.
  let supportedMember := first.setObjVal! "documentation"
    (Json.mkObj [("nodeType", toJson "StructuredDocumentation"), ("text", toJson "@custom:key ensures false")])
  let supportedRequest := request.setObjVal! "contract" (source.setObjVal! "nodes" (toJson #[supportedMember]))
  let supportedRoot := `ExecutableBindingControls.invocationFalsePostSupportedGrammar
  let .ok supportedReport ← Solidity.Frontend.ExecutableMetadataV2.Internal.retainInvocationV2 supportedRoot supportedRequest
    | throwError "supported-grammar first invocation failed"
  logInfo m!"EXECUTABLE_FAILURE before proof: separate supported-grammar report: {supportedReport.compress}"
  let proofBase ← getEnv
  let checked ← Solidity.Frontend.ExecutableMetadataV2.Internal.checkRetainedExecutableFailureV2
    supportedRoot supportedRequest 1 "first" ``preparationCertificate Json.null
  let checked ← match checked with
    | .ok value => pure value
    | .error reason => throwError "actual injected false-post refutation unavailable: {reason}"
  unless (← getEnv).constants.toList.map Prod.fst == proofBase.constants.toList.map Prod.fst do
    throwError "executable refutation scratch declarations leaked"
  liftTermElabM do
    let formula := mkApp (mkConst ``GoalPair.executableFormula) checked.prepared.goalPair
    let target ← mkAppM ``Fml.Valid #[formula]
    let name ← mkFreshUserName `_executable_actual_refutation_replay
    let base ← getEnv
    let .ok () ← Solidity.Frontend.ExecutableMetadataV2.Internal.installDeclarationsV2
      #[(name, mkNot target, checked.refutation)]
      | throwError "actual refutation positive replay refused"
    let dependencies ← collectAxioms name
    logInfo m!"EXECUTABLE_FAILURE actual captured-target refutation dependencies: {dependencies}"
    let otherFormula := mkApp (mkConst ``GoalPair.executableFormula) prepared.goalPair
    let otherTarget ← mkAppM ``Fml.Valid #[otherFormula]
    let wrongName ← mkFreshUserName `_executable_wrong_captured_target
    match ← Solidity.Frontend.ExecutableMetadataV2.Internal.validateDeclarationsV2
        #[(wrongName, mkNot otherTarget, checked.refutation)] with
    | .error (.declTypeMismatch ..) => pure ()
    | .error _ => throwError "wrong captured target failed for unrelated kernel reason"
    | .ok () => throwError "refutation accepted for another captured target"
    setEnv base

  let bridgeResult ← Solidity.Frontend.ExecutableMetadataV2.Internal.checkRetainedExecutableFailureV2
    supportedRoot supportedRequest 1 "first" ``preparationFreshSpelling Json.null
  match bridgeResult with
  | .error reason =>
    unless reason.startsWith "retained values bridge refused:" do
      throwError "wrong values bridge failed at unrelated stage: {reason}"
    logInfo m!"EXECUTABLE_FAILURE default-name bridge unavailable (not a false-equation proof): {reason}"
  | .ok _ => throwError "source-values equality silently substituted for candidate-values equality"
  logInfo "EXECUTABLE_FAILURE synthetic captured-target checks; no source certificate or span"

run_cmd checkCandidatePreparation
/- These are injected ingress/refusal controls, not the unavailable four
original byte-pinned source/certificate cases. No source span is published. -/
def checkRetainedCandidateIdentity : CommandElabM Unit := do
  let some (.thmInfo certificate) := (← getEnv).find? ``preparationCertificate
    | throwError "retained identity control theorem absent"
  let (``Not, #[goal]) := certificate.type.consumeMData.getAppFnArgs
    | throwError "retained identity control goal shape changed"
  liftTermElabM do
    let some candidate ← sourceCounterexampleCandidateV1? goal ⟨certificate.value, .null⟩
      | throwError "retained identity control candidate unavailable"
    let same := Solidity.Frontend.ExecutableMetadataV2.Internal.sameRetainedCandidateV2
    unless same candidate candidate do throwError "exact retained identity refused"
    let foreign := mkNatLit 404
    let changes : List (String × SourceCounterexampleCandidateV1) := [
      ("proof", { candidate with original := ⟨foreign, .null⟩ }),
      ("contract", { candidate with contract := foreign }),
      ("formula", { candidate with formula := foreign }),
      ("candidate", { candidate with candidate := foreign }),
      ("domain", { candidate with domain := foreign }),
      ("values", { candidate with values := foreign }),
      ("valuesEquation", { candidate with valuesEquation := foreign }),
      ("state", { candidate with state := foreign }),
      ("failure", { candidate with failure := foreign })]
    for (label, changed) in changes do
      if same candidate changed then throwError "retained identity accepted changed {label}"
    unless same candidate { candidate with original := ⟨candidate.original.proof, toJson "presentation only"⟩ } do
      throwError "presentation JSON changed proof identity"
    logInfo "EXECUTABLE_INGRESS exact retained identity and nine mutation controls passed"
  for namespaceName in [Lean.Name.str .anonymous "foreign", `V1Storage.storageAlias_legacy.Identity] do
    let result ← Solidity.Frontend.ExecutableMetadataV2.Internal.checkSourceBoundRetainedExecutableV2
      `missingSourceCapture namespaceName .null "missing.sol" ByteArray.empty ByteArray.empty 0 .null
    match result with
    | .error "pinned source/invocation admission unavailable" => pure ()
    | .error reason => throwError "source admission refusal changed: {reason}"
    | .ok _ => throwError "unavailable/foreign source admitted"
  logInfo "EXECUTABLE_INGRESS source-bound unavailable/foreign ingress refused"

run_cmd checkRetainedCandidateIdentity

def checkImporterRowProjection : CommandElabM Unit := do
  let function : Solidity.Frontend.SolcFun := {
    name := "identity"
    sourceName := "identity"
    sourceId := 29
    sourceSignature := "identity(uint256)"
    line := 1
    tag := .specified
    params := [("x", "uint256")]
    body := .ok [] }
  let row := Solidity.Frontend.ImportRow.ofFun function .elaborated ""
  let same := Solidity.Frontend.ExecutableMetadataV2.Internal.sameImportedRowProjectionV2
  unless same row function do throwError "unchanged importer row projection refused"
  let changes : List (String × Solidity.Frontend.ImportRow) := [
    ("name", { row with name := "other" }),
    ("sourceName", { row with sourceName := "other" }),
    ("sourceSignature", { row with sourceSignature := "identity(bool)" }),
    ("sourceId", { row with sourceId := 44 }),
    ("tag", { row with tag := .internal }),
    ("params", { row with params := [("other", "bool")] }),
    ("payable", { row with payable := true }),
    ("writingCall", { row with writingCall := false })]
  for (label, changed) in changes do
    if same changed function then throwError "importer projection accepted changed {label}"
  let captured ← Solidity.Frontend.importedNormalizationCaptureV1? `NoActualImporterCapture
  if captured.isSome then throwError "missing process-local importer capture fabricated"
  logInfo "EXECUTABLE_INGRESS importer row projection and eight mutation controls passed"

run_cmd checkImporterRowProjection

-- Additive lawful-table control; the original constant-table case remains deferred.
def foreignProofNamesLawfulV2 : FreshNames :=
  .ofPrefixes "foreignSe" "se" "foreignIe" "foreignMv"

theorem freshSpellingBridgeFalseLawfulV2 : freshSpellingCandidate.sourceValuesV1 ≠
    (letI : FreshNames := foreignProofNamesLawfulV2; freshSpellingCandidate.vals) := by
  decide

section ForeignProofNameControlLawfulV2
local instance : FreshNames := foreignProofNamesLawfulV2
-- A separate explicit wrong-name table control; no production instance changes.
def checkForeignProofNameBridgeLawfulV2 : CommandElabM Unit := do
  if (← getOptions).getBool `debug.skipKernelTC false then throwError "kernel checking must be enabled"
  let .ok request := Json.parse r#"{"contract":{"nodeType":"ContractDefinition","contractKind":"contract","nodes":[{"nodeType":"FunctionDefinition","id":1,"name":"first","kind":"function","visibility":"public","stateMutability":"pure","modifiers":[],"parameters":{"parameters":[]},"returnParameters":{"parameters":[]},"body":{"nodeType":"Block","statements":[]},"documentation":""}]},"listing":false}"#
    | throwError "foreign-name control request malformed"
  let root := `ExecutableBindingControls.invocationForeignProofNamesLawfulV2
  let .ok _ ← Solidity.Frontend.ExecutableMetadataV2.Internal.retainInvocationV2 root request
    | throwError "foreign-name first invocation failed"
  let result ← Solidity.Frontend.ExecutableMetadataV2.Internal.checkRetainedExecutableFailureV2
    root request 1 "first" ``preparationFreshSpelling Json.null
  match result with
  | .error reason =>
    unless reason.startsWith "retained values bridge refused:" do
      throwError "foreign-name bridge failed at unrelated stage: {reason}"
    logInfo m!"EXECUTABLE_LAWFUL_NAMES explicit foreign-name bridge refusal: {reason}"
  | .ok _ => throwError "provably different source/candidate name table accepted"
  let dependencies ← collectAxioms ``freshSpellingBridgeFalseLawfulV2
  unless dependencies.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "foreign-name control dependencies refused"
  logInfo "EXECUTABLE_LAWFUL_NAMES explicit foreign-name bridge false proof and refusal passed"
run_cmd checkForeignProofNameBridgeLawfulV2
end ForeignProofNameControlLawfulV2

end ExecutableBindingControls
