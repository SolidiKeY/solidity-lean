import Solidity.Tools.ExecutableGoalBindingV2
import Solidity.Frontend.ExecutableAst.Shared.ObligationCaptureV2
import Solidity.Tools.DirectRuntime
import Solidity.Frontend.ExecutableCounterexampleMetadataV2

/-! Structural V2 controls only. These are not the four original source imports,
not source adequacy and not ordinary runtime evidence. Guard wrong target,
wrong retained values, changed candidate arguments and unchecked proof types.
-/
open Lean Elab Command Meta Solidity Solidity.Tools
namespace ExecutableBindingControls

def C : Contract := { vars := [] }
def candidate : Cand C := { st := .nil, args := [] }
def pair : GoalPairV2 := ⟨C, C, .ff, .ff⟩
def same : SameCandidateV2 pair :=
  ⟨candidate, candidate, HEq.rfl, rfl, rfl, rfl, rfl⟩
def failure : SelectedFailureV2 pair := ⟨same, rfl, rfl⟩
theorem exactTarget : ¬ Fml.Valid pair.executableFormula := failure.refuted

def truePair : GoalPairV2 := ⟨C, C, .ff, .tt⟩
theorem trueTargetRefused (w : SelectedFailureV2 truePair) : False := by
  have h := w.executableFailure
  change Tri.tt = Tri.ff at h
  cases h

theorem wrongValuesRefused :
    ¬ RetainedValuesBindingV2 C candidate [(Var.user "foreign", .bool true)] := by
  intro h
  have e := h.sourceValues
  change [(Var.user "foreign", Semantics.CallValue.bool true)] = [] at e
  cases e

def foreignCandidate : Cand C := { candidate with args := [("foreign", .bool true)] }
theorem changedArgumentsRefused (r : SameCandidateV2 pair)
    (hi : r.imported = candidate) (he : r.executable = foreignCandidate) : False := by
  have h := r.arguments
  rw [hi, he] at h
  change [] = [("foreign", Semantics.CallValue.bool true)] at h
  cases h

open Solidity.Frontend.ExecutableAst.Shared

/-- Injected callbacks for a structural builder test; not runtime callbacks. -/
def noLoops : BodyLoopLowerer := fun _ _ raw => pure raw
def noPre : PlainEntryPre := fun _ _ => .tt

example :
    (obligationCaptureV2 noLoops noPre C "missing" false false).map (fun r => r.formula) =
      .error "missing function" :=
  obligationCaptureV2_forget noLoops noPre C "missing" false false

run_cmd do
  let emptyFunction : FunDecl := { params := [], body := [] }
  let executable : Contract := { vars := [], funs := [("noop", emptyFunction)] }
  match obligationCaptureV2 noLoops noPre executable "noop" false false with
  | .error reason => throwError "structural positive capture refused: {reason}"
  | .ok _ => logInfo "EXECUTABLE_V2 actual builder positive capture confirmed (injected callbacks)"

run_cmd do
  let some (.thmInfo certificate) := (← getEnv).find? ``exactTarget
    | throwError "missing exact-target control"
  let options ← getOptions
  if options.getBool `debug.skipKernelTC false then
    throwError "kernel checking must be enabled"
  let target ← liftTermElabM <| mkAppM ``Fml.Valid #[mkApp (mkConst ``GoalPairV2.executableFormula)
    (mkConst ``truePair)]
  let declaration := Declaration.thmDecl {
    name := `ExecutableBindingControls.wrongTargetCertificate
    levelParams := [], type := mkNot target, value := certificate.value }
  let limit := maxHeartbeats.get options
  let options := maxHeartbeats.set options (if limit == 0 then 100000 else min limit 100000)
  let environment := (← getEnv)
  let positiveName := `ExecutableBindingControls.correctTargetCertificate
  unless !(environment.contains positiveName) &&
      !(environment.contains `ExecutableBindingControls.wrongTargetCertificate) do
    throwError "kernel-control declaration name already present"
  let positive := Declaration.thmDecl {
    name := positiveName, levelParams := [],
    type := certificate.type, value := certificate.value }
  match Kernel.Environment.addDecl environment.toKernelEnv options positive with
  | .error _ => throwError "correct-target replay failed under identical kernel ceiling"
  | .ok checked =>
    match Kernel.Environment.addDecl checked options declaration with
    | .ok _ => throwError "wrong-target certificate accepted"
    | .error (.declTypeMismatch ..) =>
      logInfo "EXECUTABLE_V2 correct-target replay and wrong-target declaration-type mismatch confirmed"
    | .error _ => throwError "wrong-target refusal was not a declaration-type mismatch"

#print axioms Solidity.Tools.RetainedValuesBindingV2.failure
#print axioms Solidity.Frontend.ExecutableAst.Shared.obligationCaptureV2_forget
#print axioms Solidity.Tools.SelectedFailureV2.refuted
#print axioms ExecutableBindingControls.exactTarget
#print axioms ExecutableBindingControls.trueTargetRefused
#print axioms ExecutableBindingControls.wrongValuesRefused
#print axioms ExecutableBindingControls.changedArgumentsRefused

/- Injected compact AST exercises actual request dispatch and capture order.
It is not compiler output, source certification or a retained proof candidate. -/
run_cmd do
  let .ok request := Json.parse r#"{"contract":{"nodeType":"ContractDefinition","contractKind":"contract","nodes":[{"nodeType":"FunctionDefinition","id":1,"name":"first","kind":"function","visibility":"public","stateMutability":"pure","modifiers":[],"parameters":{"parameters":[]},"returnParameters":{"parameters":[]},"body":{"nodeType":"Block","statements":[]},"documentation":""},{"nodeType":"FunctionDefinition","id":2,"name":"second","kind":"function","visibility":"public","stateMutability":"pure","modifiers":[],"parameters":{"parameters":[]},"returnParameters":{"parameters":[]},"body":{"nodeType":"Block","statements":[]},"documentation":""}]},"listing":true}"# | throwError "capture fixture JSON"
  let .ok (_, listed) := DirectRuntime.checkWithGoalsV2 request
    | throwError "listing capture refused"
  unless listed.size == 2 do throwError "listing lost ordered goals"
  for i in [:listed.size] do
    let some goal := listed[i]? | throwError "missing ordered listing goal"
    unless goal.sourceId == Int.ofNat (i + 1) &&
        goal.functionName == (if i == 0 then "first" else "second") do
      throwError "capture identity/order mismatch"
    unless goal.request.compress == request.compress &&
        goal.source.compress == ((request.getObjVal? "contract").toOption.getD .null).compress do
      throwError "capture request/source mismatch"
    unless !goal.retry && goal.result.isNone && goal.priorResult.isNone do
      throwError "listing fabricated an evaluation or retry"
  let ordinary := request.setObjVal! "listing" (toJson false)
  let .ok (report, evaluated) := DirectRuntime.checkWithGoalsV2 ordinary
    | throwError "ordinary capture refused"
  let .ok rows := report.getArr? | throwError "ordinary report shape"
  unless rows.size == 2 && evaluated.size == 2 do throwError "ordinary capture count"
  for i in [:evaluated.size] do
    let some goal := evaluated[i]? | throwError "missing ordered evaluation goal"
    let some result := goal.result | throwError "missing actual evaluation"
    unless !goal.retry && goal.priorResult.isNone && goal.sourceId == Int.ofNat (i + 1) &&
        goal.request.compress == ordinary.compress do throwError "wrong evaluation ownership"
    let .ok status := result.getObjValAs? String "status" | throwError "missing evaluation status"
    let .ok rowStatus := rows[i]!.getObjValAs? String "status" | throwError "missing report status"
    unless status == "proved" && rowStatus == "proved" do throwError "unexpected fixture status"
    let expectedName := if i == 0 then "first" else "second"
    let .ok rowId := rows[i]!.getObjValAs? Int "sourceId" | throwError "missing report identity"
    let .ok rowName := rows[i]!.getObjValAs? String "function" | throwError "missing report name"
    let .ok memberId := goal.member.getObjValAs? Int "id" | throwError "missing member identity"
    let .ok memberName := goal.member.getObjValAs? String "name" | throwError "missing member name"
    unless rowId == goal.sourceId && memberId == goal.sourceId &&
        rowName == expectedName && memberName == expectedName && goal.functionName == expectedName do
      throwError "capture/report/member identity mismatch"
    let (contractExpression, formulaExpression) :=
      Solidity.Frontend.ExecutableMetadataV2.Internal.quoteGoal goal
    if [contractExpression, formulaExpression].any (fun e =>
        e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasSorry) then
      throwError "captured goal quotation is not closed"
    let options ← getOptions
    let current := maxHeartbeats.get options
    let options := maxHeartbeats.set options (if current == 0 then 100000 else min current 100000)
    let declaration := Declaration.defnDecl {
      name := Name.num `ExecutableBindingControls.injectedCapturedGoal i,
      levelParams := [],
      type := mkApp2 (mkConst ``Fml) contractExpression (toExpr ([] : Ctx)),
      value := formulaExpression, hints := .regular 0, safety := .safe }
    match Kernel.Environment.addDecl (← getEnv).toKernelEnv options declaration with
    | .ok _ => logInfo m!"EXECUTABLE_V2 injected captured goal typed: {goal.sourceId}"
    | .error _ => throwError "actual injected captured-goal quotation failed kernel checking"
  let foreign := request.setObjVal! "sourceId" (toJson (99 : Int))
  if (DirectRuntime.checkWithGoalsV2 foreign).isOk then
    throwError "foreign selection admitted"
  let malformed := request.setObjVal! "sourceId" (toJson "1")
  if (DirectRuntime.checkWithGoalsV2 malformed).isOk then
    throwError "malformed selector admitted"
  logInfo "EXECUTABLE_V2 injected actual-dispatch listing/evaluation/order/ownership/refusal controls passed"

#print axioms DirectRuntime.checkWithGoalsV2_forget

/- Deliberately nondefault raw data exercises quotation, not source admission.
Some location/return flags here are not an admitted Solidity signature. -/
def quotationFunction : FunDecl := {
  sourceDecl := some { declaration := some 29, name := "declared", signature := some "declared(uint256)", mutability := .viewFn, callable := .abi .publicFn .selected (some ⟨17, by decide⟩) }
  params := [("a", .prim .uint)]
  paramLocs := [("a", .memory)]
  rets := [("r", .prim .uint)]
  retMem := true
  retStorage := true
  body := [.assign (.name "x") (.num 7), .whileLoop
    { inv := [.bool true], dec := some (.num 4), unwind := some 2, brk := true,
      qinv := [.all .bool "b" (.expr (.name "b"))] } (.bool false) []]
  mods := [{ name := "m", params := [("p", .prim .bool)], args := [.bool true], body := [.hole], widths := [("p", 1)], locs := [("p", .calldata)] }]
  spec := { requires := [.bool true], ensures := [.bool false], assignable := some [.root "x"], skip := true }
  payable := true
  widths := [("a", 8)] }

def quotationContract : Contract := {
  vars := [("x", .prim .uint)]
  transientRoots := ["x"]
  funs := [("model", quotationFunction)]
  enums := [("E", ["A", "B"])]
  inv := [.bool true]
  widths := [("x", 8)]
  ctor := some quotationFunction
  inits := [("x", .num 9)]
  structs := [("S", "encoded")]
  errors := [("Oops", quotationFunction)]
  evalOrder := .viaIR }

run_cmd do
  for type in [``RawTy, ``RawExpr, ``RawInv, ``RawLoopSpec, ``OFMode,
      ``RawStmt, ``SpecExpr, ``SpecLoc, ``FunSpec, ``ModApp, ``FunDecl, ``EvalOrder] do
    let provider? ← liftTermElabM <| synthInstance? (mkApp (mkConst ``ToExpr [0]) (mkConst type))
    if provider?.isSome then throwError "raw quotation instance leaked after import"
  let expected := mkConst ``quotationContract
  let quoted := Solidity.Frontend.ExecutableMetadataV2.Internal.quoteContract quotationContract
  if quoted.hasFVar || quoted.hasMVar || quoted.hasLevelMVar || quoted.hasSorry then
    throwError "unclosed quotation"
  let options ← getOptions
  let current := maxHeartbeats.get options
  let options := maxHeartbeats.set options (if current == 0 then 100000 else min current 100000)
  let positive := Declaration.thmDecl {
    name := `ExecutableBindingControls.quotationRoundTrip,
    levelParams := [], type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Contract) expected quoted,
    value := quoteRefl (mkConst ``Contract) expected }
  let .ok checked := Kernel.Environment.addDecl (← getEnv).toKernelEnv options positive
    | throwError "full quotation failed kernel round trip"
  let axioms ← liftTermElabM do
    addDecl positive
    let dependencies ← collectAxioms `ExecutableBindingControls.quotationRoundTrip
    pure dependencies
  unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "quotation control has nonstandard axioms"
  logInfo m!"EXECUTABLE_V2 quotation control axioms: {axioms}"
  let changedSource := { quotationFunction with sourceDecl := none }
  let mutants : List (String × Contract) := [
    ("sourceDecl", { quotationContract with funs := [("model", changedSource)] }),
    ("binaryOrder", { quotationContract with evalOrder := { EvalOrder.viaIR with binaryLeftToRight := false } }),
    ("modularOrder", { quotationContract with evalOrder := { EvalOrder.viaIR with modularLeftToRight := false } }),
    ("modifierFrames", { quotationContract with evalOrder := { EvalOrder.viaIR with modifierFrames := false } }),
    ("transientRoots", { quotationContract with transientRoots := [] }),
    ("funs", { quotationContract with funs := [] }),
    ("enums", { quotationContract with enums := [] }),
    ("invariants", { quotationContract with inv := [] }),
    ("widths", { quotationContract with widths := [] }),
    ("constructor", { quotationContract with ctor := none }),
    ("initializers", { quotationContract with inits := [] }),
    ("structs", { quotationContract with structs := [] }),
    ("errors", { quotationContract with errors := [] })]
  for (label, mutant) in mutants do
    let changed := Solidity.Frontend.ExecutableMetadataV2.Internal.quoteContract mutant
    let declaration := Declaration.thmDecl {
      name := Name.str `ExecutableBindingControls.quotationWrong label,
      levelParams := [], type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Contract) expected changed,
      value := quoteRefl (mkConst ``Contract) expected }
    match Kernel.Environment.addDecl checked options declaration with
    | .ok _ => throwError m!"changed {label} accepted as original quotation"
    | .error (.declTypeMismatch ..) => logInfo m!"EXECUTABLE_V2 quotation mismatch refused: {label}"
    | .error _ => throwError m!"changed {label} failed for an unrelated reason"


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
-- Explicit injected table: this proof does not claim default string-parser reduction.
def foreignProofNames : FreshNames :=
  { name := fun _ _ => "foreign", parse := fun _ => some ("foreign", 0) }
theorem freshSpellingBridgeFalse : freshSpellingCandidate.sourceValuesV1 ≠
    (letI : FreshNames := foreignProofNames; freshSpellingCandidate.vals) := by
  decide

section InvocationRetentionControls

/- A distinct injected first invocation; lookups must never rerun it. -/
run_cmd do
  let .ok fixture := Json.parse r#"{"contract":{"nodeType":"ContractDefinition","contractKind":"contract","nodes":[{"nodeType":"FunctionDefinition","id":1,"name":"first","kind":"function","visibility":"public","stateMutability":"pure","modifiers":[],"parameters":{"parameters":[]},"returnParameters":{"parameters":[]},"body":{"nodeType":"Block","statements":[]},"documentation":""},{"nodeType":"FunctionDefinition","id":2,"name":"second","kind":"function","visibility":"public","stateMutability":"pure","modifiers":[],"parameters":{"parameters":[]},"returnParameters":{"parameters":[]},"body":{"nodeType":"Block","statements":[]},"documentation":""}]},"listing":true}"# | throwError "invocation fixture JSON"
  let request := fixture.setObjVal! "listing" (toJson false)
  let base ← getEnv
  let root := `ExecutableBindingControls.invocationPrimary
  let .ok report ← Solidity.Frontend.ExecutableMetadataV2.Internal.retainInvocationV2 root request
    | throwError "first invocation failed"
  let .ok rows := report.getArr? | throwError "missing invocation rows"
  unless rows.size == 2 do throwError "invocation lost rows"
  for (id, functionName, index) in [(1, "first", 0), (2, "second", 1)] do
    let some selected ← Solidity.Frontend.ExecutableMetadataV2.Internal.selectedInvocationGoalV2?
      root request id functionName | throwError "actual retained terminal goal missing"
    unless selected.captureIndex == index && selected.goal.sourceId == id &&
        selected.goal.functionName == functionName && selected.goal.retryRequiredV2? == some false do
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
    let name ← mkFreshUserName `_executable_v2_true_control
    let checked ← Solidity.Frontend.ExecutableMetadataV2.Internal.installDeclarationsV2 #[(name, type, proof)]
    setEnv base
    unless checked.isOk do throwError "true executable evaluation control failed"
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
  logInfo m!"EXECUTABLE_V2 before proof: injected false-post report: {falseReport.compress}"
  let falseReceipt ← Solidity.Frontend.ExecutableMetadataV2.Internal.invocationReceiptV2? falseRoot
  logInfo m!"EXECUTABLE_V2 before proof: injected false-post capture: {(falseReceipt.map Json.compress).getD "missing"}"
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
  logInfo m!"EXECUTABLE_V2 before proof: separate supported-grammar report: {supportedReport.compress}"
  let proofBase ← getEnv
  let checked ← Solidity.Frontend.ExecutableMetadataV2.Internal.checkRetainedExecutableFailureV2
    supportedRoot supportedRequest 1 "first" ``preparationCertificate Json.null
  let checked ← match checked with
    | .ok value => pure value
    | .error reason => throwError "actual injected false-post refutation unavailable: {reason}"
  unless (← getEnv).constants.toList.map Prod.fst == proofBase.constants.toList.map Prod.fst do
    throwError "executable refutation scratch declarations leaked"
  liftTermElabM do
    let formula := mkApp (mkConst ``GoalPairV2.executableFormula) checked.prepared.goalPair
    let target ← mkAppM ``Fml.Valid #[formula]
    let name ← mkFreshUserName `_executable_v2_actual_refutation_replay
    let base ← getEnv
    let .ok () ← Solidity.Frontend.ExecutableMetadataV2.Internal.installDeclarationsV2
      #[(name, mkNot target, checked.refutation)]
      | throwError "actual refutation positive replay refused"
    let dependencies ← collectAxioms name
    logInfo m!"EXECUTABLE_V2 actual captured-target refutation dependencies: {dependencies}"
    let otherFormula := mkApp (mkConst ``GoalPairV2.executableFormula) prepared.goalPair
    let otherTarget ← mkAppM ``Fml.Valid #[otherFormula]
    let wrongName ← mkFreshUserName `_executable_v2_wrong_captured_target
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
    logInfo m!"EXECUTABLE_V2 default-name bridge unavailable (not a false-equation proof): {reason}"
  | .ok _ => throwError "source-values equality silently substituted for candidate-values equality"
  logInfo m!"EXECUTABLE_V2 actual injected false-post report retained: {falseReport.compress}"
  logInfo "EXECUTABLE_V2 checked executable failure, true-target refusal and unavailable default-name bridge controls passed"
  let receipt? ← Solidity.Frontend.ExecutableMetadataV2.Internal.invocationReceiptV2? root
  logInfo m!"EXECUTABLE_V2 first invocation outcome: {(receipt?.map Json.compress).getD "missing receipt"}"
  let some retained ← Solidity.Frontend.ExecutableMetadataV2.Internal.retainedInvocationV2? root request
    | throwError "actual invocation not retained"
  unless retained.goals.size == 2 && retained.report.compress == report.compress do
    throwError "wrong retained actual report"
  let some receiptBefore ← Solidity.Frontend.ExecutableMetadataV2.Internal.invocationReceiptV2? root
    | throwError "missing ordered invocation receipt"
  let some _ ← Solidity.Frontend.ExecutableMetadataV2.Internal.retainedInvocationV2? root request
    | throwError "read-only lookup lost capture"
  let some receiptAfter ← Solidity.Frontend.ExecutableMetadataV2.Internal.invocationReceiptV2? root
    | throwError "read-only lookup lost receipt"
  unless receiptBefore.compress == receiptAfter.compress do throwError "lookup changed invocation"
  let wrong := request.setObjVal! "sourceId" (toJson (99 : Int))
  if (← Solidity.Frontend.ExecutableMetadataV2.Internal.retainedInvocationV2? root wrong).isSome then
    throwError "foreign request matched actual invocation"
  match ← Solidity.Frontend.ExecutableMetadataV2.Internal.retainInvocationV2 root wrong with
  | .error "capture name unavailable" => pure ()
  | _ => throwError "duplicate invocation admitted"
  setEnv base
  match ← Solidity.Frontend.ExecutableMetadataV2.Internal.retainInvocationV2 root request with
  | .error "capture name unavailable" => pure ()
  | _ => throwError "environment rollback permitted execution replay"
  if (← getEnv).contains root then throwError "rollback replay created a declaration"
  let some goal := retained.goals[0]? | throwError "missing actual retained goal"
  let (contract, formula) := Solidity.Frontend.ExecutableMetadataV2.Internal.quoteGoal goal
  let forged := `ExecutableBindingControls.forgedInvocation
  let forgedContract := forged ++ `contract
  let forgedFormula := forged ++ `formula
  let fake := #[(forged, mkConst ``String, toExpr request.compress),
    (forgedContract, mkConst ``Contract, contract),
    (forgedFormula, mkApp2 (mkConst ``Fml) (mkConst forgedContract) (toExpr ([] : Ctx)), formula)]
  let .ok () ← liftTermElabM (Solidity.Frontend.ExecutableMetadataV2.Internal.installDeclarationsV2 fake)
    | throwError "coherent forged declaration control did not install"
  if (← Solidity.Frontend.ExecutableMetadataV2.Internal.retainedInvocationV2? forged request).isSome then
    throwError "public declarations alone authenticated an invocation"
  let goodName := `ExecutableBindingControls.invalidPrefix
  let badName := `ExecutableBindingControls.invalidClosedValue
  let invalid := #[(goodName, mkConst ``Nat, toExpr (1 : Nat)),
    (badName, mkConst ``Nat, mkConst ``Bool.true)]
  let validation ← liftTermElabM do
    let checked ← Solidity.Frontend.ExecutableMetadataV2.Internal.validateDeclarationsV2 invalid
    pure checked
  match validation with
  | .error (.declTypeMismatch ..) => pure ()
  | .error _ => throwError "invalid closed value failed for unrelated reason"
  | .ok () => throwError "invalid closed value accepted synchronously"
  let failed ← liftTermElabM <| Solidity.Frontend.ExecutableMetadataV2.Internal.installDeclarationsV2 invalid
  if failed.isOk || (← getEnv).contains goodName || (← getEnv).contains badName then
    throwError "failed validation published a declaration prefix"
  let collision := `ExecutableBindingControls.collidingInvocation
  let child := Lean.Name.str (Lean.Name.num collision 0) "contract"
  let .ok () ← liftTermElabM <| Solidity.Frontend.ExecutableMetadataV2.Internal.installDeclarationsV2
    #[(child, mkConst ``Nat, toExpr (17 : Nat))]
    | throwError "collision control setup failed"
  let .ok unchanged ← Solidity.Frontend.ExecutableMetadataV2.Internal.retainInvocationV2 collision request
    | throwError "retention failure changed ordinary runtime success"
  unless unchanged.compress == report.compress do throwError "retention failure replaced report"
  if (← Solidity.Frontend.ExecutableMetadataV2.Internal.retainedInvocationV2? collision request).isSome ||
      (← getEnv).contains collision then throwError "failed capture published a retained root"
  let some failureReceipt ← Solidity.Frontend.ExecutableMetadataV2.Internal.invocationReceiptV2? collision
    | throwError "retention failure dropped receipt"
  unless (failureReceipt.getObjValAs? Bool "retained").toOption == some false &&
      (failureReceipt.getObjValAs? String "reason").toOption == some "capture declaration collision" do
    throwError "retention failure detail was lost"
  logInfo m!"EXECUTABLE_V2 actual injected invocation receipt: {receiptBefore.compress}"
  logInfo "EXECUTABLE_V2 no-search lookup, rollback replay, coherent forgery, synchronous rejection and atomic-failure controls passed"

end InvocationRetentionControls

section ForeignProofNameControl
local instance : FreshNames := foreignProofNames
-- A separate explicit wrong-name table control; no production instance changes.
run_cmd do
  let .ok request := Json.parse r#"{"contract":{"nodeType":"ContractDefinition","contractKind":"contract","nodes":[{"nodeType":"FunctionDefinition","id":1,"name":"first","kind":"function","visibility":"public","stateMutability":"pure","modifiers":[],"parameters":{"parameters":[]},"returnParameters":{"parameters":[]},"body":{"nodeType":"Block","statements":[]},"documentation":""}]},"listing":false}"#
    | throwError "foreign-name control request malformed"
  let root := `ExecutableBindingControls.invocationForeignProofNames
  let .ok _ ← Solidity.Frontend.ExecutableMetadataV2.Internal.retainInvocationV2 root request
    | throwError "foreign-name first invocation failed"
  let result ← Solidity.Frontend.ExecutableMetadataV2.Internal.checkRetainedExecutableFailureV2
    root request 1 "first" ``preparationFreshSpelling Json.null
  match result with
  | .error reason =>
    unless reason.startsWith "retained values bridge refused:" do
      throwError "foreign-name bridge failed at unrelated stage: {reason}"
    logInfo m!"EXECUTABLE_V2 explicit foreign-name bridge refusal: {reason}"
  | .ok _ => throwError "provably different source/candidate name table accepted"
  let dependencies ← collectAxioms ``freshSpellingBridgeFalse
  unless dependencies.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "foreign-name control dependencies refused"
  logInfo "EXECUTABLE_V2 explicit foreign-name bridge false proof and refusal passed"
end ForeignProofNameControl

/- Injected protocol negatives, not actual annotated-loop or source evidence. -/
run_cmd do
  let outcome (status : String) (reason : String := "") :=
    Json.mkObj [("status", toJson status), ("reason", toJson reason)]
  let initial : Solidity.Frontend.ExecutableMetadataV2.Internal.EvaluationBranchV2 :=
    ⟨false, none, some (outcome "pending")⟩
  let retried : Solidity.Frontend.ExecutableMetadataV2.Internal.EvaluationBranchV2 :=
    ⟨true, initial.result, some (outcome "pending")⟩
  let select := Solidity.Frontend.ExecutableMetadataV2.Internal.terminalBranchOffsetV2?
  unless select true "pending" [initial, retried] == some 1 &&
      select false "pending" [initial] == some 0 do throwError "complete branch protocol refused"
  let negatives := [
    select true "pending" [initial],
    select false "pending" [initial, retried],
    select true "pending" [retried, initial],
    select true "pending" [initial, retried, retried],
    select true "pending" [initial, { retried with priorResult := some (outcome "pending" "foreign") }],
    select true "proved" [initial, retried],
    select true "pending" [initial, { retried with result := none }],
    select true "pending" [initial, { retried with priorResult := none }],
    select true "ready" [initial, { retried with result := some (outcome "ready") }],
    select false "ready" [{ initial with result := some (outcome "ready") }],
    select false "pending" [{ initial with result := some Json.null }],
    select false "pending" [{ initial with priorResult := initial.result }],
    select false "pending" [retried],
    select false "pending" []]
  unless negatives.all Option.isNone do throwError "incomplete or foreign branch protocol accepted"
  logInfo "EXECUTABLE_V2 injected complete-branch controls: 2 positive, 14 negative"

/- The four original fixtures are not present here. These are refusal controls,
not a fabricated positive source-admission or four-case executable result. -/
run_cmd do
  let namespaces := [`V1Storage.storageAlias_legacy.Identity, `V1Storage.storageAlias_ir.Identity,
    `V1Storage.storageCopy_legacy.Identity, `V1Storage.storageCopy_ir.Identity]
  for (namespaceName, sourceId) in namespaces.zip ([29, 29, 44, 44] : List Int) do
    unless (Solidity.Frontend.ExecutableMetadataV2.Internal.fourCasePinsV2? namespaceName).map (·.1) == some sourceId do
      throwError "reviewed exact namespace pin missing"
  let impostors := [Lean.Name.str .anonymous "V1Storage.storageAlias_legacy.Identity",
    Lean.Name.str (Lean.Name.str .anonymous "V1Storage.storageAlias_legacy") "Identity",
    Lean.Name.num `V1Storage.storageAlias_legacy.Identity 0,
    `Foreign.storageAlias_legacy.Identity]
  for namespaceName in impostors do
    if (Solidity.Frontend.ExecutableMetadataV2.Internal.fourCasePinsV2? namespaceName).isSome then
      throwError "nonidentical Lean namespace accepted"
  let empty := ByteArray.empty
  for namespaceName in namespaces do
    if (Solidity.Frontend.ExecutableMetadataV2.Internal.fourCaseSourceIdV2?
        namespaceName empty empty).isSome then throwError "missing original fixture/source accepted"
    if (← Solidity.Frontend.ExecutableMetadataV2.Internal.admittedInvocationSourceV2?
        `ExecutableBindingControls.invocationPrimary namespaceName Json.null "foreign.sol" empty empty).isSome then
      throwError "unbound source admitted"
  if (Solidity.Frontend.ExecutableMetadataV2.Internal.fourCaseSourceIdV2?
      `Foreign.storageAlias_legacy.Identity empty empty).isSome then throwError "foreign namespace accepted"
  -- Correct sizes are insufficient: immutable independent digests are mandatory.
  let wrongFixture := ByteArray.mk (Array.replicate 5479 (0 : UInt8))
  let wrongSource := ByteArray.mk (Array.replicate 153 (0 : UInt8))
  if (Solidity.Frontend.ExecutableMetadataV2.Internal.fourCaseSourceIdV2?
      `V1Storage.storageAlias_legacy.Identity wrongFixture wrongSource).isSome then
    throwError "same-sized modified raw bytes accepted"
  logInfo "EXECUTABLE_V2 four-case source pin refusal controls passed; original positive inputs unavailable"

/- A nondefault typed candidate under distinct contracts. This is synthetic
candidate-data preservation, not the four source cases or failure equivalence. -/
def layoutImported : Contract := { vars := [("x", .prim .uint), ("flag", .prim .bool)] }
def layoutExecutable : Contract :=
  { layoutImported with
    evalOrder := EvalOrder.viaIR
    funs := [("different", { params := [], body := [] })] }
def layoutCandidate : Cand layoutImported :=
  { st := .cons (.prim (PrimTy.ofIntD .uint 37)) (.cons (.prim true) .nil),
    args := [("flag", .bool true)],
    tx := { msgSender := PrimTy.ofIntD .uint 9, timestamp := PrimTy.ofIntD .uint 17 },
    net := [(PrimTy.ofIntD .uint 7, 16)], bal := PrimTy.ofIntD .uint 3 }
def layoutPair : GoalPairV2 := ⟨layoutImported, layoutExecutable, .ff, .tt⟩
def layoutRelation : SameCandidateV2 layoutPair :=
  SameCandidateV2.ofLayout layoutPair layoutCandidate rfl

theorem layoutCandidatePreserved :
    layoutRelation.imported = layoutCandidate ∧
    layoutRelation.executable.st = layoutCandidate.st ∧
    layoutRelation.executable.args = layoutCandidate.args ∧
    layoutRelation.executable.tx = layoutCandidate.tx ∧
    layoutRelation.executable.net = layoutCandidate.net ∧
    layoutRelation.executable.bal = layoutCandidate.bal :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wrongLayoutRefused (h : layoutImported.vars = C.vars) : False := by
  change [("x", Ty.prim PrimTy.uint), ("flag", Ty.prim PrimTy.bool)] = [] at h
  cases h

-- A same-candidate relation cannot supply the missing executable failure.
theorem layoutRelationDoesNotRefuteTrue (w : SelectedFailureV2 layoutPair) : False := by
  have h := w.executableFailure
  change Tri.tt = Tri.ff at h
  cases h

run_cmd do
  for name in [``Cand.rebindLayoutV2_storage, ``Cand.rebindLayoutV2_argInts,
      ``Cand.rebindLayoutV2_vals, ``SameCandidateV2.ofLayout_imported,
      ``layoutCandidatePreserved, ``wrongLayoutRefused, ``layoutRelationDoesNotRefuteTrue] do
    let axioms ← collectAxioms name
    unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "candidate layout control has nonstandard axioms"
    logInfo m!"EXECUTABLE_V2 layout control axioms: {name}: {axioms}"

/- These are injected ingress/refusal controls, not the unavailable four
original byte-pinned source/certificate cases. No source span is published. -/
run_cmd do
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
    logInfo "EXECUTABLE_V2 exact retained identity and nine mutation controls passed"
  for namespaceName in [Lean.Name.str .anonymous "foreign", `V1Storage.storageAlias_legacy.Identity] do
    let result ← Solidity.Frontend.ExecutableMetadataV2.Internal.checkSourceBoundRetainedExecutableV2
      `missingSourceCapture namespaceName .null "missing.sol" ByteArray.empty ByteArray.empty 0 .null
    match result with
    | .error "pinned source/invocation admission unavailable" => pure ()
    | .error reason => throwError "source admission refusal changed: {reason}"
    | .ok _ => throwError "unavailable/foreign source admitted"
  logInfo "EXECUTABLE_V2 source-bound unavailable/foreign ingress refused"

run_cmd do
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
  logInfo "EXECUTABLE_V2 importer row projection and eight mutation controls passed"

end ExecutableBindingControls
