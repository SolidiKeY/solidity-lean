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

end ExecutableBindingControls
