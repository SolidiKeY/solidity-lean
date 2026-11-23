import Solidity.Tools.ExecutableGoalBinding
import Solidity.Frontend.ExecutableAst.Shared.ObligationCapture
import Solidity.Tools.DirectRuntime

/-! Structural executable-goal controls only. These are not the four original source imports,
not source adequacy and not ordinary runtime evidence. Guard wrong target,
wrong retained values, changed candidate arguments and unchecked proof types.
-/
open Lean Elab Command Meta Solidity Solidity.Tools
namespace ExecutableBindingControls

def C : Contract := { vars := [] }
def candidate : Cand C := { st := .nil, args := [] }
def pair : GoalPair := ⟨C, C, .ff, .ff⟩
def same : SameCandidate pair :=
  ⟨candidate, candidate, HEq.rfl, rfl, rfl, rfl, rfl⟩
def failure : SelectedFailure pair := ⟨same, rfl, rfl⟩
theorem exactTarget : ¬ Fml.Valid pair.executableFormula := failure.refuted

def truePair : GoalPair := ⟨C, C, .ff, .tt⟩
theorem trueTargetRefused (w : SelectedFailure truePair) : False := by
  have h := w.executableFailure
  change Tri.tt = Tri.ff at h
  cases h

theorem wrongValuesRefused :
    ¬ RetainedValuesBinding C candidate [(Var.user "foreign", .bool true)] := by
  intro h
  have e := h.sourceValues
  change [(Var.user "foreign", Semantics.CallValue.bool true)] = [] at e
  cases e

def foreignCandidate : Cand C := { candidate with args := [("foreign", .bool true)] }
theorem changedArgumentsRefused (r : SameCandidate pair)
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
    (obligationCapture noLoops noPre C "missing" false false).map (fun r => r.formula) =
      .error "missing function" :=
  obligationCapture_forget noLoops noPre C "missing" false false

run_cmd do
  let emptyFunction : FunDecl := { params := [], body := [] }
  let executable : Contract := { vars := [], funs := [("noop", emptyFunction)] }
  match obligationCapture noLoops noPre executable "noop" false false with
  | .error reason => throwError "structural positive capture refused: {reason}"
  | .ok _ => logInfo "EXECUTABLE_V2 actual builder positive capture confirmed (injected callbacks)"

run_cmd do
  let some (.thmInfo certificate) := (← getEnv).find? ``exactTarget
    | throwError "missing exact-target control"
  let options ← getOptions
  if options.getBool `debug.skipKernelTC false then
    throwError "kernel checking must be enabled"
  let target ← liftTermElabM <| mkAppM ``Fml.Valid #[mkApp (mkConst ``GoalPair.executableFormula)
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

#print axioms Solidity.Tools.RetainedValuesBinding.failure
#print axioms Solidity.Frontend.ExecutableAst.Shared.obligationCapture_forget
#print axioms Solidity.Tools.SelectedFailure.refuted
#print axioms ExecutableBindingControls.exactTarget
#print axioms ExecutableBindingControls.trueTargetRefused
#print axioms ExecutableBindingControls.wrongValuesRefused
#print axioms ExecutableBindingControls.changedArgumentsRefused


/- Injected compact AST exercises actual request dispatch and capture order.
It is not compiler output, source certification or a retained proof candidate. -/
run_cmd do
  let .ok request := Json.parse r#"{"contract":{"nodeType":"ContractDefinition","contractKind":"contract","nodes":[{"nodeType":"FunctionDefinition","id":1,"name":"first","kind":"function","visibility":"public","stateMutability":"pure","modifiers":[],"parameters":{"parameters":[]},"returnParameters":{"parameters":[]},"body":{"nodeType":"Block","statements":[]},"documentation":""},{"nodeType":"FunctionDefinition","id":2,"name":"second","kind":"function","visibility":"public","stateMutability":"pure","modifiers":[],"parameters":{"parameters":[]},"returnParameters":{"parameters":[]},"body":{"nodeType":"Block","statements":[]},"documentation":""}]},"listing":true}"# | throwError "capture fixture JSON"
  let .ok (_, listed) := DirectRuntime.checkWithGoals request
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
    unless goal.retryRequired? == none && !goal.retry && goal.result.isNone && goal.priorResult.isNone do
      throwError "listing fabricated an evaluation or retry"
  let ordinary := request.setObjVal! "listing" (toJson false)
  let .ok (report, evaluated) := DirectRuntime.checkWithGoals ordinary
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
    unless goal.retryRequired? == some false && status == "proved" && rowStatus == "proved" do throwError "unexpected fixture status"
    let expectedName := if i == 0 then "first" else "second"
    let .ok rowId := rows[i]!.getObjValAs? Int "sourceId" | throwError "missing report identity"
    let .ok rowName := rows[i]!.getObjValAs? String "function" | throwError "missing report name"
    let .ok memberId := goal.member.getObjValAs? Int "id" | throwError "missing member identity"
    let .ok memberName := goal.member.getObjValAs? String "name" | throwError "missing member name"
    unless rowId == goal.sourceId && memberId == goal.sourceId &&
        rowName == expectedName && memberName == expectedName && goal.functionName == expectedName do
      throwError "capture/report/member identity mismatch"
  let foreign := request.setObjVal! "sourceId" (toJson (99 : Int))
  if (DirectRuntime.checkWithGoals foreign).isOk then
    throwError "foreign selection admitted"
  let malformed := request.setObjVal! "sourceId" (toJson "1")
  if (DirectRuntime.checkWithGoals malformed).isOk then
    throwError "malformed selector admitted"
  logInfo "EXECUTABLE_V2 injected actual-dispatch listing/evaluation/order/ownership/refusal controls passed"

#print axioms DirectRuntime.checkWithGoals_forget

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
def layoutPair : GoalPair := ⟨layoutImported, layoutExecutable, .ff, .tt⟩
def layoutRelation : SameCandidate layoutPair :=
  SameCandidate.ofLayout layoutPair layoutCandidate rfl

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
theorem layoutRelationDoesNotRefuteTrue (w : SelectedFailure layoutPair) : False := by
  have h := w.executableFailure
  change Tri.tt = Tri.ff at h
  cases h

run_cmd do
  for name in [``Cand.rebindLayout_storage, ``Cand.rebindLayout_argInts,
      ``Cand.rebindLayout_vals, ``SameCandidate.ofLayout_imported,
      ``layoutCandidatePreserved, ``wrongLayoutRefused, ``layoutRelationDoesNotRefuteTrue] do
    let axioms ← collectAxioms name
    unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "candidate layout control has nonstandard axioms"
    logInfo m!"EXECUTABLE_V2 layout control axioms: {name}: {axioms}"


end ExecutableBindingControls
