import Std.Sync.Mutex
import Solidity.Tools.DirectRuntime

/-! # Internal executable invocation retention and reification for V2 intake

Prevents the regression of quoting the importer contract instead of the actual
executable contract: source declarations, operand schedules and every other
field remain literal data. Generic derived quotations reuse the existing raw
constructors; no parser, normalizer, builder or verifier is copied. Retention
runs the ordinary first request once; reification and lookup never rerun it.

The resulting expressions are UNCHECKED until independently kernel checked.
This is not capture authentication, compiler adequacy, candidate failure or
metadata ingress. No certificate or source location is published here.
-/
namespace Solidity.Frontend.ExecutableMetadataV2.Internal
open Lean Solidity

-- Use Lean's generator, changing only its instance registration to local.
-- Its constructor quoting implementation and the shared source types stay unchanged.
section
run_cmd do
  let localKind ← `(Lean.Parser.Term.attrKind| local)
  for type in [``RawTy, ``RawExpr, ``RawInv, ``RawLoopSpec, ``OFMode,
      ``RawStmt, ``SpecExpr, ``SpecLoc, ``FunSpec, ``ModApp, ``FunDecl, ``EvalOrder] do
    let commands ← withFreshMacroScope <| Lean.Elab.Command.liftTermElabM <|
      Lean.Elab.Deriving.ToExpr.mkToExprInstanceCmds #[type]
    for command in commands do
      let localized := command.rewriteBottomUp fun node =>
        if node.isOfKind ``Lean.Parser.Command.instance then node.setArg 0 localKind else node
      Lean.Elab.Command.elabCommand localized

/-- Full literal constructor, including all proof fields. The existing Boolean
side conditions must reduce in the kernel; no proof is trusted by this quoter. -/
def quoteContract (C : Contract) : Expr :=
  mkAppN (mkConst ``Contract.mk) #[toExpr C.vars, toExpr C.transientRoots,
    rflTrue, toExpr C.funs, toExpr C.enums, toExpr C.inv, toExpr C.widths,
    toExpr C.ctor, toExpr C.inits, toExpr C.structs, toExpr C.errors,
    toExpr C.evalOrder, rflTrue, rflTrue]

/-- Reify the actual captured intrinsic target without rebuilding it. This may
be a listing or unsupported-to-certify capture: callers must independently
validate invocation ownership, branch, source and certificate admission. -/
def quoteGoal (goal : Tools.DirectRuntime.RequestGoalCaptureV2) : Expr × Expr :=
  let contract := quoteContract goal.contract
  (contract, Fml.quote contract goal.formula)

end


open Elab Command Meta

private initialize invocationClaimsV2 : Std.Mutex (Nat × NameMap Nat) ←
  Std.Mutex.new (0, {})

private def claimInvocationV2 (name : Lean.Name) : IO (Option Nat) :=
  invocationClaimsV2.atomically do
    let state : Nat × NameMap Nat ← get
    let next := state.1
    let claims := state.2
    if (claims.find? name).isSome then return none
    let updated : NameMap Nat := claims.insert name next
    set (next + 1, updated)
    return some next

private def invocationClaimV2? (name : Lean.Name) : IO (Option Nat) :=
  invocationClaimsV2.atomically do
    let (_, claims) ← get
    return claims.find? name

/-- Internal actual-invocation data, not source or certificate authentication.
A publisher must look this up again; a caller-made copy is not an admission. -/
structure RetainedInvocationV2 where
  private mk ::
  request : Json
  token : Nat
  report : Json
  goals : Array Tools.DirectRuntime.RequestGoalCaptureV2
  declarations : Array (Lean.Name × Expr × Expr)

private structure InvocationAttemptV2 where
  request : Json
  token : Nat
  report : Option (Except String Json) := none
  retained : Option RetainedInvocationV2 := none
  reason : String := "pending"

private initialize invocationAttemptsV2 : EnvExtension (NameMap InvocationAttemptV2) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

private def kernelOptionsV2 : CoreM Options := do
  let options ← getOptions
  let current := maxHeartbeats.get options
  let limit := if current == 0 then 100000 else min current 100000
  return debug.skipKernelTC.set (Elab.async.set (maxHeartbeats.set options limit) false) false

/-- Synchronous validation in a scratch kernel environment, with the unchanged
ceiling (or caller's tighter limit). This publishes nothing and checks no source
or candidate relation. The ordered declarations may refer to preceding ones. -/
def validateDeclarationsV2 (declarations : Array (Lean.Name × Expr × Expr)) :
    CoreM (Except Kernel.Exception Unit) := do
  let options ← kernelOptionsV2
  let mut checked := (← getEnv).toKernelEnv
  for (name, type, value) in declarations do
    let declaration := Declaration.defnDecl {
      name := name, levelParams := [], type := type, value := value,
      hints := .regular 0, safety := .safe }
    match Kernel.Environment.addDecl checked options declaration with
    | .error error => return .error error
    | .ok next => checked := next
  return .ok ()

/-- Atomic publication of closed, synchronously checked data declarations.
No caller-supplied declaration can create an invocation registry entry. -/
def installDeclarationsV2 (declarations : Array (Lean.Name × Expr × Expr)) :
    TermElabM (Except String Unit) := do
  let base ← getEnv
  try
    for (name, type, value) in declarations do
      if (← getEnv).contains name then throwError "capture declaration collision"
      if [type, value].any (fun e => e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasSorry) then
        throwError "capture declaration is not closed"
    match ← validateDeclarationsV2 declarations with
    | .error error => throwKernelException error
    | .ok () => pure ()
    let options ← kernelOptionsV2
    withOptions (fun _ => options) do
      for (name, type, value) in declarations do
        addDecl <| .defnDecl {
          name := name, levelParams := [], type := type, value := value,
          hints := .regular 0, safety := .safe }
        let dependencies ← collectAxioms name
        unless dependencies.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
          throwError "capture declaration has nonstandard axioms"
    return .ok ()
  catch error =>
    setEnv base
    return .error (← error.toMessageData.toString)

/-- One first execution in place of an ordinary request, never a later lookup.
The original runtime result survives retention failure. A process-lifetime
mutex claim prevents reuse even after environment rollback or command failure.
This does not admit a source, candidate, session or certificate. -/
def retainInvocationV2 (name : Lean.Name) (request : Json) :
    CommandElabM (Except String Json) := do
  if (← getEnv).contains name then return .error "capture name unavailable"
  let some token ← claimInvocationV2 name | return .error "capture name unavailable"
  modifyEnv fun env => invocationAttemptsV2.modifyState env
    (·.insert name { request := request, token := token })
  let base ← getEnv
  let execution ← liftTermElabM <| tryCatchRuntimeEx
    (pure (Tools.DirectRuntime.checkWithGoalsV2 request))
    (fun error => do
      modifyEnv fun env => invocationAttemptsV2.modifyState env
        (·.insert name { request := request, token := token, reason := "runtime exception" })
      throw error)
  let original := execution.map Prod.fst
  let record (retained : Option RetainedInvocationV2) (reason : String) : CommandElabM Unit :=
    modifyEnv fun env => invocationAttemptsV2.modifyState env
      (·.insert name ⟨request, token, some original, retained, reason⟩)
  match execution with
  | .error _ => record none "runtime refused"; return original
  | .ok (report, goals) =>
    try
      let mut declarations : Array (Lean.Name × Expr × Expr) :=
        #[(name, mkConst ``String, toExpr request.compress)]
      for i in [:goals.size] do
        let some goal := goals[i]? | throwError "missing actual capture"
        let (contract, formula) := quoteGoal goal
        let contractName := Lean.Name.str (Lean.Name.num name i) "contract"
        let formulaName := Lean.Name.str (Lean.Name.num name i) "formula"
        declarations := declarations.push (contractName, mkConst ``Contract, contract)
        declarations := declarations.push (formulaName,
          mkApp2 (mkConst ``Fml) (mkConst contractName) (toExpr ([] : Ctx)), formula)
      match ← liftTermElabM (installDeclarationsV2 declarations) with
      | .error reason =>
        setEnv base
        record none reason
      | .ok () => record (some ⟨request, token, report, goals, declarations⟩) "retained"
      return original
    catch error =>
      setEnv base
      record none (← error.toMessageData.toString)
      return original

/-- Read-only lookup. No evaluation, decoding, building or candidate search.
It requires the private actual-invocation record, durable process token and
all exact closed declarations. Source/session/candidate admission is separate. -/
def retainedInvocationV2? (name : Lean.Name) (request : Json) :
    CommandElabM (Option RetainedInvocationV2) := do
  let some attempt := (invocationAttemptsV2.getState (← getEnv)).find? name | return none
  let some retained := attempt.retained | return none
  unless (← invocationClaimV2? name) == some retained.token do return none
  unless retained.request.compress == request.compress do return none
  for (name, type, value) in retained.declarations do
    let some (.defnInfo declaration) := (← getEnv).find? name | return none
    unless declaration.levelParams.isEmpty && declaration.safety == .safe &&
        declaration.type == type && declaration.value == value do return none
  return some retained

/-- Protocol facts only: callers cannot use this record as invocation,
source or certificate authority. Real intake must obtain its retry requirement
from the private retained invocation and `retryRequiredV2?`. -/
structure EvaluationBranchV2 where
  retry : Bool
  priorResult : Option Json
  result : Option Json

private def runtimeStatusV2? (result : Option Json) : Option String := do
  let result ← result
  let status ← (result.getObjValAs? String "status").toOption
  if status == "proved" || status == "refuted" || status == "pending" then some status else none

/-- Select an offset only for a complete, ordered initial/retry protocol.
Full prior-result bytes must match, even when both outcomes are pending.
This is a protocol validator, not the actual-invocation intake or a certificate. -/
def terminalBranchOffsetV2? (needsRetry : Bool) (reportStatus : String)
    (branches : List EvaluationBranchV2) : Option Nat := do
  match needsRetry, branches with
  | false, [initial] =>
    if initial.retry || initial.priorResult.isSome then none else do
      let status ← runtimeStatusV2? initial.result
      if status == reportStatus then some 0 else none
  | true, [initial, retry] =>
    if initial.retry || initial.priorResult.isSome || !retry.retry then none else do
      let initialStatus ← runtimeStatusV2? initial.result
      let prior ← retry.priorResult
      let original ← initial.result
      let finalStatus ← runtimeStatusV2? retry.result
      if initialStatus == "pending" && prior.compress == original.compress &&
          finalStatus == reportStatus then some 1 else none
  | _, _ => none

/-- An internal selection of the actual execution target. No source bytes,
candidate, failure certificate or span is admitted by this record. -/
structure SelectedInvocationGoalV2 where
  private mk ::
  invocation : RetainedInvocationV2
  row : Json
  goal : Tools.DirectRuntime.RequestGoalCaptureV2
  captureIndex : Nat

/-- Read only the private retained first execution, preserving global capture
index and exact report/member identities. A missing retry is refused even when
initial and terminal statuses would both be pending. No search is performed. -/
def selectedInvocationGoalV2? (name : Lean.Name) (request : Json)
    (sourceId : Int) (functionName : String) : CommandElabM (Option SelectedInvocationGoalV2) := do
  let some invocation ← retainedInvocationV2? name request | return none
  let some rows := invocation.report.getArr?.toOption | return none
  let rows := rows.filter fun row =>
    (row.getObjValAs? Int "sourceId").toOption == some sourceId
  unless rows.size == 1 do return none
  let some row := rows[0]? | return none
  unless (row.getObjValAs? String "function").toOption == some functionName do return none
  let some status := (row.getObjValAs? String "status").toOption | return none
  let captures := invocation.goals.toList.zipIdx |>.filter fun item => item.1.sourceId == sourceId
  let (initial, _) :: _ := captures | return none
  let some needsRetry := initial.retryRequiredV2? | return none
  for (goal, _) in captures do
    unless goal.functionName == functionName && goal.request.compress == request.compress &&
        goal.source.compress == initial.source.compress && goal.member.compress == initial.member.compress &&
        (goal.member.getObjValAs? Int "id").toOption == some sourceId &&
        (goal.member.getObjValAs? String "name").toOption == some functionName &&
        goal.specified == initial.specified && goal.box == initial.box do return none
  let facts := captures.map fun (goal, _) =>
    ({ retry := goal.retry, priorResult := goal.priorResult, result := goal.result } : EvaluationBranchV2)
  let some offset := terminalBranchOffsetV2? needsRetry status facts | return none
  let some (goal, index) := captures[offset]? | return none
  return some ⟨invocation, row, goal, index⟩

/-- Diagnostic receipt only, never certificate admission. -/
def invocationReceiptV2? (name : Lean.Name) : CommandElabM (Option Json) := do
  let some attempt := (invocationAttemptsV2.getState (← getEnv)).find? name | return none
  let report := attempt.report.map fun result => match result with
    | .ok rows => Json.mkObj [("ok", rows)]
    | .error reason => Json.mkObj [("error", toJson reason)]
  return some (Json.mkObj [("reason", toJson attempt.reason), ("token", toJson attempt.token),
    ("report", report.getD .null), ("retained", toJson attempt.retained.isSome)])

end Solidity.Frontend.ExecutableMetadataV2.Internal
