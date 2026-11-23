import Solidity.Frontend.ExecutableCounterexampleMetadataV2
import Solidity.Examples.ExecutableRequestData

/-! Synthetic executable invocation retention and request/goal selection checks.
These injected ASTs are not compiler output or source-failure certificates. -/
open Lean Elab Command Meta Solidity Solidity.Tools
namespace ExecutableBindingControls
open Solidity.Frontend.ExecutableMetadataV2.Internal

/- A distinct injected first invocation; lookups must never rerun it. -/
def checkInvocationRetention : CommandElabM Unit := do
  let axioms ← collectAxioms ``Solidity.Tools.DirectRuntime.checkWithGoals_forget
  unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "forget theorem has nonstandard axioms"
  logInfo m!"EXECUTABLE_INVOCATION forget theorem axioms: {axioms}"
  let .ok fixture := invocationFixture | throwError "invocation fixture JSON"
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
        selected.goal.functionName == functionName && selected.goal.retryRequired? == some false do
      throwError "actual retained terminal goal changed identity"
  for (id, functionName) in [(1, "second"), (2, "first"), (99, "first")] do
    if (← Solidity.Frontend.ExecutableMetadataV2.Internal.selectedInvocationGoalV2?
        root request id functionName).isSome then throwError "foreign terminal goal selected"
  if (← Solidity.Frontend.ExecutableMetadataV2.Internal.selectedInvocationGoalV2?
      root fixture 1 "first").isSome then throwError "changed request selected"
  logInfo "EXECUTABLE_INVOCATION actual capture and selection controls passed"
  let empty := ByteArray.empty
  for (namespaceName, sourceId) in ([(`V1Storage.storageAlias_legacy.Identity, 29),
      (`V1Storage.storageAlias_ir.Identity, 29), (`V1Storage.storageCopy_legacy.Identity, 44),
      (`V1Storage.storageCopy_ir.Identity, 44)] : List (Lean.Name × Int)) do
    unless (fourCasePinsV2? namespaceName).map (·.1) == some sourceId do
      throwError "exact namespace pin missing"
    if (fourCaseSourceIdV2? namespaceName empty empty).isSome then
      throwError "missing fixture/source bytes accepted"
    if (← admittedInvocationSourceV2? root namespaceName request "foreign.sol" empty empty).isSome then
      throwError "unbound source admitted"
    match ← checkSourceBoundRetainedExecutableV2 root namespaceName request "foreign.sol" empty empty 0 Json.null with
    | .error "pinned source/invocation admission unavailable" => pure ()
    | _ => throwError "missing source inputs reached retained executable admission"
  logInfo "EXECUTABLE_INVOCATION missing source inputs refused; no positive source certification"
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
  logInfo m!"EXECUTABLE_INVOCATION actual injected invocation receipt: {receiptBefore.compress}"
  logInfo "EXECUTABLE_INVOCATION no-search lookup, rollback replay, coherent forgery, synchronous rejection and atomic-failure controls passed"


run_cmd checkInvocationRetention

/- Injected protocol negatives, not actual annotated-loop or source evidence. -/
def checkBranchProtocol : CommandElabM Unit := do
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
  logInfo "EXECUTABLE_INGRESS injected complete-branch controls: 2 positive, 14 negative"

run_cmd checkBranchProtocol

/- The four original fixtures are not present here. These are refusal controls,
not a fabricated positive source-admission or four-case executable result. -/
def checkSourcePinRefusals : CommandElabM Unit := do
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
  logInfo "EXECUTABLE_INGRESS four-case source pin refusal controls passed; original positive inputs unavailable"

run_cmd checkSourcePinRefusals

end ExecutableBindingControls
