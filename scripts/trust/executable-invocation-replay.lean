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

run_cmd checkInvocationRetention

end ExecutableBindingControls
