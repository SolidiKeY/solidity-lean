import Solidity.Examples.ExecutableGoalBinding
import Solidity.Examples.ExecutableRequestData
import Solidity.Frontend.ExecutableCounterexampleMetadataV2

/-! Synthetic named-theorem candidate data and independent true-target checks.
No original source certificate, executable failure or span is admitted here. -/
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
  logInfo "EXECUTABLE_PREPARATION candidate data checked; true target is not a failure certificate"

run_cmd checkCandidatePreparation
end ExecutableBindingControls
