import Solidity.Examples.SourceCounterexample

/-!
# Same-candidate companion regression controls

Guards the editor regression where a second search, a different goal, or
modified evaluator arguments supplies presentation metadata. These controls use
an actual counterexample from the existing source-certificate example. They
certify no source span: clause locations are not carried by that producer yet.
-/

open Solidity Lean Elab Command Meta

def SourceCandidateNoArgs : Contract := contract!{
  ensures false;
  function bad() public pure {}
}

def sourceCandidateNoArgsFormula : Fml SourceCandidateNoArgs [] := cspec[SourceCandidateNoArgs]{bad}

run_cmd liftTermElabM do
  let goal ← mkAppM ``Fml.Valid #[mkConst ``sourceCandidateNoArgsFormula]
  let some actual ← Tools.refuteSourceCandidateV1? goal 16
    | throwError "real no-argument counterexample must be retained"
  let (_, args) := actual.original.proof.consumeMData.getAppFnArgs
  let equalityType ← inferType actual.failure
  let forgedFailure := mkApp2 (mkConst ``id [levelZero]) equalityType (mkConst ``True.intro)
  let forged : Tools.SourceCounterexample := {
    proof := mkAppN (mkConst ``Fml.not_valid_of_eval3Peel) (args.set! 5 forgedFailure)
    report := actual.original.report }
  unless (← Tools.sourceCounterexampleCandidateV1? goal forged).isNone do
    throwError "FORGED_INTERNAL_PROOF_ACCEPTED: malformed id application passed inferred type"

run_cmd liftTermElabM do
  let formula := mkConst ``Solidity.Examples.SourceCounterexample.badSpec
  let goal ← mkAppM ``Fml.Valid #[formula]
  let some evidence ← Tools.refuteSourceCandidateV1? goal 16
    | throwError "the existing real counterexample must expose its same candidate"
  unless ← isDefEq (← inferType evidence.candidate)
      (mkApp (mkConst ``Tools.Cand) evidence.contract) do
    throwError "candidate is not intrinsically typed at the original contract"
  let reconstructed ← mkAppM ``Fml.not_valid_of_eval3Peel
    #[evidence.values, evidence.state, evidence.failure]
  unless ← isDefEq reconstructed evidence.original.proof do
    throwError "companion changed the original proof candidate"
  let name := `Solidity.Tools.SourceCandidateControlsV1.refuted
  addDecl <| .thmDecl {name, levelParams := [], type := mkNot goal, value := evidence.original.proof}
  let axioms ← collectAxioms name
  unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "nonstandard axiom in actual counterexample"
  let equalityName := `Solidity.Tools.SourceCandidateControlsV1.arguments
  let equalityType ← inferType evidence.valuesEquation
  addDecl <| .thmDecl {name := equalityName, levelParams := [], type := equalityType, value := evidence.valuesEquation}
  let argumentAxioms ← collectAxioms equalityName
  unless argumentAxioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "nonstandard axiom in argument correspondence"
  let assigned ← mkFreshExprMVar (mkNot goal)
  assigned.mvarId!.assign evidence.original.proof
  let rawAssigned : Tools.SourceCounterexample := {proof := assigned, report := evidence.original.report}
  unless (← Tools.sourceCounterexampleCandidateV1? goal rawAssigned).isNone do
    throwError "ASSIGNED_MVAR_ACCEPTED: returned original proof is not closed"
  let otherGoal ← mkAppM ``Fml.Valid #[mkConst ``Solidity.Examples.SourceCounterexample.goodSpec]
  unless (← Tools.sourceCounterexampleCandidateV1? otherGoal evidence.original).isNone do
    throwError "proof from another goal was accepted"
  let (_, args) := evidence.original.proof.consumeMData.getAppFnArgs
  let reject (changed : Array Expr) : TermElabM Unit := do
    let forged : Tools.SourceCounterexample := {
      proof := mkAppN (mkConst ``Fml.not_valid_of_eval3Peel) changed
      report := evidence.original.report }
    unless (← Tools.sourceCounterexampleCandidateV1? goal forged).isNone do
      throwError "modified candidate/domain/arguments were accepted"
  let (_, #[valueType]) := (← inferType evidence.values).getAppFnArgs
    | throwError "expected the original candidate's argument list"
  let noValues := mkApp (mkConst ``List.nil [levelZero]) valueType
  reject (args.set! 2 noValues)
  let (``Tools.Cand.mk, candidateFields) := evidence.candidate.getAppFnArgs
    | throwError "expected the actual quoted candidate constructor"
  unless candidateFields.size == 6 do throwError "unexpected candidate fields"
  let (_, #[argumentType]) := (← inferType candidateFields[2]!).getAppFnArgs
    | throwError "expected the actual candidate argument list"
  let noArguments := mkApp (mkConst ``List.nil [levelZero]) argumentType
  let differentCandidate := mkAppN (mkConst ``Tools.Cand.mk) (candidateFields.set! 2 noArguments)
  reject (args.set! 3 (mkApp2 (mkConst ``Tools.Cand.tstate) evidence.contract differentCandidate))
  let otherDomain := mkApp (mkConst ``Tools.poolDom) (toExpr ([997] : List Int))
  reject (args.set! 1 otherDomain)
  let equalityType ← inferType evidence.failure
  let forgedFailure := mkApp2 (mkConst ``id [levelZero]) equalityType (mkConst ``True.intro)
  reject (args.set! 5 forgedFailure)
  unless (← Tools.refuteSourceCandidateV1? goal 0).isNone do
    throwError "zero budget must not search"
  unless (← Tools.refuteSourceCandidateV1? otherGoal 16).isNone do
    throwError "true specification was reported refuted"
  logInfo m!"SOURCE_CANDIDATE_V1: real counterexample retained; wrong goal/domain/arguments/candidate and forged proof plus zero-budget rejected; axioms {axioms}; argument equality axioms {argumentAxioms}"
