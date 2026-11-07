import Solidity.Tools.Counterexample

/-!
# A certified model witness for the exact tested formula

`refuteSource?` accepts the original goal type `Fml.Valid φ`. It searches once,
then checks a proof of that exact goal's negation using the same candidate that
is serialized. Search and certification failures return `none`. The caller must
retain the proof with `addDecl` at the exact negated goal and check its axioms
before reporting a refutation to a client.

The first fragment has primitive storage and named primitive input binders.
Callback, recursive and other goal readings are filtered by the testing frontend.
These are arbitrary typed model prestates, not constructor-reachable transaction
traces. The optional outcome reports only post-storage or a halt; it says nothing
about a complete post-ledger or heap. All numbers are decimal JSON strings,
except Boolean argument values. The external-response table is explicitly empty.
-/

namespace Solidity.Tools

open Lean Elab Term Meta

/-- A proof and presentation of the same candidate. The proof's retained
declaration and axiom policy belong to the frontend that selected the goal. -/
structure SourceCounterexample where
  proof : Expr
  report : Json

/-- Presentation only: callers must not infer a certificate from this JSON. -/
def sourceArgumentJson (modelName : String) (value : Semantics.CallValue) : Json :=
  let (type, value) : String × Json := match value with
    | .bool b => ("bool", toJson b)
    | .uint n => ("uint", toJson (toString n.1))
    | .int n => ("int", toJson (toString n.1))
  Json.mkObj [("modelName", toJson modelName), ("type", toJson type), ("value", value)]

/-- Present the actual model prestate and its limited outcome. This serializer
does not itself certify the witness or assert transaction reachability. -/
def sourceWitnessJson (C : Contract) (w : Witness C) : Json :=
  let c := w.cand
  let transaction := Json.mkObj [
    ("msgSender", toJson (toString c.tx.msgSender.1)),
    ("selfAddress", toJson (toString c.tx.selfAddress.1)),
    ("msgValue", toJson (toString c.tx.msgValue.1)),
    ("timestamp", toJson (toString c.tx.timestamp.1)),
    ("ext", Json.arr #[])]
  let ledger := c.net.map fun (address, amount) => Json.mkObj [
    ("address", toJson (toString address.1)), ("amount", toJson (toString amount))]
  let fields := [
    ("kind", toJson "model-state"),
    ("arguments", Json.arr ((c.args.map fun (name, value) => sourceArgumentJson name value).toArray)),
    ("transaction", transaction),
    ("initialStorage", toJson (fmtStorageLine C c.st true)),
    ("initialLedger", Json.arr ledger.toArray),
    ("initialBalance", toJson (toString c.bal.1)),
    ("lines", toJson (w.lines C))]
  let outcome := match w.outcome with
    | none => []
    | some (.error halt) => [("outcome", Json.mkObj [
        ("kind", toJson "halt"), ("halt", toJson (fmtHalt halt))])]
    | some (.ok storage) => [("outcome", Json.mkObj [
        ("kind", toJson "postStorage"), ("storage", toJson (fmtStorageLine C storage true))])]
  Json.mkObj (fields ++ outcome)

private def primitivePrefix {C : Contract} : {Γ : Ctx} → Fml C Γ → Bool
  | _, .all _ _ body => primitivePrefix body
  | _, .bind _ _ (.val _) body => primitivePrefix body
  | _, .bind .. => false
  | _, _ => true

/-- Execute the bounded model search directly. This returns a runtime
counterexample, not a Lean proof or certificate. -/
def directSourceWitness (C : Contract) (φ : Fml C []) : Option Json := do
  unless C.vars.all (fun (_, type) => type.isPrimitive) && primitivePrefix φ do none
  let ps := Fml.params φ
  let names := ps.filterMap fun
    | (.user name, _) => some name
    | _ => none
  unless names.length == ps.length && names.eraseDups.length == names.length &&
      names.all (fun name => !name.isEmpty) do none
  let witness ← (searchFml C φ 256).witness
  let c := witness.cand
  unless c.tx.ext.isEmpty do none
  unless Fml.eval3Peel (poolDom c.argInts) c.vals (c.tstate C) φ == .ff do none
  return sourceWitnessJson C witness
    |>.setObjVal! "certified" (toJson false)
    |>.setObjVal! "goalKind" (toJson "fmlValid")

/-- Search a narrow source-friendly fragment and return a proof of the exact
original `Fml.Valid` goal's negation with the same model witness. Budget zero
does no search; the initial search budget is capped at 256 candidates, followed
by the existing searcher's bounded 64-round shrinking phase. -/
def refuteSource? (goalTy : Expr) (budget : Nat := 256) : TermElabM (Option SourceCounterexample) := do
  if budget == 0 then return none
  let saved ← Term.saveState
  let messages ← Core.getMessageLog
  let result ← withCurrHeartbeats <| tryCatchRuntimeEx (do
    let goalTy ← instantiateMVars goalTy
    if goalTy.hasMVar || goalTy.hasFVar || goalTy.hasSorry then return none
    let (``Fml.Valid, #[cE, φE]) := goalTy.consumeMData.getAppFnArgs | return none
    unless cE.isConst do return none
    unless ← isProp goalTy do return none
    unless ← isDefEq (← inferType cE) (mkConst ``Contract) do return none
    let (``Fml, #[formulaC, Γ]) := (← whnf (← inferType φE)).getAppFnArgs | return none
    unless ← isDefEq formulaC cE do return none
    unless (← whnf Γ).isAppOf ``List.nil do return none
    let C ← unsafe evalExpr Contract (mkConst ``Contract) cE
    unless C.vars.all (fun (_, type) => type.isPrimitive) do return none
    let φ ← unsafe evalExpr (Fml C []) (← inferType φE) (← Symex.evaluable φE)
    unless primitivePrefix φ do return none
    let ps := Fml.params φ
    let names := ps.filterMap fun
      | (.user name, _) => some name
      | _ => none
    unless names.length == ps.length && names.eraseDups.length == names.length &&
        names.all (fun name => !name.isEmpty) do return none
    let search := searchFml C φ (min budget 256)
    let some witness := search.witness | return none
    let c := witness.cand
    -- The current search proposes an empty table. Never serialize a different
    -- table as empty if a future search starts generating external responses.
    unless c.tx.ext.isEmpty do return none
    unless Fml.eval3Peel (poolDom c.argInts) c.vals (c.tstate C) φ = .ff do return none
    let domE := mkApp (mkConst ``poolDom) (toExpr c.argInts)
    let stateE := mkApp2 (mkConst ``Cand.tstate) cE (c.quote cE)
    let valsE := toExpr c.vals
    let evaluated ← mkAppM ``Fml.eval3Peel #[domE, valsE, stateE, φE]
    let failure ← mkDecideProof (← mkEq evaluated (mkConst ``Tri.ff))
    let proof ← instantiateMVars (← mkAppM ``Fml.not_valid_of_eval3Peel #[valsE, stateE, failure])
    if proof.hasMVar || proof.hasFVar || proof.hasSorry then return none
    let type := mkNot goalTy
    unless ← isDefEq (← inferType proof) type do return none
    let name ← mkFreshUserName `_source_counterexample_certificate
    let declaration := Declaration.thmDecl {name, levelParams := [], type, value := proof}
    let options := maxHeartbeats.set (← getOptions) 100000
    match Kernel.Environment.addDecl (← getEnv).toKernelEnv options declaration with
    | .error _ => pure none
    | .ok _ => pure (some {proof, report := sourceWitnessJson C witness}))
    fun _ => pure none
  if result.isNone then saved.restore
  else Core.setMessageLog messages
  return result


/-- Literal source argument bindings. This additive projection does not change
`Cand.vals` or assert an equivalence for arbitrary `FreshNames` instances. The
companion must certify equality with the original proof's actual values. -/
def Cand.sourceValuesV1 {C : Contract} (candidate : Cand C) :
    List (Var × Semantics.CallValue) :=
  candidate.args.map fun (name, value) => (Var.user name, value)

/-- Additive V1 companion guarding the editor regression where metadata is
attached to a second searched candidate. Every expression is closed and checked
against the exact original proof application, with independent kernel validation. `candidate` has type `Cand C`;
`failure` proves the evaluator equality at the retained domain/arguments/state.
A retained kernel-checked equality binds the original proof values to that
candidate's literal source user-name/value pairs. It makes no general
`Cand.vals`/`FreshNames` equivalence claim.
The existing proof and JSON are retained unchanged; JSON remains presentation only. No source span or failed
postcondition attribution is inferred; those require a separate correspondence.
Callers retain and axiom-audit both the original proof and argument equality. -/
structure SourceCounterexampleCandidateV1 where
  original : SourceCounterexample
  contract : Expr
  formula : Expr
  candidate : Expr
  domain : Expr
  values : Expr
  valuesEquation : Expr
  state : Expr
  failure : Expr

/-- Recover the candidate used by an existing exact-goal certificate, without a
second search. Unexpected proof shapes, a different goal, and inconsistent
state/domain/argument expressions fail closed. This companion accepts no source
range and cannot certify one supplied by a caller. -/
def sourceCounterexampleCandidateV1? (goalTy : Expr) (original : SourceCounterexample) :
    TermElabM (Option SourceCounterexampleCandidateV1) := do
  let saved ← Term.saveState
  let messages ← Core.getMessageLog
  let result ← tryCatchRuntimeEx (do
    if original.proof.hasMVar || original.proof.hasFVar || original.proof.hasSorry ||
        original.proof.hasLevelMVar then return none
    let goalTy ← instantiateMVars goalTy
    let proof ← instantiateMVars original.proof
    if [goalTy, proof].any (fun e => e.hasMVar || e.hasFVar || e.hasSorry) then return none
    let (``Fml.Valid, #[goalC, goalFormula]) := goalTy.consumeMData.getAppFnArgs | return none
    let (``Fml.not_valid_of_eval3Peel, #[cE, domE, valsE, stateE, formulaE, failureE]) :=
      proof.consumeMData.getAppFnArgs | return none
    unless ← isDefEq (← inferType proof) (mkNot goalTy) do return none
    -- A public Expr input needs kernel validation, not only inferred types.
    -- Never exceed the existing producer's 100000-heartbeat kernel ceiling,
    -- or a caller's smaller nonzero budget.
    let options ← getOptions
    let currentLimit := maxHeartbeats.get options
    let limit := if currentLimit == 0 then 100000 else min currentLimit 100000
    let options := maxHeartbeats.set options limit
    let checked (type value : Expr) : TermElabM Bool := do
      let name ← mkFreshUserName `_source_candidate_v1_certificate
      let declaration := Declaration.thmDecl {name, levelParams := [], type, value}
      match Kernel.Environment.addDecl (← getEnv).toKernelEnv options declaration with
      | .error _ => return false
      | .ok _ => return true
    unless ← checked (mkNot goalTy) proof do return none
    unless ← isDefEq cE goalC do return none
    unless ← isDefEq formulaE goalFormula do return none
    let (``Cand.tstate, #[stateC, candidateE]) := stateE.consumeMData.getAppFnArgs | return none
    unless ← isDefEq stateC cE do return none
    unless ← isDefEq (← inferType candidateE) (mkApp (mkConst ``Cand) cE) do return none
    let candidateVals := mkApp2 (mkConst ``Cand.sourceValuesV1) cE candidateE
    let valuesType ← mkEq valsE candidateVals
    let valuesEquation ← instantiateMVars (← mkDecideProof valuesType)
    unless ← checked valuesType valuesEquation do return none
    let candidateInts ← mkAppM ``Cand.argInts #[candidateE]
    unless ← withTransparency .all (isDefEq domE (mkApp (mkConst ``poolDom) candidateInts)) do return none
    let evaluated ← mkAppM ``Fml.eval3Peel #[domE, valsE, stateE, formulaE]
    unless ← isDefEq (← inferType failureE) (← mkEq evaluated (mkConst ``Tri.ff)) do return none
    let expressions := [cE, formulaE, candidateE, domE, valsE, valuesEquation, stateE, failureE]
    if expressions.any (fun e => e.hasMVar || e.hasFVar || e.hasSorry) then return none
    return some {
      original := original
      contract := cE
      formula := formulaE
      candidate := candidateE
      domain := domE
      values := valsE
      valuesEquation := valuesEquation
      state := stateE
      failure := failureE })
    fun _ => pure none
  if result.isNone then saved.restore
  else Core.setMessageLog messages
  return result

/-- Search once through the unchanged producer, then expose only the candidate
already present in its exact-goal certificate. Existing budgets and shrinking
remain those of `refuteSource?`; this does not run an attribution search. -/
def refuteSourceCandidateV1? (goalTy : Expr) (budget : Nat := 256) :
    TermElabM (Option SourceCounterexampleCandidateV1) := do
  let some original ← refuteSource? goalTy budget | return none
  sourceCounterexampleCandidateV1? goalTy original

end Solidity.Tools
