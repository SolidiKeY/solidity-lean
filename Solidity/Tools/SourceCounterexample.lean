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

end Solidity.Tools
