import Solidity.Frontend.Testing

/-! Native-plugin entry for the certified frontend's extended readings.
The final candidate is inspected and discarded; no result theorem is added.
The launcher must attest this command and its tactics execute compiled C. -/
namespace Solidity.Tools.FastMode
open Lean Elab Command Term Meta Solidity.Frontend

private partial def containsRecursive (N : Lean.Name) (e : Expr) (fuel : Nat := 8) : MetaM Bool := do
  if (e.find? (·.isConstOf ``Stmt.callRec)).isSome then return true
  if fuel == 0 then return false
  for name in e.getUsedConstants do
    if N.isPrefixOf name then
      if let some value := (← getConstInfo name).value? then
        if ← containsRecursive N value (fuel - 1) then return true
  return false

private def closed (stx : Term) : TermElabM Expr := do
  let term ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars term

private def noCallbackFrames (formula : Expr) : TermElabM Bool := do
  let check ← mkAppM ``Fml.callsBack #[toExpr false, ← Symex.evaluable formula]
  let goal ← mkFreshExprSyntheticOpaqueMVar (← mkEq check (toExpr false))
  tryCatchRuntimeEx (do
    let remaining ← Tactic.run goal.mvarId! (Tactic.evalTactic (← `(tactic| sol_no_callback)))
    return remaining.isEmpty) (fun _ => pure false)

/-- Unknown reduction is an error, never a guessed change of reading. -/
private def callbackValue (formula : Expr) : TermElabM Bool := do
  let check ← mkAppM ``Fml.callsBack #[toExpr false, ← Symex.evaluable formula]
  let value ← withTransparency .all <| reduce check
  if value.isConstOf ``Bool.false then return false
  if value.isConstOf ``Bool.true then return true
  throwError "native callback classification did not reduce to a Boolean"

/-- Audit the expression directly, including transient auxiliary declarations.
No declaration containing this final candidate is introduced for the audit. -/
private def standardProof (proof : Expr) : TermElabM Bool := do
  let mut pending := proof.getUsedConstants.toList
  let mut visited : Lean.NameSet := {}
  while !pending.isEmpty do
    let name :: rest := pending | break
    pending := rest
    if visited.contains name then continue
    visited := visited.insert name
    let info ← getConstInfo name
    match info with
    | .axiomInfo _ =>
      unless standardAxioms.contains name do return false
    | .quotInfo _ => pure ()
    | _ =>
      pending := info.type.getUsedConstants.toList ++ pending
      match info with
      | .defnInfo value => pending := value.value.getUsedConstants.toList ++ pending
      | .thmInfo value => pending := value.value.getUsedConstants.toList ++ pending
      | .opaqueInfo value => pending := value.value.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.ctors ++ pending
      | _ => pure ()
  return true

private def branch (index : Nat) (goal : MVarId) : TermElabM Json := do
  return Json.mkObj [("id", toJson s!"open/{index + 1}"),
    ("sequent", toJson (← Meta.ppGoal goal).pretty)]

private def outcome (status reason : String) (branches : Array Json := #[]) : Json :=
  Json.mkObj [("status", toJson status), ("reason", toJson reason),
    ("verification", toJson "native"), ("openBranches", toJson branches)]

private def searchExtended (target : Expr) (recursive callback share : Bool) : TermElabM Json := do
  let goal ← mkFreshExprSyntheticOpaqueMVar target
  let root := #[Json.mkObj [("id", toJson "root"), ("sequent", toJson (← ppExpr target).pretty)]]
  let pendingReason := if callback then "a recursive call under the callback reading (O7) its contract does not prove"
    else "a recursive call its callee's contract does not prove"
  let remaining ← if recursive then do
      let stx ← if callback then `(tactic| rec_auto_c) else `(tactic| rec_auto)
      let some remaining ← tryCatchRuntimeEx
          (some <$> Tactic.run goal.mvarId! (Tactic.evalTactic stx)) (fun _ => pure none)
        | return outcome "pending" pendingReason root
      pure remaining
    else
      withOptions (fun options => options.setBool `sol.prove.stopAtOpen true
          |>.setBool `sol.prove.sharedResidues share) <|
        Tactic.run goal.mvarId! (Tactic.evalTactic (← `(tactic| sol_prove)))
  unless remaining.isEmpty do
    let branches ← remaining.toArray.mapIdxM branch
    return outcome "pending" (if recursive then pendingReason else "open proof goals") branches
  let proof ← instantiateMVars goal
  if proof.hasMVar || proof.hasFVar then return outcome "error" "incomplete proof term" root
  Core.checkSystem "native candidate checking"
  let env ← getEnv
  let inferred ← match Kernel.check env {} proof with
    | .ok type => pure type
    | .error _ => throwError "native candidate failed detached kernel checking"
  Core.checkSystem "native candidate checking"
  unless Kernel.isDefEqGuarded env {} inferred target do
    throwError "native candidate does not have the exact source target type"
  Core.checkSystem "native candidate checking"
  let standard ← if proof.hasSorry then pure false else standardProof proof
  Core.checkSystem "native candidate audit"
  unless standard do
    return outcome (if recursive then "pending" else "unsupported")
      (if recursive then pendingReason else "proof uses nonstandard axioms") root
  return outcome "proved" ""

private def extendedRow (N : Lean.Name) (row : ImportRow) : TermElabM Json := withCurrHeartbeats do
  let raw ← testFormula N row
  let formula ← Symex.evaluable raw
  let recursive ← containsRecursive N (if row.tag == .specified then raw else formula)
  let callback ← if recursive then do pure (!(← noCallbackFrames raw)) else callbackValue raw
  unless recursive || callback do throwError "native extended entry received an ordinary reading"
  let target ← if callback then do
      let type ← closed (← `(ValidT (C := $(mkCIdent N))
        (.noCallback invariant[$(mkCIdent N)]) $(← Term.exprToSyntax raw)))
      pure (mkApp type.appFn! formula)
    else pure (mkApp2 (mkConst ``Fml.Valid) (mkConst N) formula)
  let shared := !recursive && testingShares target.appArg!
  let before ← Term.saveState
  let context ← readThe Core.Context
  let deadline := if context.maxHeartbeats == 0 then none
    else some (context.initHeartbeats + context.maxHeartbeats)
  let attempt (share : Bool) := tryCatchRuntimeEx
    (withOptions (·.setBool `sol.prove.sharedResidues false) <| searchExtended target recursive callback share)
    (fun error => return outcome "error" (← error.toMessageData.toString))
  let first ← attempt shared
  let result ← if (first.getObjValAs? String "status").toOption == some "proved" || !shared then
      pure first
    else do
      before.restore
      match deadline with
      | none => attempt false
      | some deadline =>
        let now ← IO.getNumHeartbeats
        let remaining := deadline - now
        if remaining == 0 then
          pure (outcome "error" "proof proposal exhausted the original heartbeat budget")
        else
          withTheReader Core.Context (fun context => {context with initHeartbeats := now, maxHeartbeats := remaining}) <|
            attempt false
  unless result matches .obj _ do throwError "extended search returned a non-object: {result.compress}"
  return result.setObjVal! "nativeStrategy" (toJson
    (if recursive then (if callback then "rec_auto_c" else "rec_auto") else "sol_prove"))

syntax (name := checkExtended) "#fast_meta " ident " ids " str " to " str : command

@[command_elab checkExtended]
def elabCheckExtended : CommandElab := fun stx => do
  let N ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let some requestText := stx[3].isStrLit? | throwError "expected literal source IDs"
  let some output := stx[5].isStrLit? | throwError "expected literal output path"
  let requested ← Lean.ofExcept (fromJson? (← Lean.ofExcept (Json.parse requestText)) : Except String (Array Int))
  let rows ← reportRows N
  let results : Array Json ← withScope (fun scope => {scope with openDecls := .simple `Solidity [] :: scope.openDecls}) <|
    liftTermElabM do
      let before ← Term.saveState
      try
        requested.mapM fun id => do
          let some row := rows.find? (·.sourceId == id) | throwError "unknown source obligation ID"
          unless row.status == .elaborated && row.tag != .internal && row.tag != .skip do
            throwError "native extended entry requires an eligible source obligation"
          let result ← tryCatchRuntimeEx (extendedRow N row)
            (fun error => return outcome "error" (← error.toMessageData.toString))
          unless result matches .obj _ do throwError "extended row returned a non-object: {result.compress}"
          let display := if row.sourceName.isEmpty then row.name else row.sourceName
          let signature := if row.sourceSignature.isEmpty then
            s!"{display}({",".intercalate (row.params.map Prod.snd)})" else row.sourceSignature
          let mut result := result
          for (key, value) in [("sourceId", toJson id), ("function", toJson display),
              ("signature", toJson signature), ("tag", toJson row.tag.toStr), ("reading", toJson "solc")] do
            result := result.setObjVal! key value
          return result
      finally before.restore
  IO.FS.writeFile output (toJson results).pretty

end Solidity.Tools.FastMode
