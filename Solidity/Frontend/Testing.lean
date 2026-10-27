import Solidity.Frontend.Problems
import Solidity.Calculus.SolSpec
import Solidity.Calculus.CallbackDerive
import Solidity.Calculus.Recursion
import Solidity.Calculus.RecursionCallback
import Solidity.Calculus.ProveChunked
import Solidity.Tools.Preconditions
import Solidity.Tools.SourceCounterexample

/-!
# Testing imported Solidity files

The machine-readable entry point used by `scripts/test-solidity.mjs`.
Every proved result has a kernel-checked declaration and an axiom check.
An unfinished search stays pending; import gaps remain visible.

A plain obligation whose formula hands control to a callee that may call
back (`Fml.callsBack false`: a `try`, a value call) is stated as
`ValidT .noCallback N.f.problem`, the callee changing the state as it may
(`docs/options.md`, O7), and proved by `sol_prove`'s walk of `ProvesC`; the
others as `⊢ N.f.problem`, whose `Fml.Valid` is the same reading there
(`validT_noCallback_iff`).  One with a recursive call (`Stmt.callRec`) is
stated as `Fml.Valid N.f.problem` and proved by `rec_auto`, each recursive call
by the contract `true`/`true` proved by induction over its frames
(`docs/kernel-port.md`, "Recursion"): the search does no induction.  Whether
it calls back is read off one frame of each unrolling (`sol_no_callback`);
where it does, it is stated as `ValidT .noCallback N.f.problem` and proved
by `rec_auto_c` (`Calculus/RecursionCallback.lean`).  A plain walk longer
than `oneCheckSteps` is checked in chunks (`Seq.proveChunked`), each leaf
searched as `sol_prove?` searches it (`Derive.searchLeaf`).
-/

namespace Solidity.Frontend

open Lean Elab Command Meta

private def ImportRow.displayName (r : ImportRow) : String :=
  if r.sourceName.isEmpty then r.name else r.sourceName

private def ImportRow.signature (r : ImportRow) : String :=
  if r.sourceSignature.isEmpty then
    s!"{r.displayName}({",".intercalate (r.params.map Prod.snd)})"
  else r.sourceSignature

/-- Normalize Solidity's integer type aliases without changing punctuation or
substrings of declaration names. Accept ABI-style selectors as well as the
source frontend's `uint`/`int` spelling. -/
def functionSelectorKey (selector : String) : String := Id.run do
  let alias (word : String) : String :=
    if word == "uint256" then "uint" else if word == "int256" then "int" else word
  let mut out := ""
  let mut word := ""
  for c in selector.toList do
    if c.isAlphanum || c == '_' || c == '$' then word := word.push c
    else
      out := (out ++ alias word).push c
      word := ""
  return out ++ alias word

/-- Select by source name, generated name, or a signature with type aliases. -/
def ImportRow.matchesSelector (r : ImportRow) (selector : String) : Bool :=
  selector == r.name || selector == r.displayName ||
    functionSelectorKey selector == functionSelectorKey r.signature

/-- `t`, elaborated with no metavariable left. -/
private def elabClosed (t : Term) : TermElabM Expr := do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- Whether the obligation `p` may hand control to a callee that calls back
under `transferSemantics:noCallback` (`Fml.callsBack false`), run as compiled
code on its value (`Symex.evaluable`: a `whnf` of it may pass `maxRecDepth`);
`true` where it does not run. -/
private def callsBackE (N : Lean.Name) (φ : Expr) : TermElabM Bool := do
  let φ ← Symex.evaluable φ
  let e ← elabClosed (← `(Fml.callsBack (C := $(mkCIdent N)) false $(← Term.exprToSyntax φ)))
  tryCatchRuntimeEx (unsafe evalExpr Bool (mkConst ``Bool) e) fun _ => pure true

/-- Whether the obligation `p`, which has a recursive call, provably hands
control to no callee under `transferSemantics:noCallback`: `sol_no_callback`
reads each unrolling off one frame (its `whnf` would unroll them). -/
private def noCallbackRecE (N : Lean.Name) (φ : Expr) : TermElabM Bool := do
  let φ ← Symex.evaluable φ
  let ty ← elabClosed (← `(Fml.callsBack (C := $(mkCIdent N)) false
    $(← Term.exprToSyntax φ) = false))
  let g ← mkFreshExprSyntheticOpaqueMVar ty
  let tac ← `(tactic| sol_no_callback)
  tryCatchRuntimeEx (do
      let gs ← Tactic.run g.mvarId! (Tactic.evalTactic tac)
      return gs.isEmpty)
    fun _ => pure false

/-- Whether `e`, or a declaration of the import `N` it names, has a
recursive call (`Stmt.callRec`). -/
private partial def hasCallRec (N : Lean.Name) (e : Expr) (fuel : Nat := 8) : MetaM Bool := do
  if (e.find? (·.isConstOf ``Stmt.callRec)).isSome then return true
  if fuel == 0 then return false
  for c in e.getUsedConstants do
    if N.isPrefixOf c then
      if let some v := (← getConstInfo c).value? then
        if ← hasCallRec N v (fuel - 1) then return true
  return false

/-- Whether the program `n` exposes nothing (`Prog.exposesNone`), reduced
by `whnf`; `false` where it does not reduce. -/
private def exposesNoneE (n : Lean.Name) : TermElabM Bool := do
  let e ← elabClosed (← `(Prog.exposesNone $(mkCIdent n)))
  let v ← withTransparency .all <| whnf e
  return v.isConstOf ``Bool.true

/-- **The tails reading of the import `N`** (`docs/options.md`, O6): `.clean`
when every function a transaction may run (every row but an internal one)
elaborated, takes no storage reference, and exposes nothing
(`Prog.exposesNone`), so that clean tails are the contract's invariant
(`ReachableBy.cleanTail`); `.solc` otherwise. -/
def contractTailMode (N : Lean.Name) (rows : List ImportRow) : CommandElabM TailMode :=
  liftTermElabM do
    for r in rows do
      if r.tag == .internal then continue
      unless r.status == .elaborated do return .solc
      if r.paramTypes.any (fun t => t matches .alias _) then return .solc
      let ok ← tryCatchRuntimeEx (exposesNoneE (r.declName N)) fun _ => pure false
      unless ok do return .solc
    return .clean

/-- The longest walk a test checks in one kernel check; a longer one is
checked `chunkSteps` steps at a time (`sol_prove (chunk := n)`,
`Calculus/ProveChunked.lean`), as one check of it may pass the memory a
session has (`docs/loops.md`). -/
def oneCheckSteps : Nat := 1024

/-- The steps of a chunk of a walk past `oneCheckSteps`. -/
def chunkSteps : Nat := 128

/-- Retain an exact-goal refutation only after kernel and transitive axiom
checks. JSON is presentation of the candidate used by that same proof. -/
private def testCounterexample (ty : Expr) (name : Lean.Name) (r : ImportRow) :
    TermElabM (Option Json) := do
  let saved ← Term.saveState
  let messages ← Core.getMessageLog
  let result ← withCurrHeartbeats <| tryCatchRuntimeEx (do
    let some witness ← Tools.refuteSource? ty | return none
    if witness.proof.hasMVar || witness.proof.hasFVar || witness.proof.hasSorry then return none
    addDecl <| .thmDecl {name, levelParams := [], type := mkNot ty, value := witness.proof}
    let axioms ← collectAxioms name
    unless axioms.all (standardAxioms.contains ·) do return none
    let .ok arguments := witness.report.getObjValAs? (Array Json) "arguments" | return none
    let arguments := arguments.map fun argument =>
      match argument.getObjValAs? String "modelName" with
      | .error _ => argument
      | .ok modelName => match List.findIdx? (fun (p : String × String) => p.1 == modelName) r.params with
        | none => argument
        | some index => argument.setObjVal! "paramIndex" (toJson index)
    return some <| witness.report
      |>.setObjVal! "arguments" (toJson arguments)
      |>.setObjVal! "certified" (toJson true)
      |>.setObjVal! "goalKind" (toJson "fmlValid")
      |>.setObjVal! "certificateDeclaration" (toJson name.toString)
      |>.setObjVal! "axioms" (toJson (axioms.map Lean.Name.toString)))
    fun _ => pure none
  if result.isNone then saved.restore
  else Core.setMessageLog messages
  return result
/-- The original source obligation, including a specified function's clauses. -/
def testFormula (N : Lean.Name) (r : ImportRow) : TermElabM Expr := do
  if r.tag != .specified then return mkConst (r.declName N ++ `problem)
  let stx ← `(cspec[$(mkCIdent N)]{ $(mkIdent (.mkSimple r.name)) })
  let φ ← Term.withoutErrToSorry <| Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  if φ.hasSorry then throwError "the specification does not elaborate"
  return φ

/-- The same tails premise used by source verification, for inspection. -/
def testTailMode (N : Lean.Name) (r : ImportRow) (tail : TailMode) (φ : Expr) :
    TermElabM TailMode := do
  if tail != .clean || r.tag == .specified then return .solc
  if ← hasCallRec N (← Symex.evaluable φ) then return .solc
  return if ← callsBackE N φ then .solc else .clean

/-- Whether a proof tree of the ordinary calculus can describe this obligation. -/
def testOrdinaryTree (N : Lean.Name) (φ : Expr) : TermElabM Bool := do
  if ← hasCallRec N (← Symex.evaluable φ) then return false
  return !(← callsBackE N φ)

/-- Test one imported obligation. Search constructs a proof term; `addDecl`
checks it in the kernel before it can be reported as proved. Open goals are
pending; budget exhaustion is an error. Neither is evidence a claim is false. -/
def testObligation (N : Lean.Name) (r : ImportRow) (tail : TailMode := .solc)
    (showGoals : Bool := false)
    (counterexampleOutput : Option (IO.Ref (Option Json)) := none) :
    CommandElabM (String × String × TailMode) := do
  let f := r.declName N
  let env ← getEnv
  unless r.tag == .specified || env.contains (f ++ `problem) do
    return ("unsupported", "no scoped obligation", .solc)
  -- the reading an obligation is stated under, kept for an error past that point
  let modeRef ← IO.mkRef TailMode.solc
  withScope (fun sc => { sc with openDecls := .simple `Solidity [] :: sc.openDecls }) <|
    liftTermElabM <| withCurrHeartbeats <| tryCatchRuntimeEx (do
      let C := mkConst N
      -- a specification's obligation, scoped
      let spec? ← if r.tag == .specified then do
          -- a specification that does not elaborate is an error, not a
          -- `sorry`; logged too, as the import reports it
          let φ ← try
              testFormula N r
            catch e => logException e; throw e
          if φ.hasSorry then throwError "the specification does not elaborate"
          pure (some φ)
        else pure none
      -- a recursive call: `rec_auto`, each call by its callee's contract
      -- (its `requires`/`ensures`, else `true`/`true`) proved by induction
      -- over the frames (a specified row has no `N.f.problem`: `(← …)` in a
      -- `&&` would run first)
      let recursive ← match spec? with
        | some φ => hasCallRec N φ
        | none => hasCallRec N (← Symex.evaluable (mkConst (f ++ `problem)))
      -- the callback reading (O7): a recursive call's frames read off one
      -- (`sol_no_callback`), not unrolled by `whnf`
      let obligation := spec?.getD (mkConst (f ++ `problem))
      let cb ← if recursive then pure !(← noCallbackRecE N obligation)
        else callsBackE N obligation
      let callbackTy (φ : Expr) : TermElabM Expr := do
        elabClosed (← `(ValidT (C := $(mkCIdent N))
          (.noCallback invariant[$(mkCIdent N)]) $(← Term.exprToSyntax φ)))
      -- a recursive call that may call back, or past a callee that may:
      -- `rec_auto_c`, each call read without callbacks where nothing calls
      -- back, else by a contract over the callback runs (`ProvesC.recContract`)
      if recursive && cb then
        let ty ← callbackTy obligation
        -- the walk reads the formula by its value; the kernel unfolds it
        let goalTy := mkApp ty.appFn! (← Symex.evaluable obligation)
        let g ← mkFreshExprSyntheticOpaqueMVar goalTy
        let tac ← `(tactic| rec_auto_c)
        let pendingMsg := "a recursive call under the callback reading (O7) its contract does not prove"
        let some goals ← tryCatchRuntimeEx (some <$> Tactic.run g.mvarId! (Tactic.evalTactic tac))
            fun _ => pure none
          | return ("pending", pendingMsg, .solc)
        unless goals.isEmpty do return ("pending", pendingMsg, .solc)
        let proof ← instantiateMVars g
        if proof.hasMVar || proof.hasFVar then return ("error", "incomplete proof term", .solc)
        let name := f ++ `tested
        addDecl <| .thmDecl { name, levelParams := [], type := ty, value := proof }
        unless (← collectAxioms name).all (standardAxioms.contains ·) do
          return ("pending", pendingMsg, .solc)
        return ("proved", "", .solc)
      if recursive then
        let (ty, goalTy) := match spec? with
          | some φ => (mkApp2 (mkConst ``Fml.Valid) C φ, mkApp2 (mkConst ``Fml.Valid) C φ)
          | none => (mkApp2 (mkConst ``Fml.Valid) C (mkConst (f ++ `problem)), mkConst ``True)
        -- the walk reads the formula by its value; the kernel unfolds it
        let goalTy ← if spec?.isSome then pure goalTy else
          pure (mkApp2 (mkConst ``Fml.Valid) C (← Symex.evaluable (mkConst (f ++ `problem))))
        let g ← mkFreshExprSyntheticOpaqueMVar goalTy
        let tac ← `(tactic| rec_auto)
        let pendingMsg := "a recursive call its callee's contract does not prove"
        let some goals ← tryCatchRuntimeEx (some <$> Tactic.run g.mvarId! (Tactic.evalTactic tac))
            fun _ => pure none
          | return ("pending", pendingMsg, .solc)
        unless goals.isEmpty do return ("pending", pendingMsg, .solc)
        let proof ← instantiateMVars g
        if proof.hasMVar || proof.hasFVar then return ("error", "incomplete proof term", .solc)
        let name := f ++ `tested
        addDecl <| .thmDecl { name, levelParams := [], type := ty, value := proof }
        unless (← collectAxioms name).all (standardAxioms.contains ·) do
          return ("pending", pendingMsg, .solc)
        return ("proved", "", .solc)
      -- the clean-tails reading (O6): a plain obligation of a contract whose
      -- functions expose nothing, under the premise `cleanTail(storage) = true`
      let mode : TailMode := if tail == .clean && spec?.isNone && !cb then .clean else .solc
      modeRef.set mode
      let problem := mkConst (f ++ `problem)
      let premised (φ : Expr) : Expr :=
        if mode == .clean then mkAppN (mkConst ``Fml.imp) #[C, ctxE [],
          mkApp2 (mkConst ``Fml.cleanTail) C (ctxE []), φ] else φ
      let (ty, goalTy) ← if cb then do
          -- Specifications use their actual formula too: they need not have
          -- a generated `problem` declaration.
          let ty ← callbackTy obligation
          pure (ty, mkApp ty.appFn! (← Symex.evaluable obligation))
        else if let some φ := spec? then do
          let ty := mkApp2 (mkConst ``Fml.Valid) C φ
          pure (ty, ty)
        else if mode == .clean then do
          -- the walk reads the formula by its value; the kernel unfolds it
          pure (ProofTree.provesE C (premised problem),
            ProofTree.provesE C (premised (← Symex.evaluable problem)))
        else
          let ty := ProofTree.provesE C problem
          pure (ty, ty)
      let g ← mkFreshExprSyntheticOpaqueMVar goalTy
      let goals ← if cb then do
          let tac ← `(tactic| sol_prove)
          -- only whether a leaf is left is reported: stop at the first
          withOptions (·.setBool `sol.prove.stopAtOpen true) <|
            Tactic.run g.mvarId! (Tactic.evalTactic tac)
        else if r.tag == .specified then do
          let tac ← `(tactic| sol_spec_try)
          Tactic.run g.mvarId! (Tactic.evalTactic tac)
        else do
          let out ← IO.mkRef (none : Option Derive.Search)
          let long ← IO.mkRef false
          let _ ← Tactic.run g.mvarId! do
            -- a walk past one kernel check: in chunks, each leaf searched
            try out.set (some (← scopedSearch g.mvarId! (oneCheck := oneCheckSteps)))
            catch e =>
              unless (← e.toMessageData.toString).startsWith Seq.longWalkNote do throw e
              long.set true
          if ← long.get then
            Tactic.run g.mvarId! do
              let left ← Seq.proveChunked g.mvarId! chunkSteps fun l => do
                pure (if (← Derive.searchLeaf l Seq.goalFits).isSome then [] else [l])
              Tactic.setGoals left
          else
            let some s ← out.get | throwError "search did not run"
            pure s.open_
      unless goals.isEmpty do
        if r.tag == .specified && !cb then
          if let some output := counterexampleOutput then
            if let some witness ← testCounterexample ty (f ++ `refuted) r then
              output.set (some witness)
              return ("refuted", "kernel-checked counterexample to the tested obligation", mode)
        let detail ← if showGoals then do
            let messages ← goals.mapM fun g => return (← Meta.ppGoal g).pretty
            pure ("open proof goals\n" ++ "\n\n".intercalate messages)
          else pure "open proof goals"
        return ("pending", detail, mode)
      let proof ← instantiateMVars g
      if proof.hasMVar || proof.hasFVar then return ("error", "incomplete proof term", mode)
      let name := f ++ `tested
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := proof }
      unless (← collectAxioms name).all (standardAxioms.contains ·) do
        return ("unsupported", "proof uses nonstandard axioms", mode)
      return ("proved", "", mode))
      fun e => return ("error", ← e.toMessageData.toString, ← modeRef.get)

/-- Check a specified row's entry condition separately from its postcondition. -/
def testPreconditions (N : Lean.Name) (r : ImportRow) : CommandElabM (String × String) :=
  withScope (fun sc => { sc with openDecls := .simple `Solidity [] :: sc.openDecls }) <|
    liftTermElabM <| withCurrHeartbeats <| tryCatchRuntimeEx (do
      let φ ← elabClosed (← `(cspec[$(mkCIdent N)]{ $(mkIdent (.mkSimple r.name)) }))
      let name := r.declName N ++ `entryAudited
      match ← Tools.auditPreconditions φ name with
      | .impossible => pure ("impossible", s!"kernel-checked: {name}")
      | .possible => pure ("possible", s!"kernel-checked: {name}")
      | .unknown reason => pure ("unknown", reason))
    fun e => do pure ("unknown", ← e.toMessageData.toString)

/-- Machine-readable testing entry point for a solc import. Listing performs
no proof search. Every selected import row is retained, including gaps and
functions whose specification has no plain box/diamond obligation. -/
syntax (name := solkeyTest) "#solkey_test " ident (&" only " str)?
  (&" from " num)? (&" count " num)? (&" listing")? (&" audit_preconditions")?
  (&" counterexamples")? " to " str : command

@[command_elab solkeyTest]
def elabSolkeyTest : CommandElab := fun stx => do
  let N ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let only? := if stx[2].isNone then none else stx[2][1].isStrLit?
  let first := if stx[3].isNone then 0 else stx[3][1].isNatLit?.getD 0
  let count? := if stx[4].isNone then none else stx[4][1].isNatLit?
  let listing := !stx[5].isNone
  let audit := !stx[6].isNone
  let counterexamples := !stx[7].isNone
  if listing && audit then throwError "precondition auditing requires verification, not listing"
  if listing && counterexamples then throwError "counterexample search requires verification, not listing"
  let auditFields (status reason : String) : List (String × Json) :=
    if audit then [("preconditions", toJson status), ("preconditionReason", toJson reason)] else []
  let allRows ← reportRows N
  let selected := (allRows.filter fun r => only?.all r.matchesSelector).drop first
  let rows := count?.map (selected.take ·) |>.getD selected
  if rows.isEmpty && (!allRows.isEmpty || only?.isSome) then
    throwError "#solkey_test: no functions selected"
  let output := stx[9].isStrLit?.getD ""
  -- Checkpoint before search, then after every function: a process timeout
  -- preserves completed results and explicitly marks the unattempted rows.
  let mut results : Array Json := rows.toArray.map fun r => Json.mkObj ([
    ("function", toJson r.displayName), ("tag", toJson r.tag.toStr),
    ("signature", toJson r.signature),
    ("sourceId", toJson r.sourceId),
    ("invalidSpecification", toJson ((r.sourceDiagnostic.map (·.name)) == some `solidity.specificationSyntax)),
    ("status", toJson "notRun"), ("reason", toJson "contract run interrupted"),
    ("reading", toJson "solc"), ("elapsedMs", toJson (0 : Nat))] ++
      auditFields "notRun" "contract run interrupted")
  IO.FS.writeFile output (Json.arr results).pretty
  -- the tails reading (O6): clean where every function exposes nothing
  let tail ← contractTailMode N allRows
  for r in rows, i in [:rows.length] do
    let t0 ← IO.monoMsNow
    let witnessOutput ← IO.mkRef (none : Option Json)
    let (status, reason, mode) ← if r.status != .elaborated then
        pure (r.status.toStr, r.reason, TailMode.solc)
      else if r.tag == .internal || r.tag == .skip then pure (r.tag.toStr, "", .solc)
      else if r.tag != .specified && r.tag.modality?.isNone then
        pure ("unsupported", s!"{r.tag.toStr}: no obligation", .solc)
      else if listing then pure ("ready", "", tail)
      else testObligation N r tail (counterexampleOutput := if counterexamples then some witnessOutput else none)
    let (preconditions, preconditionReason) ← if !audit then pure ("notRequested", "")
      else if r.status != .elaborated || r.tag != .specified then
        pure ("notApplicable", "no admitted function specification")
      else testPreconditions N r
    let elapsed ← IO.monoMsNow
    let witness ← witnessOutput.get
    results := results.set! i <| Json.mkObj ([
      ("function", toJson r.displayName), ("tag", toJson r.tag.toStr),
      ("signature", toJson r.signature),
      ("sourceId", toJson r.sourceId),
      ("invalidSpecification", toJson ((r.sourceDiagnostic.map (·.name)) == some `solidity.specificationSyntax)),
      ("status", toJson status), ("reason", toJson reason),
      ("reading", toJson (if mode == .clean then "clean" else "solc")),
      ("elapsedMs", toJson (elapsed - t0))] ++ auditFields preconditions preconditionReason ++
        (witness.map (fun value => [("counterexample", value)]) |>.getD []))
    IO.FS.writeFile output (Json.arr results).pretty

end Solidity.Frontend
