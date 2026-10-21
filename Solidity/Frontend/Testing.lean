import Solidity.Frontend.Problems
import Solidity.Calculus.SolSpec
import Solidity.Calculus.CallbackDerive
import Solidity.Calculus.Recursion

/-!
# Testing imported Solidity files

The machine-readable entry point used by `scripts/test-solidity.mjs`.
Every proved result has a kernel-checked declaration and an axiom check.
An unfinished search stays pending; import gaps remain visible.

A plain obligation whose formula hands control to a callee that may call
back (`Fml.callsBack false`: a `try`, a value call) is stated as
`ValidT .noCallback N.f.problem`, the callee changing the state as it may
(`docs/options.md`, O7), and proved by `sol_prove`'s walk of `ProvesC`; the
others as `⊢ N.f.problem`, whose `Valid` is the same reading there
(`validT_noCallback_iff`).  One with a recursive call (`Stmt.callRec`) is
stated as `Valid N.f.problem` and proved by `rec_auto`, each recursive call
by the contract `true`/`true` proved by induction over its frames
(`docs/kernel-port.md`, "Recursion"): the search does no induction.
-/

namespace Solidity.Frontend

open Lean Elab Command Meta

private def ImportRow.displayName (r : ImportRow) : String :=
  if r.sourceName.isEmpty then r.name else r.sourceName

private def ImportRow.signature (r : ImportRow) : String :=
  if r.sourceSignature.isEmpty then
    s!"{r.displayName}({",".intercalate (r.params.map Prod.snd)})"
  else r.sourceSignature

/-- `t`, elaborated with no metavariable left. -/
private def elabClosed (t : Term) : TermElabM Expr := do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- Whether the obligation `p` may hand control to a callee that calls back
under `transferSemantics:noCallback` (`Fml.callsBack false`), read off its
value; `true` where it does not reduce. -/
private def callsBackE (N p : Lean.Name) : TermElabM Bool := do
  let e ← elabClosed (← `(Fml.callsBack (C := $(mkCIdent N)) false $(mkCIdent p)))
  let v ← withTransparency .all <| whnf e
  return !v.isConstOf ``Bool.false

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

/-- Test one imported obligation. Search constructs a proof term; `addDecl`
checks it in the kernel before it can be reported as proved. Open goals are
pending; budget exhaustion is an error. Neither is evidence a claim is false. -/
def testObligation (N : Lean.Name) (r : ImportRow) (tail : TailMode := .solc) :
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
      let cb ← if r.tag == .specified || !r.writingCall then pure false
        else callsBackE N (f ++ `problem)
      -- a specification's obligation, scoped
      let spec? ← if r.tag == .specified then do
          let stx ← `(cspec[$(mkCIdent N)]{ $(mkIdent (.mkSimple r.name)) })
          let φ ← Term.elabTerm stx none
          Term.synthesizeSyntheticMVarsNoPostponing
          pure (some (← instantiateMVars φ))
        else pure none
      -- a recursive call: `rec_auto`, each call by its callee's contract
      -- (its `requires`/`ensures`, else `true`/`true`) proved by induction
      -- over the frames (a specified row has no `N.f.problem`: `(← …)` in a
      -- `&&` would run first)
      let recursive ← match spec? with
        | some φ => hasCallRec N φ
        | none => hasCallRec N (← Symex.evaluable (mkConst (f ++ `problem)))
      -- under the callback reading (O7) a recursive call is a point where
      -- control may leave (`Stmt.hasTransfer`, conservative: its frames are
      -- not unfolded), which no rule of `ProvesC` steps over, and a contract
      -- (`FunContract`) reads the run without callbacks (`docs/kernel-port.md`,
      -- "Recursion")
      if recursive && cb then
        return ("pending", "a recursive call under the callback reading (O7): no contract rule", .solc)
      if recursive then
        let (ty, goalTy) := match spec? with
          | some φ => (mkApp2 (mkConst ``Valid) C φ, mkApp2 (mkConst ``Valid) C φ)
          | none => (mkApp2 (mkConst ``Valid) C (mkConst (f ++ `problem)), mkConst ``True)
        -- the walk reads the formula by its value; the kernel unfolds it
        let goalTy ← if spec?.isSome then pure goalTy else
          pure (mkApp2 (mkConst ``Valid) C (← Symex.evaluable (mkConst (f ++ `problem))))
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
      let (ty, goalTy) ← if let some φ := spec? then do
          let ty := mkApp2 (mkConst ``Valid) C φ
          pure (ty, ty)
        else if cb then do
          -- the faithful reading: the callee may change the state
          let ty ← elabClosed (← `(ValidT (C := $(mkCIdent N)) .noCallback
            $(mkCIdent (f ++ `problem))))
          -- the walk reads the formula by its value; the kernel unfolds it
          pure (ty, mkApp ty.appFn! (← Symex.evaluable (mkConst (f ++ `problem))))
        else if mode == .clean then do
          -- the walk reads the formula by its value; the kernel unfolds it
          pure (ProofTree.provesE C (premised problem),
            ProofTree.provesE C (premised (← Symex.evaluable problem)))
        else
          let ty := ProofTree.provesE C problem
          pure (ty, ty)
      let g ← mkFreshExprSyntheticOpaqueMVar goalTy
      let goals ← if r.tag == .specified then do
          let tac ← `(tactic| sol_spec_try)
          Tactic.run g.mvarId! (Tactic.evalTactic tac)
        else if cb then do
          let tac ← `(tactic| sol_prove)
          -- only whether a leaf is left is reported: stop at the first
          withOptions (·.setBool `sol.prove.stopAtOpen true) <|
            Tactic.run g.mvarId! (Tactic.evalTactic tac)
        else do
          let out ← IO.mkRef (none : Option Derive.Search)
          let _ ← Tactic.run g.mvarId! do
            out.set (some (← scopedSearch g.mvarId!))
          let some s ← out.get | throwError "search did not run"
          pure s.open_
      unless goals.isEmpty do return ("pending", "open proof goals", mode)
      let proof ← instantiateMVars g
      if proof.hasMVar || proof.hasFVar then return ("error", "incomplete proof term", mode)
      let name := f ++ `tested
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := proof }
      unless (← collectAxioms name).all (standardAxioms.contains ·) do
        return ("unsupported", "proof uses nonstandard axioms", mode)
      return ("proved", "", mode))
      fun e => return ("error", ← e.toMessageData.toString, ← modeRef.get)

/-- Machine-readable testing entry point for a solc import. Listing performs
no proof search. Every selected import row is retained, including gaps and
functions whose specification has no plain box/diamond obligation. -/
syntax (name := solkeyTest) "#solkey_test " ident (&" only " str)?
  (&" from " num)? (&" count " num)? (&" listing")? " to " str : command

@[command_elab solkeyTest]
def elabSolkeyTest : CommandElab := fun stx => do
  let N ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let only? := if stx[2].isNone then none else stx[2][1].isStrLit?
  let first := if stx[3].isNone then 0 else stx[3][1].isNatLit?.getD 0
  let count? := if stx[4].isNone then none else stx[4][1].isNatLit?
  let listing := !stx[5].isNone
  let allRows ← reportRows N
  let selected := (allRows.filter fun r =>
    only?.all fun n => n == r.name || n == r.displayName || n == r.signature).drop first
  let rows := count?.map (selected.take ·) |>.getD selected
  if rows.isEmpty && (!allRows.isEmpty || only?.isSome) then
    throwError "#solkey_test: no functions selected"
  let output := stx[7].isStrLit?.getD ""
  -- Checkpoint before search, then after every function: a process timeout
  -- preserves completed results and explicitly marks the unattempted rows.
  let mut results : Array Json := rows.toArray.map fun r => Json.mkObj [
    ("function", toJson r.displayName), ("tag", toJson r.tag.toStr),
    ("signature", toJson r.signature),
    ("status", toJson "notRun"), ("reason", toJson "contract run interrupted"),
    ("reading", toJson "solc"), ("elapsedMs", toJson (0 : Nat))]
  IO.FS.writeFile output (Json.arr results).pretty
  -- the tails reading (O6): clean where every function exposes nothing
  let tail ← contractTailMode N allRows
  for r in rows, i in [:rows.length] do
    let t0 ← IO.monoMsNow
    let (status, reason, mode) ← if r.status != .elaborated then
        pure (r.status.toStr, r.reason, TailMode.solc)
      else if r.tag == .internal || r.tag == .skip then pure (r.tag.toStr, "", .solc)
      else if r.tag != .specified && r.tag.modality?.isNone then
        pure ("unsupported", s!"{r.tag.toStr}: no obligation", .solc)
      else if listing then pure ("ready", "", tail)
      else testObligation N r tail
    let elapsed ← IO.monoMsNow
    results := results.set! i <| Json.mkObj [
      ("function", toJson r.displayName), ("tag", toJson r.tag.toStr),
      ("signature", toJson r.signature),
      ("status", toJson status), ("reason", toJson reason),
      ("reading", toJson (if mode == .clean then "clean" else "solc")),
      ("elapsedMs", toJson (elapsed - t0))]
    IO.FS.writeFile output (Json.arr results).pretty

end Solidity.Frontend
