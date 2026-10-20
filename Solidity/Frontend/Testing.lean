import Solidity.Frontend.Problems
import Solidity.Calculus.SolSpec
import Solidity.Calculus.CallbackDerive

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
(`validT_noCallback_iff`).
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

/-- Test one imported obligation. Search constructs a proof term; `addDecl`
checks it in the kernel before it can be reported as proved. Open goals are
pending; budget exhaustion is an error. Neither is evidence a claim is false. -/
def testObligation (N : Lean.Name) (r : ImportRow) : CommandElabM (String × String) := do
  let f := r.declName N
  let env ← getEnv
  unless r.tag == .specified || env.contains (f ++ `problem) do
    return ("unsupported", "no scoped obligation")
  withScope (fun sc => { sc with openDecls := .simple `Solidity [] :: sc.openDecls }) <|
    liftTermElabM <| withCurrHeartbeats <| tryCatchRuntimeEx (do
      let C := mkConst N
      let cb ← if r.tag == .specified || !r.writingCall then pure false
        else callsBackE N (f ++ `problem)
      let (ty, goalTy) ← if r.tag == .specified then do
          let stx ← `(cspec[$(mkCIdent N)]{ $(mkIdent (.mkSimple r.name)) })
          let φ ← Term.elabTerm stx none
          Term.synthesizeSyntheticMVarsNoPostponing
          let ty := mkApp2 (mkConst ``Valid) C (← instantiateMVars φ)
          pure (ty, ty)
        else if cb then do
          -- the faithful reading: the callee may change the state
          let ty ← elabClosed (← `(ValidT (C := $(mkCIdent N)) .noCallback
            $(mkCIdent (f ++ `problem))))
          -- the walk reads the formula by its value; the kernel unfolds it
          pure (ty, mkApp ty.appFn! (← Symex.evaluable (mkConst (f ++ `problem))))
        else
          let ty := ProofTree.provesE C (mkConst (f ++ `problem))
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
      unless goals.isEmpty do return ("pending", "open proof goals")
      let proof ← instantiateMVars g
      if proof.hasMVar || proof.hasFVar then return ("error", "incomplete proof term")
      let name := f ++ `tested
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := proof }
      unless (← collectAxioms name).all (standardAxioms.contains ·) do
        return ("unsupported", "proof uses nonstandard axioms")
      return ("proved", ""))
      fun e => return ("error", ← e.toMessageData.toString)

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
    ("elapsedMs", toJson (0 : Nat))]
  IO.FS.writeFile output (Json.arr results).pretty
  for r in rows, i in [:rows.length] do
    let t0 ← IO.monoMsNow
    let (status, reason) ← if r.status != .elaborated then
        pure (r.status.toStr, r.reason)
      else if r.tag == .internal || r.tag == .skip then pure (r.tag.toStr, "")
      else if r.tag != .specified && r.tag.modality?.isNone then
        pure ("unsupported", s!"{r.tag.toStr}: no obligation")
      else if listing then pure ("ready", "")
      else testObligation N r
    let elapsed ← IO.monoMsNow
    results := results.set! i <| Json.mkObj [
      ("function", toJson r.displayName), ("tag", toJson r.tag.toStr),
      ("signature", toJson r.signature),
      ("status", toJson status), ("reason", toJson reason),
      ("elapsedMs", toJson (elapsed - t0))]
    IO.FS.writeFile output (Json.arr results).pretty

end Solidity.Frontend
