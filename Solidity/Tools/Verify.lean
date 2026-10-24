import Solidity.Tools.CompleteVerification

/-!
# `#verify`: prove a specification, or refute it

`#verify C.f` states the obligation of the function `f` of the contract `C`,
scoped (`cspec[C]{f}`, `Calculus/Spec.lean`: `spec[C]{f}` under `open
scoped Solidity.Scoped`), as `⊨ᶠ` of it (`Fml.Valid`). It first tries exact
declaration/input compilation and complete
arithmetic decision (`CompleteVerification.lean`), with both verdicts checked
against that original obligation. A proof is offered with `sol_exact`.
Unsupported syntax or a resource failure falls back to `sol_spec_try`. With
no goal left the function is proved, and the command offers the theorem
as a suggestion (`Try this:`; a click replaces the `#verify C.f` with it;
`#verify C` prints it as text).  Otherwise it searches for a counterexample (`refuteSpec`,
`Counterexample.lean`): one found refutes the specification, certified if
the kernel checked it; none found leaves the function open (`gaveUp`), with the goals
`sol_spec_try` could not close.  `#verify C` does so for every function of
`C` with an obligation.

Each stage has its own ambient `maxHeartbeats` allowance; a timed-out exact
stage falls back, and a timed-out proof leaves heuristic refutation available.
A verdict is only as strong as its word: `✓` is a proof the kernel checked
(and no `sorry` in it), `✗ (certified)` a kernel-checked `¬ ⊨ᶠ spec[C]{f}` of
the scoped obligation, `✗ (tested)` a state in which the typed run runs the
call and a postcondition evaluates to false, with the premises that `eval3` cannot
decide (a `\forall` over a `uint`) true by the generator's construction.
-/

namespace Solidity.Tools

open Lean Elab Term Meta

/-- What `#verify` concludes about a function. -/
inductive Verdict where
  | proved
  /-- A proof from the exact supported-fragment decision. -/
  | provedExact
  /-- A counterexample, whether the kernel certified it, and the conjuncts
  it fails. -/
  | refuted (r : Refutation)
  /-- The goals `sol_spec_try` left, and why there are none if it gave up. -/
  | gaveUp (goals : List MVarId) (note : String := "")
  | error (msg : String)

/-- An exception's message, its first line. -/
def errText (e : Exception) : MetaM String := do
  let msg ← (← addMessageContext e.toMessageData).toString
  pure ((msg.splitOn "\n").headD msg)

/-- **Verify `f`**: exact supported-fragment decision first, then
`sol_spec_try` and heuristic refutation of the original `cspec[C]{f}`. -/
def verifyFunction (n : Lean.Name) (f : String) : TermElabM Verdict := withCurrHeartbeats do
  let C ← unsafe evalConst Contract n
  let cE := Lean.mkConst n
  let φE? ← try
      let stx ← `(cspec[$(mkCIdent n)]{ $(mkIdent (.mkSimple f)) })
      let e ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      pure (Except.ok (← instantiateMVars e))
    catch e => pure (.error (← errText e))
  let φE ← match φE? with
    | .ok e => pure e
    | .error msg => return .error msg
  let saved ← saveState
  let complete ← tryCatchRuntimeEx (withCurrHeartbeats do
      match ← exactVerify φE with
      | .proved _ => pure (some Verdict.provedExact)
      | .refuted _ r xs => return some (.refuted (← exactRefutation n C f φE r xs))
      | .refutedDependent _ r xs => return some (.refuted (← dependentRefutation n C f φE r xs)))
    (fun _ => pure none)
  saved.restore
  if let some v := complete then return v
  let goal ← mkFreshExprMVar (mkApp2 (Lean.mkConst ``Fml.Valid) cE φE)
  let tac ← `(tactic| sol_spec_try)
  let run : TermElabM (Except String (List MVarId)) := do
    pure (.ok (← Tactic.run goal.mvarId! (Tactic.evalTactic tac)))
  -- each step its own heartbeats: a proof search that times out leaves the
  -- refutation its whole budget
  let res ← tryCatchRuntimeEx (withCurrHeartbeats run) fun e => do pure (.error (← errText e))
  match res with
  | .ok [] =>
    if (← instantiateMVars goal).hasSorry then return .gaveUp [] r"the proof contains `sorry`"
    return .proved
  | _ =>
    let gs := match res with
      | .ok gs => gs
      | .error _ => []
    let note := match res with
      | .ok _ => ""
      | .error msg => msg
    match ← withCurrHeartbeats (refuteSpec n C f) with
    | .error msg => return .error msg
    | .ok (_, some r) => return .refuted r
    | .ok (_, none) => return .gaveUp gs note

/-- The theorem a proved `f` of the contract `c` is: the scoped obligation
`#verify` proved, written `⊨ᶠ spec[C]{f}` where `open scoped
Solidity.Scoped` is in effect (`inScope`; `spec[C]{f}` is then
`cspec[C]{f}`), `valid% cspec[C]{f}` (`Fml.Valid`) elsewhere. -/
def provedTheorem (c : Lean.Name) (f : String) (inScope : Bool) (exactDecision : Bool := false) : String :=
  let tactic := if exactDecision then "sol_exact" else "sol_spec"
  if inScope then s!"theorem {f}_spec : ⊨ᶠ spec[{c}]\{{f}} := by {tactic}"
  else s!"theorem {f}_spec : valid% cspec[{c}]\{{f}} := by {tactic}"

/-- The report of a verdict: one line, then the witness or the first goal
left (`inScope` as in `provedTheorem`). -/
def Verdict.report (C : Contract) (c : Lean.Name) (f : String) (inScope : Bool) :
    Verdict → MetaM MessageData
  | .proved => pure m!"✓ {f}\n{provedTheorem c f inScope}"
  | .provedExact => pure m!"✓ {f}\n{provedTheorem c f inScope true}"
  | .refuted r => pure (reportMsg (r.head f) r.lines)
  | .gaveUp [] note => pure m!"? {f}: gave up: {note}"
  | .gaveUp (g :: gs) _ =>
    pure m!"? {f}: {gs.length + 1} goals left, the first:\n{MessageData.ofGoal g}"
  | .error msg => pure m!"! {f}: {msg}"

/-- `#verify C.f`: prove or refute the specification of `f`; `#verify C`:
of every function of `C` with an obligation. -/
syntax (name := verifyCmd) "#verify " ident : command

open Command in
/-- `#verify`: one message per function. -/
@[command_elab verifyCmd]
def elabVerify : Lean.Elab.Command.CommandElab := fun stx => liftTermElabM do
  let ns ← getCurrNamespace
  let short (c : Lean.Name) : Lean.Name := c.replacePrefix ns .anonymous
  let inScope ← surfaceOn
  let one (c : Lean.Name) (C : Contract) (f : String) (suggest : Bool) : TermElabM Unit := do
    match ← verifyFunction c f with
    | .proved =>
      if suggest then
        logInfo m!"✓ {f}"
        Lean.Meta.Tactic.TryThis.addSuggestion stx
          { suggestion := .string (provedTheorem (short c) f inScope) }
      else logInfo (← Verdict.report C (short c) f inScope .proved)
    | .provedExact =>
      if suggest then
        logInfo m!"✓ {f}"
        Lean.Meta.Tactic.TryThis.addSuggestion stx
          { suggestion := .string (provedTheorem (short c) f inScope true) }
      else logInfo (← Verdict.report C (short c) f inScope .provedExact)
    | v => logInfo (← v.report C (short c) f inScope)
  match ← resolveTarget "#verify" stx[1].getId with
  | .function c C f => one c C f true
  | .contract c C =>
    let fs := C.funs.filter fun (_, d) => hasObligation C d
    if fs.isEmpty then logInfo m!"{c} has no function with a specification"
    for (f, _) in fs do one c C f false

end Solidity.Tools
