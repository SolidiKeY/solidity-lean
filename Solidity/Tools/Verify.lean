import Solidity.Tools.Counterexample

/-!
# `#verify`: prove a specification, or refute it

`#verify C.f` states the obligation of the function `f` of the contract `C`
(`spec[C]{f}`, `Calculus/Spec.lean`) and tries `sol_spec_try` on it.  With
no goal left the function is proved, and the command offers the theorem
as a suggestion (`Try this:`; a click replaces the `#verify C.f` with it;
`#verify C` prints it as text).  Otherwise it searches for a counterexample (`refuteSpec`,
`Counterexample.lean`): one found refutes the specification, certified if
the kernel checked it; none found leaves the function stuck, with the goals
`sol_spec_try` could not close.  `#verify C` does so for every function of
`C` with an obligation.

Each function runs under the ambient `maxHeartbeats`, counted from its own
start; running out is reported as stuck, not as a failure of the command.
A verdict is only as strong as its word: `✓` is a proof the kernel checked
(and no `sorry` in it), `✗ (certified)` a kernel-checked `¬ ⊨ spec[C]{f}`,
`✗ (tested)` a state in which the interpreter runs the call and a
postcondition evaluates to false, with the premises that `eval3` cannot
decide (a `\forall` over a `uint`) true by the generator's construction.
-/

namespace Solidity.Tools

open Lean Elab Term Meta

/-- What `#verify` concludes about a function. -/
inductive Verdict where
  | proved
  /-- A counterexample, whether the kernel certified it, and the conjuncts
  it fails. -/
  | refuted (r : Refutation)
  /-- The goals `sol_spec_try` left, and why there are none if it gave up. -/
  | stuck (goals : List MVarId) (note : String := "")
  | error (msg : String)

/-- An exception's message, its first line. -/
def errText (e : Exception) : MetaM String := do
  let msg ← (← addMessageContext e.toMessageData).toString
  pure ((msg.splitOn "\n").headD msg)

/-- **Verify `f`**: elaborate `spec[C]{f}`, run `sol_spec_try` on
`⊨ spec[C]{f}`, and search for a counterexample where goals are left. -/
def verifyFunction (n : Lean.Name) (f : String) : TermElabM Verdict := withCurrHeartbeats do
  let C ← unsafe evalConst Contract n
  let cE := Lean.mkConst n
  let φE? ← try
      let stx ← `(spec[$(mkCIdent n)]{ $(mkIdent (.mkSimple f)) })
      let e ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      pure (Except.ok (← instantiateMVars e))
    catch e => pure (.error (← errText e))
  let φE ← match φE? with
    | .ok e => pure e
    | .error msg => return .error msg
  let goal ← mkFreshExprMVar (mkApp2 (Lean.mkConst ``Valid) cE φE)
  let tac ← `(tactic| sol_spec_try)
  let run : TermElabM (Except String (List MVarId)) := do
    pure (.ok (← Tactic.run goal.mvarId! (Tactic.evalTactic tac)))
  let res ← tryCatchRuntimeEx run fun e => do pure (.error (← errText e))
  match res with
  | .ok [] =>
    if (← instantiateMVars goal).hasSorry then return .stuck [] "the proof contains `sorry`"
    return .proved
  | _ =>
    let gs := match res with
      | .ok gs => gs
      | .error _ => []
    let note := match res with
      | .ok _ => ""
      | .error msg => msg
    match ← refuteSpec n C f with
    | .error msg => return .error msg
    | .ok (_, some r) => return .refuted r
    | .ok (_, none) => return .stuck gs note

/-- The theorem a proved `f` of the contract `c` is. -/
def provedTheorem (c : Lean.Name) (f : String) : String :=
  s!"theorem {f}_spec : ⊨ spec[{c}]\{{f}} := by sol_spec"

/-- The report of a verdict: one line, then the witness or the first goal
left. -/
def Verdict.report (C : Contract) (c : Lean.Name) (f : String) : Verdict → MetaM MessageData
  | .proved => pure m!"✓ {f}\n{provedTheorem c f}"
  | .refuted r => pure (reportMsg (r.head f) (r.lines C))
  | .stuck [] note => pure m!"? {f}: gave up: {note}"
  | .stuck (g :: gs) _ =>
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
  let one (c : Lean.Name) (C : Contract) (f : String) (suggest : Bool) : TermElabM Unit := do
    match ← verifyFunction c f with
    | .proved =>
      if suggest then
        logInfo m!"✓ {f}"
        Lean.Meta.Tactic.TryThis.addSuggestion stx
          { suggestion := .string (provedTheorem (short c) f) }
      else logInfo (← Verdict.report C (short c) f .proved)
    | v => logInfo (← v.report C (short c) f)
  match ← resolveTarget "#verify" stx[1].getId with
  | .function c C f => one c C f true
  | .contract c C =>
    let fs := C.funs.filter fun (_, d) => hasObligation C d
    if fs.isEmpty then logInfo m!"{c} has no function with a specification"
    for (f, _) in fs do one c C f false

end Solidity.Tools
