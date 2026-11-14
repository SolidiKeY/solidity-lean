import Solidity.Automation.Certificate
import Solidity.Calculus.Budget

/-! Bounded certificate production. Search selects constructors; the kernel
checks the resulting proof, including every local witness and side condition.
The caller supplies its existing verified fallback. This opt-in tactic does
not change the existing strategy or its proof budgets. -/
namespace Solidity.Automation
open Lean Meta Elab Tactic

/-- Produce only the encoded fragment, without the `verified` escape hatch.
Fuel bounds the certificate depth; the surrounding attempt bounds total work. -/
private def produce : Nat → TacticM Unit
  | 0 => throwError "certificate: depth exhausted"
  | n + 1 => withMainContext do
    let type ← instantiateMVars (← (← getMainGoal).getType)
    let_expr Certificate C R Γ H φ := type
      | throwError "certificate: expected a certificate goal"
    if φ.isAppOf ``Fml.all then
      evalTactic (← `(tactic| apply Certificate.allIntro))
    else if φ.isAppOf ``Fml.imp then
      evalTactic (← `(tactic| apply Certificate.intro))
    else if φ.isAppOf ``Fml.upd then
      evalTactic (← `(tactic| apply Certificate.updIntro))
    else if φ.isAppOf ``Fml.modal then
      let_expr Fml.modal _ _ Γ₁ Γ₂ m program κ body := φ
        | throwError "certificate: expected modality"
      let_expr Prog.cons _ _ Γ' _ statement rest := program
        | throwError "certificate: unsupported program"
      let fresh ← mkAppM ``Hyps.fresh #[H, φ]
      let selected ← whnf (← mkAppM ``Stmt.step #[fresh, m, statement])
      let_expr Premise.update _ _ _ update := selected
        | throwError "certificate: unsupported rule"
      let nextH ← mkAppM ``Hyps.upd #[H, m, update]
      let nextFormula ← mkAppM ``Fml.modalK #[m, rest, κ, body]
      let child ← mkFreshExprSyntheticOpaqueMVar
        (← mkAppM ``Certificate #[C, R, nextH, nextFormula])
      let cert := mkAppN (mkConst ``Certificate.update)
        #[C, R, Γ, Γ', Γ₁, Γ₂, H, m, statement, rest, κ, body, update,
          ← mkEqRefl selected, ← mkEqRefl (mkConst ``Bool.true), child]
      (← getMainGoal).assign cert
      replaceMainGoal [child.mvarId!]
    else
      let wrapped ← mkAppM ``Hyps.wrap #[H, φ]
      let initial ← mkAppOptM ``Decide.SymS.init #[some C]
      let lowered ← mkAppM ``Fml.toLS #[mkConst ``Bool.true, initial, wrapped]
      let someLeaf ← whnf lowered
      let_expr Option.some _ leaf := someLeaf
        | throwError "certificate: unsupported lowering"
      let leaf ← reduce leaf
      let someLeaf := mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Decide.LFml) C) leaf
      let yes ← mkEqRefl (mkConst ``Bool.true)
      let witness := mkAppN (mkConst ``LeafWitness.spine) #[C, leaf, yes]
      let cert := mkAppN (mkConst ``Certificate.leaf)
        #[C, R, Γ, H, φ, leaf, ← mkEqRefl someLeaf, witness, yes]
      -- These reflexivity witnesses are proposals: checkedAttempt checks
      -- their actual expected types in the kernel before assigning the caller.
      (← getMainGoal).assign cert
      replaceMainGoal []
    let children ← getUnsolvedGoals
    for child in children do
      setGoals [child]
      produce n
    setGoals []

/-- Check the actual submitted candidate, even if its type was checked before.
Closure retains local hypotheses; unresolved metavariables are never generalized. -/
private def checkedAttempt (candidate : TacticM Unit) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let siblings := (← getGoals).tail!
  let temporary ← mkFreshExprSyntheticOpaqueMVar (← goal.getType)
  setGoals [temporary.mvarId!]
  candidate
  unless (← getUnsolvedGoals).isEmpty do
    throwError "certificate: incomplete candidate"
  let type ← instantiateMVars (← goal.getType)
  let proof ← instantiateMVars temporary
  if type.hasMVar || proof.hasMVar then
    throwError "certificate: unresolved metavariables"
  let some remaining ← Budget.remaining
    | throwError "certificate: missing local budget"
  let configured := Lean.Core.getMaxHeartbeats (← getOptions)
  let allowance := if configured == 0 then remaining else min remaining configured
  let kernelBudget := allowance / 1000
  if kernelBudget == 0 then throwError "certificate: checking budget exhausted"
  let checked ← withOptions (fun o =>
      ((Elab.async.set o false).setBool `debug.skipKernelTC false).setNat
        `maxHeartbeats kernelBudget) <|
    mkAuxTheorem type proof (zetaDelta := true) (cache := false)
  Lean.Core.checkMaxHeartbeats "certificate"
  goal.assign checked
  setGoals siblings

/-- The attempt includes production and synchronous kernel checking. Refusal
restores the whole tactic state before running the supplied fallback. The
attempt is capped at one quarter of the remaining enclosing heartbeats, and
at 50,000 heartbeats. Consumed heartbeats are not refunded. -/
def certificateOr (candidate fallback : TacticM Unit) : TacticM Unit := do
  let remaining ← Budget.remaining
  let budget := match remaining with
    | none => 50
    | some r => min 50 (r / 4000)
  if budget == 0 then fallback
  else
    let result ← Budget.bounded budget (checkedAttempt candidate)
    if result.isNone then fallback

/-- Generate a small certificate, or run the caller's unchanged verified path. -/
syntax "sol_certificate_or" "(" tacticSeq ")" : tactic
elab_rules : tactic
  | `(tactic| sol_certificate_or ($fallback:tacticSeq)) =>
    certificateOr (do
      evalTactic (← `(tactic| apply Certificate.proves))
      produce 64) (evalTactic fallback)

end Solidity.Automation
