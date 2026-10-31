import Solidity.Calculus.CloseScoped
import Solidity.Calculus.CloseFrame

/-!
# The original payment-last callback leaf

An opt-in proof tactic for the PiggyBank payout invariant. It retains the
existing bounded prefix peeler and uses typed root-frame, ledger-debit and
resumption lemmas where interval reasoning alone is insufficient. The default
closer, its heuristics and budgets are unchanged. This is not a decision procedure.
-/

namespace Solidity.PaymentClose
open Lean Elab Tactic Meta
open CloseJ
open Semantics

private theorem paymentOwnerFrame {C : Contract} {old new : Storage C}
    (frame : ∀ {W : Ty} (q : SRef C W),
      Theory.diverges [Selector.root "state"] q.labels = true → new.find q = old.find q)
    (howner : C.rootType "owner" = some (.prim .uint)) :
    new.find (SRef.ofRoot "owner" howner) = old.find (SRef.ofRoot "owner" howner) :=
  frame _ (by rw [CloseS.labels_ofRoot]; decide +kernel)

private theorem paymentDebitZero (nt : Ledger)
    (owner self amount : PrimTy.uint.Denote)
    (nonself : owner.1 ≠ self.1) (paid : (lookupBy owner nt).getD 0 = amount.1) :
    (if owner.1 = self.1 then (lookupBy owner nt).getD 0
      else (lookupBy owner nt).getD 0 - amount.1) = 0 := by
  rw [if_neg nonself, paid, Int.sub_self]

private theorem paymentStateValue {C : Contract} {st : Storage C}
    {hstate : C.rootType "state" = some (.prim .uint)}
    (read : st.find (SRef.ofRoot "state" hstate) =
      some (SVal.prim (p := .uint) (⟨2, rfl⟩ : PrimTy.uint.Denote))) :
    ((st.find (SRef.ofRoot "state" hstate)).getD (SVal.prim PrimTy.uint.dflt)).view.1 = 2 := by
  rw [read]
  rfl

private theorem paymentResumeNet {P : Prop}
    {state owner balance : PrimTy.uint.Denote} {nt : Ledger}
    (inv : P → ((state.1 ≠ 2 → (lookupBy owner nt).getD 0 = balance.1) ∧
      (state.1 = 2 → (lookupBy owner nt).getD 0 = 0)))
    (present : P) (broken : state.1 = 2) : (lookupBy owner nt).getD 0 = 0 :=
  (inv present).2 broken

private theorem paymentResumeBalance {P : Prop}
    {state owner balance : PrimTy.uint.Denote} {nt : Ledger}
    (inv : P → ((state.1 ≠ 2 → (lookupBy owner nt).getD 0 = balance.1) ∧
      (state.1 = 2 → (lookupBy owner nt).getD 0 = 0)))
    (present : P) (unbroken : state.1 ≠ 2) : (lookupBy owner nt).getD 0 = balance.1 :=
  (inv present).1 unbroken

private def paymentSettle (gs : List MVarId) (hs : List FVarId) (bounds : Bounds) (prems : Array FVarId) :
    TacticM (Option (MVarId × Bounds)) := do
  let some gMain := gs.getLast? | throwError "sol_close_join_steps: no goal"
  for gS in gs.dropLast do
    let before ← saveState
    let interval ← try (closeSide gS bounds prems >>= fun ok =>
      if ok then pure true else closeArith gS bounds prems) catch _ => pure false
    unless interval do
      before.restore
      let remaining ← runOn gS (← `(tactic| first
        | assumption
        | (intros; apply paymentResumeNet (by assumption) (by assumption); assumption)
        | (
          intros
          rw [paymentOwnerFrame (by assumption) rfl]
          apply paymentDebitZero
          · assumption
          · apply_assumption
            omega)))
      unless remaining.isEmpty do
        throwError "payment typed side goal remains open"
  let mut gM := gMain
  let mut bounds := bounds
  for h in hs do
    let some (g', b') ← addInterval gM h bounds | return none
    (gM, bounds) := (g', b')
  return some (gM, bounds)

mutual

/-- The leaf's binders, premises and updates one at a time, the rest of
the formula held opaque (a fresh `ψ` and `rest = ψ`), so that each step
evaluates one update with `close_rw_s` and every value is named once; a
summary's update first split into its call sites (`shareStep`).  Stops at
the first formula that is not a binder, a premise or an update; `none`
where the goal closed on the way. -/
private partial def paymentPeel (g : MVarId) (bounds : Bounds) (prems : Array FVarId) (k : Nat) :
    TacticM (Option (MVarId × Bounds × Array FVarId)) := do
  let mut g := g
  let mut k := k
  repeat
    match ← shareStep g k with
    | some g' => g := g'; k := k + 1
    | none => break
  g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Solidity.holds 4 do return some (g, bounds, prems)
  let φ ← whnfR t.appArg!
  let rest? : Option Expr :=
    if φ.isAppOfArity ``Fml.upd 6 || φ.isAppOfArity ``Fml.bind 6 then some (φ.getArg! 5)
    else if φ.isAppOfArity ``Fml.all 5 then some (φ.getArg! 4)
    else if φ.isAppOfArity ``Fml.imp 4 then some (φ.getArg! 3)
    else none
  let some rest := rest? | return some (g, bounds, prems)
  -- a premise is read as far as it goes: where the steps past it fail, the
  -- leaf is left at it, as before premises were read (`closeSteps` then
  -- evaluates it whole)
  if φ.isAppOfArity ``Fml.imp 4 then
    let saved ← saveState
    try return ← paymentPeelHead g t φ rest bounds prems k
    catch _ => saved.restore; return some (g, bounds, prems)
  paymentPeelHead g t φ rest bounds prems k

/-- `peel`'s step at a head `φ` of rest `rest`, then `peel` on. -/
private partial def paymentPeelHead (g : MVarId) (t φ rest : Expr) (bounds : Bounds) (prems : Array FVarId)
    (k : Nat) : TacticM (Option (MVarId × Bounds × Array FVarId)) := g.withContext do
  -- `∀ ψ, rest = ψ → holds σ (head ψ)`, built in place (no `kabstract`)
  let ty ← withLocalDeclD `ψ (← inferType rest) fun ψ => do
    withLocalDeclD `hψ (← mkEq rest ψ) fun h => do
      mkForallFVars #[ψ, h] (mkApp t.appFn! (mkAppN φ.getAppFn (φ.getAppArgs.pop.push ψ)))
  let g' ← mkFreshExprSyntheticOpaqueMVar ty (← g.getTag)
  g.assign (mkApp2 g' rest (← mkEqRefl rest))
  let (fs, g₁) ← g'.mvarId!.introNP 2
  let (ψ, hψ) := (fs[0]!, fs[1]!)
  let gs ← runOn g₁ (← `(tactic| simp (config := { maxSteps := 400000 }) only [close_rw_s]))
  let [g₂] := gs | if gs.isEmpty then return none else
    throwError "sol_close_join_steps: a step split the goal"
  let (gs, hs, ps) ← introFront g₂
  let prems := prems ++ ps.toArray
  let some (gM, bounds) ← paymentSettle gs hs bounds prems | return none
  -- the rest back, by its equation
  let gM ← gM.withContext do
    let tgt ← whnfR (← instantiateMVars (← gM.getType))
    unless tgt.isAppOfArity ``Solidity.holds 4 && tgt.appArg! == mkFVar ψ do
      throwError "sol_close_join_steps: a step left {tgt}"
    gM.replaceTargetEq (mkApp tgt.appFn! rest)
      (← mkCongrArg tgt.appFn! (← mkEqSymm (mkFVar hψ)))
  paymentPeel gM bounds prems k

end
private def paymentCloseSteps : TacticM Unit := do
  evalTactic (← `(tactic| (sol_close_unwrap; intro σ)))
  let some (g, bounds, prems) ← paymentPeel (← getMainGoal) {} #[] 0 | setGoals []; return
  let gs ← runOn g (← `(tactic| sol_close_eval))
  let mut rest : Array MVarId := #[]
  for g in gs do
    let (gs', hs, ps) ← introFront g
    if let some (g', _) ← paymentSettle gs' hs bounds (prems ++ ps.toArray) then rest := rest.push g'
  setGoals rest.toList
  evalTactic (← `(tactic| all_goals first
    | omega
    | (apply paymentResumeBalance (by assumption) (by assumption); assumption)
    | (have broken : (_ : Int) = 2 := paymentStateValue (by assumption); omega)))
  unless (← getGoals).isEmpty do throwError "sol_close_join_steps: goals left"

/-- Explicit payment-leaf closing, within the existing incremental-closer budget. -/
syntax (name := solPaymentClose) "sol_payment_close" : tactic

@[tactic solPaymentClose]
def elabSolPaymentClose : Tactic := fun _ => withMainContext do
  Budget.within CloseJ.budget paymentCloseSteps

end Solidity.PaymentClose
