import Solidity.Automation.SummaryContracts
import Solidity.Automation.SummaryCache
import Solidity.Calculus.Closers

/-! Example-only adapters retain the API's callee, pre/post and frame obligations.
Keys encode fixed source fixtures, not a proved canonical serializer or cross-contract transport.
The frontend requires named contracts; non-leaf fresh-name transport is not supplied here.
The no-argument storage chain demonstrates full intermediate-callee reuse without that issue.
-/
namespace Solidity.Examples.Summaries.Support
open Lean Elab Meta Tactic Term
/-- Extract the actual typed body carried by the first call in a scoped formula. -/
elab "summary_body " φ:term : term => do
  let mut e ← elabTerm φ none
  e ← whnf e
  while e.isAppOf ``Fml.all || e.isAppOf ``Fml.imp do
    e ← whnf e.getAppArgs.back!
  unless e.isAppOf ``Fml.modal do throwError "expected a modality"
  let mut p ← whnf e.getAppArgs[e.getAppArgs.size - 3]!
  while p.isAppOf ``Prog.cons do
    let s ← whnf p.getAppArgs[p.getAppArgs.size - 2]!
    if s.isAppOf ``Stmt.call then return s.getAppArgs.back!
    p ← whnf p.getAppArgs.back!
  throwError "expected a call"
/-- Close a one-argument API obligation without reconstructing its typed snapshots. -/
def closedObligation {C : Contract} {rs Γf : Ctx}
    (spec : Automation.Summary.Specification C [.val .uint] rs Γf)
    (ret : CallRet [] rs []) : Fml C [] :=
  Fml.allArgs (Γ := []) (.snoc .nil .uint (.user "x") (.simple (.lit 0 rfl)))
    (FunContract.obligation ret spec.body spec.requires spec.ensures spec.modality)
/-- A scalar return enters the same callee state at every caller target. -/
theorem certifyScalar {C : Contract} {Γf : Ctx}
    (s : Automation.Summary.Specification C [.val .uint] [.val .uint] Γf)
    (h : Fml.Valid (closedObligation s (.val .uint (.user "r") none)))
    (within : Prog.within s.mutability s.body = true) (writes : writesRets 1 s.body = true) :
    s.Certified := by
  have hc : FunContract (CallRet.val (Γ := []) .uint (.user "r") none)
      s.body s.requires s.ensures s.modality := FunContract.ofValid (holds_allArgs _ h)
  refine ⟨?_, within, ?_⟩
  · intro Γ Γ' ret
    cases ret with
    | val p r res => exact hc
    | rets bs => cases bs with
      | snoc bs p r => cases bs; exact hc
  · intro Γ Γ' ret
    cases ret with
    | val p r res => exact writes
    | rets bs => cases bs with
      | snoc bs p r => cases bs; exact writes
/-- An empty return frame is likewise independent of the caller. -/
theorem certifyVoid {C : Contract} {ps Γf : Ctx}
    (s : Automation.Summary.Specification C ps [] Γf) (args : Args C [] ps)
    (h : Fml.Valid (Fml.allArgs args (FunContract.obligation (CallRet.none (Γ := [])) s.body s.requires s.ensures s.modality)))
    (within : Prog.within s.mutability s.body = true) (writes : writesRets 0 s.body = true) :
    s.Certified := by
  have hc : FunContract (CallRet.none (Γ := [])) s.body s.requires s.ensures s.modality :=
    FunContract.ofValid (holds_allArgs args h)
  refine ⟨?_, within, ?_⟩
  · intro Γ Γ' ret
    cases ret with
    | none => exact hc
    | rets bs => cases bs; exact hc
  · intro Γ Γ' ret
    cases ret with
    | none => exact writes
    | rets bs => cases bs; exact writes
/-- Force one call expansion without changing the semantics or the selected rule. -/
theorem expandRuns {C : Contract} {Γ Γ' Γ₁ Γ₂ : Ctx}
    {H : Hyps C [] Γ} {m : Modality} {s : Stmt C Γ Γ'} {p : Premise C Γ Γ'}
    {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
    (runs : ∀ σ, Premise.Runs m s p σ)
    (h : Fml.Valid (H.wrap (p.fml m ω κ φ))) :
    Fml.Valid (H.wrap (.modal m (.cons s ω) κ φ)) :=
  fun σ => H.wrap_mono (fun τ hτ => (runs τ).sound ω κ φ hτ) σ (h σ)

private def contextSyntax : TacticM (TSyntax `term) := withMainContext do
  let ty ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
  let_expr Fml.Valid C φ := ty | throwError "expected validity"
  let nil := ctxE []
  let (H, _, _) ← Contract.peel C (mkApp2 (mkConst ``Hyps.nil) C nil) nil φ
  Term.exprToSyntax H
/-- Expand only the wrapper; keep an inner helper call available for a certificate. -/
elab "summary_inline" : tactic => do
  let H ← contextSyntax
  evalTactic (← `(tactic| first
    | refine expandRuns (H := $H) (fun σ => Premise.sound_callVal _ _ _ _ _ _ σ) ?_
    | refine expandRuns (H := $H) (fun σ => Premise.sound_callNone _ _ _ σ) ?_))
  replaceMainGoal [← Symex.normValid (← getMainGoal)]
/-- Consume an existing certificate, leaving exactly the pre/post caller obligations. -/
elab "summary_use " spec:term:max ppSpace cert:term:max : tactic => do
  let H ← contextSyntax
  evalTactic (← `(tactic| refine Automation.Summary.Specification.use $spec $cert
    (H := $H) ?_ ?_))

private def certificateUses : Expr → Nat
  | .const n _ => if n == ``Automation.Summary.Specification.use then 1 else 0
  | .app f a => certificateUses f + certificateUses a
  | .lam _ t b _ | .forallE _ t b _ => certificateUses t + certificateUses b
  | .letE _ t v b _ => certificateUses t + certificateUses v + certificateUses b
  | .mdata _ e | .proj _ _ e => certificateUses e
  | _ => 0
/-- Deterministic bounded program steps; pin the actual certificate applications in the proof. -/
elab "summary_calls " n:num ppSpace spec:term:max ppSpace cert:term:max : tactic => do
  let g ← getMainGoal
  let step ← `(tactic| first | summary_use $spec $cert | summary_inline | sol_step)
  let advance := fun goal => do
    let_expr Fml.Valid C φ := ← goal.getType | throwError "expected validity"
    if ← isDefEq (mkApp3 (mkConst ``Fml.modalFree) C (ctxE []) φ) (mkConst ``Bool.true) then
      throwError "program finished"
    evalTacticAtRaw step.raw goal
  withoutRecover (setGoals (← Meta.repeat' advance (← getGoals) 128))
  let count := certificateUses (← instantiateMVars (mkMVar g))
  unless count == n.getNat do throwError "expected {n.getNat} certificate uses, got {count}"
  for leaf in ← getGoals do
    let_expr Fml.Valid C φ := ← leaf.getType | throwError "expected validity"
    unless ← isDefEq (mkApp3 (mkConst ``Fml.modalFree) C (ctxE []) φ) (mkConst ``Bool.true) do
      throwError "summary walk left a modality"
  evalTactic (← `(tactic| all_goals (sol_prove; all_goals (sol_leaf; sol_close))))

open Automation.Summary
/-- The proof is checked once; all consumers retrieve its exact indexed verdict. -/
structure CheckedSummary (key : Key) (P : Prop) where
  proof : P
namespace CheckedSummary
def valid {key : Key} {P : Prop} (_ : CheckedSummary key P) (k : Key) : Prop := k = key ∧ P
def verdict {key : Key} {P : Prop} (c : CheckedSummary key P) : Verdict c.valid key :=
  .proved ⟨rfl, c.proof⟩
def saved {key : Key} {P : Prop} (c : CheckedSummary key P) : Cache c.valid :=
  ({} : Cache c.valid).insert key c.verdict
/-- Recover evidence from the cache lookup, retaining both possible verdict constructors. -/
theorem fromCache {key : Key} {P : Prop} (c : CheckedSummary key P) : P := by
  have hit : c.saved.lookup key = some c.verdict := Cache.lookup_insert _ _ _
  cases e : c.saved.lookup key with
  | none => rw [show c.saved.lookup key = none from e] at hit; contradiction
  | some v => cases v with
    | proved h => exact h.2
    | refuted h => exact False.elim (h ⟨rfl, c.proof⟩)
/-- Hits bypass even a different verifier. -/
theorem hit {key : Key} {P : Prop} (c : CheckedSummary key P)
    (verify : (k : Key) → Option (Verdict c.valid k)) :
    c.saved.check key verify = (some c.verdict, c.saved, false) :=
  Cache.check_hit _ _ _ _ (Cache.lookup_insert _ _ _)
/-- Actual source-edit controls, including the checker's invocation flag. -/
def edits {key : Key} {P : Prop} (c : CheckedSummary key P) (same changed : Key) : Bool :=
  same == key && (c.saved.lookup same).isSome &&
    !(c.saved.check same (fun _ => none)).2.2 && (c.saved.lookup changed).isNone &&
    (c.saved.check changed (fun _ => none)).2.2
end CheckedSummary

/-- Fixture encoding for a leaf declaration; unrelated functions are excluded explicitly. -/
def leafKey (C : Contract) (f spec : String) : Key :=
  ⟨reprStr (Semantics.lookupBy f C.funs), spec, reprStr { C with funs := [] }, []⟩
/-- Replace one actual declaration while retaining every other contract field. -/
def editFunction (C : Contract) (f : String) (replacement : Contract) : Contract :=
  { C with funs := C.funs.map (fun (n, d) =>
      if n == f then (n, replacement.funs.head!.2) else (n, d)) }
def editUnrelated (C : Contract) : Contract :=
  editFunction C "version" (contract!{ function version() pure returns (uint r) { r = 2; } })

end Solidity.Examples.Summaries.Support
