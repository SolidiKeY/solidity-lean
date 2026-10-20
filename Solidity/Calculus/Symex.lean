import Solidity.Calculus.Sound
import Solidity.Calculus.Quote
import Solidity.Calculus.TacticSyntax

/-!
# Symbolic execution on scoped formulas

`sol_step` and `sol_symex` (`Calculus/TacticSyntax.lean`) on a goal `Valid φ`: the
strategy (`Fml.step`, `symex`, `Calculus/Step.lean`) fires
the rule of the first statement until no modality is left.  Every step is
sound (`Fml.stepR_sound`), from the soundness of each rule
(`Stmt.sound`), so the result
of `symex n φ` valid makes `φ` valid (`symex_valid`).

The result is computed by the compiled strategy and quoted back
(`Fml.quote`, `normValid`), as today's `normValid` does: the kernel
re-checks it when the proof is.
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract}

section Sound

/-- One modality one step on is sound. -/
theorem Fml.modalStep_sound (k : Nat) (m : Modality) {Γ Γ₁ Γ₀ : Ctx} (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) {ψ : Fml C Γ} (h : Fml.modalStep k m P κ φ = some ψ)
    (σ : State C Γ) (hψ : holds σ ψ) : holds σ (.modal m P κ φ) := by
  cases P with
  | nil =>
    cases h
    exact holds_exit m κ φ σ hψ
  | cons s ω =>
    change some ((s.step k m).fml m ω κ φ) = some ψ at h
    cases h
    exact Stmt.sound k m s _ rfl σ ω κ φ hψ

set_option hygiene false in
/-- A connective over one formula: its step is the step of the formula under
it (`φ'`, `hφ : φ.stepR k = some φ'`), the connective `f` around it. -/
local macro "step_under " f:term:max : tactic => `(tactic| (
  intro χ h σ hχ
  obtain ⟨φ', hφ, rfl⟩ :=
    Option.map_eq_some_iff.1 (show (Fml.stepR k φ).map $f = some χ from h)))

/-- **One step of the strategy is sound**, at any fresh index. -/
theorem Fml.stepR_sound (k : Nat) {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {ψ : Fml C Γ}, φ.stepR k = some ψ → ∀ σ, holds σ ψ → holds σ φ := by
  induction φ with
  | tt | eq | wellFormed | not => intro _ h; cases h
  | and φ ψ ihφ ihψ =>
    intro χ h σ hχ
    change (match Fml.stepR k φ with
      | some φ' => some (Fml.and φ' ψ)
      | none => (Fml.stepR k ψ).map (Fml.and φ)) = some χ at h
    split at h
    · rename_i φ' hφ
      cases h
      exact ⟨ihφ hφ σ hχ.1, hχ.2⟩
    · obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨hχ.1, ihψ hψ σ hχ.2⟩
  | imp a φ _ ih =>
    step_under (Fml.imp a)
    exact fun ha => ih hφ σ (hχ ha)
  | upd m U φ ih =>
    step_under (Fml.upd m U)
    exact Upd.afterT_imp hχ fun σ' h => ih hφ σ' h
  | modal m P κ φ => intro χ h σ hχ; exact Fml.modalStep_sound k m P κ φ h σ hχ
  | havoc φ ih =>
    step_under Fml.havoc
    exact fun st nt => ih hφ _ (hχ st nt)
  | all x p φ ih =>
    step_under (Fml.all x p)
    exact fun v => ih hφ _ (hχ v)
  | bind m x t φ ih =>
    step_under (Fml.bind m x t)
    exact Modality.forallB_imp (fun v => ih hφ _) hχ
  | anon xs φ ih =>
    step_under (Fml.anon xs)
    exact fun b => ih hφ _ (hχ b)

/-- `n` steps are sound. -/
theorem symex_sound {Γ : Ctx} : (n : Nat) → (φ : Fml C Γ) → ∀ σ, holds σ (symex n φ) → holds σ φ
  | 0, _, _, h => h
  | n + 1, φ, σ, h => by
    unfold symex at h
    split at h
    · rename_i ψ hψ
      exact Fml.stepR_sound _ φ hψ σ (symex_sound n ψ σ h)
    · exact h

/-- To prove `φ` valid, prove what `symex n` leaves of it valid. -/
theorem symex_valid (n : Nat) {φ : Fml C []} (h : Valid (symex n φ)) : Valid φ :=
  fun σ => symex_sound n φ σ (h σ)

/-- To prove `φ` valid, prove what one step leaves of it valid. -/
theorem Fml.step_valid {φ : Fml C []} (h : Valid (φ.step.getD φ)) : Valid φ := by
  intro σ
  cases hs : φ.step with
  | none => simpa only [hs, Option.getD_none] using h σ
  | some ψ =>
    exact Fml.stepR_sound _ φ hs σ (by simpa only [hs, Option.getD_some] using h σ)

end Sound

/-! ## The tactics -/

namespace Symex

open Lean Elab Tactic Meta

/-- The goal `Valid φ`, its contract and formula; `none` on any other goal. -/
def validGoal? (g : MVarId) : MetaM (Option (Expr × Expr)) := do
  let ty ← instantiateMVars (← g.getType)
  let_expr Valid C φ := ty | return none
  return some (C, ← instantiateMVars φ)

/-- The element `i` of a list literal. -/
def listLitGet? (l : Expr) : Nat → Option Expr
  | 0 => if l.isAppOfArity ``List.cons 3 then some l.appFn!.appArg! else none
  | i + 1 => if l.isAppOfArity ``List.cons 3 then listLitGet? l.appArg! i else none

/-- The closed formula `φ` of the contract `C`, unfolded to a term the
compiled code can evaluate: a constant with no code (an obligation
`solc_scoped_problems` declared) by its value, and an entry of a table
with no code (`List.getD T i _`, how `solc_scoped_problems` declares an
obligation) by the element of `T`'s list literal. -/
partial def evaluable (φ : Expr) : MetaM Expr := do
  let φ ← instantiateMVars φ
  let codeless (n : Lean.Name) : MetaM (Option Expr) := do
    if (IR.findEnvDecl (← getEnv) n).isSome then return none
    let some (.defnInfo d) := (← getEnv).find? n | return none
    return some d.value
  if let .const n _ := φ then
    if let some v ← codeless n then return ← evaluable v
  if φ.isAppOfArity ``List.getD 4 then
    if let (.const t _, some i) := (φ.getArg! 1, (φ.getArg! 2).rawNatLit?) then
      if let some l ← codeless t then
        if let some x := listLitGet? l i then return ← evaluable x
  return φ

/-- Whether `e` is an application of a constructor of `Fml`. -/
def isFmlCtor (e : Expr) : MetaM Bool := do
  let some n := e.getAppFn.constName? | return false
  let some (.ctorInfo i) := (← getEnv).find? n | return false
  return i.induct == ``Fml

/-- The parameters of a quoted formula (decision 28): its leading `∀`s up to
the first explicit one (`Fml.isExplicitAll`), past hidden binders; `none`
where its leading binders are not all written out (a constant), every
leading `∀` then read as a parameter. -/
partial def paramCount (e : Expr) (acc : Nat := 0) : MetaM (Option Nat) := do
  let e := (← instantiateMVars e).consumeMData
  if Fml.isExplicitAll e then return some acc
  if e.isAppOfArity ``Fml.all 5 then return ← paramCount e.appArg! (acc + 1)
  if e.isAppOfArity ``Fml.bind 6 then return ← paramCount e.appArg! acc
  if ← isFmlCtor e then return some acc
  return none

/-- `out`, a formula the strategy computed from `src`, with `src`'s explicit
`∀`s marked again where the two have the same leading binders. -/
partial def restoreMarks (src out : Expr) : Expr :=
  let src := src.consumeMData
  let isAll := out.isAppOfArity ``Fml.all 5 && src.isAppOfArity ``Fml.all 5
  if isAll || (out.isAppOfArity ``Fml.bind 6 && src.isAppOfArity ``Fml.bind 6) then
    let args := out.getAppArgs
    let k := args.size - 1
    let args := args.set! k (restoreMarks src.appArg! args[k]!)
    let args := if isAll && Fml.isExplicitAll src then args.set! 2 (Fml.markExplicitVar args[2]!)
      else args
    mkAppN out.getAppFn args
  else out

/-- Placeholders for the free variables `xs` of a formula, which the
compiled strategy carries along without reading them: a `Nat` (a recursive
call's frames left) by a literal no program writes, a program thunk (the
frame below of a recursive call, in an induction step,
`Calculus/Recursion.lean`) by `Prog.recSentinel`.  The arguments, and what
each placeholder is quoted as, to be written back; `none` if a variable is
of another type. -/
def placeholders (xs : Array Expr) : MetaM (Option (Array Expr × Array (Expr × Expr))) := do
  let mut args := #[]
  let mut back := #[]
  for x in xs, i in [0:xs.size] do
    let ty ← whnfR (← instantiateMVars (← inferType x))
    if ty.isConstOf ``Nat then
      let l := mkRawNatLit (2 ^ 62 + i)
      args := args.push l
      back := back.push (l, x)
    else if ty.isForall && ty.bindingDomain!.isConstOf ``Unit &&
        ty.bindingBody!.isAppOfArity ``Prog 3 && !ty.bindingBody!.hasLooseBVars then
      let P := ty.bindingBody!
      args := args.push (Lean.mkLambda `u .default (mkConst ``Unit)
        (mkAppN (mkConst ``Prog.recSentinel) #[P.getArg! 0, P.getArg! 1, mkRawNatLit i]))
      back := back.push (mkConst (.num `_recFVar i), x)
    else return none
  -- only where a program thunk is free: a `Nat` alone may be computed with
  unless back.any (·.1.isConst) do return none
  return some (args, back)

/-- Compute the formula of a goal `Valid φ` (`Solidity.normValid` for
scoped formulas): the compiled strategy's result quoted back
(`Fml.quote`); the kernel re-checks it.  A formula with a variable
or of an anonymous contract falls back to `Meta.reduce`.  With `src`, the
formula the step started from, its explicit `∀`s stay marked
(`restoreMarks`). -/
def normValid (g : MVarId) (src : Option Expr := none) : TacticM MVarId := do
  let some (C, φ) ← validGoal? g | throwError "expected a goal `Valid φ`"
  let φ' ← match C.constName?, φ.hasFVar || φ.hasMVar with
    | some n, false =>
      unsafe evalExpr Lean.Expr (mkConst ``Lean.Expr)
        (mkApp4 (mkConst ``Fml.quote) C (quoteConstName n)
          (mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)) (← evaluable φ))
    | some n, true =>
      -- free variables the strategy only carries: evaluated at placeholders
      let xs := (Lean.collectFVars {} φ).fvarIds.map mkFVar
      match ← if φ.hasMVar then pure none else placeholders xs with
      | some (args, back) =>
        let lam ← mkLambdaFVars xs (← evaluable φ)
        let out ← unsafe evalExpr Lean.Expr (mkConst ``Lean.Expr)
          (mkApp4 (mkConst ``Fml.quote) C (quoteConstName n)
            (mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)) (mkAppN lam args))
        pure (out.replace fun e => (back.find? (·.1 == e)).map (·.2))
      | none => withTransparency .all <| Meta.reduce φ (skipTypes := true) (skipProofs := true)
    | _, _ => withTransparency .all <| Meta.reduce φ (skipTypes := true) (skipProofs := true)
  let φ' := match src with
    | some src => restoreMarks src φ'
    | none => φ'
  g.replaceTargetDefEq (mkApp2 (mkConst ``Valid) C φ')

/-- Apply `lem`, a lemma `Valid ψ → Valid φ`, to the goal `g`, and compute
`ψ`; with `unchanged`, a goal left as it was is an error. -/
def applyValid (tac : String) (g : MVarId) (lem : Expr) (unchanged : Option MessageData := none) :
    TacticM MVarId := do
  let before ← instantiateMVars (← g.getType)
  let tag ← g.getTag
  let [g'] ← g.apply lem | throwError "{tac}: unexpected goals"
  let g'' ← normValid g' (before.getAppArgs.back?)
  -- the goal keeps its name, as today's (`apply` names it by the premise)
  g''.setTag tag
  if let some msg := unchanged then
    if (← instantiateMVars (← g''.getType)) == before then throwError "{tac}: {msg}"
  return g''

/-- The fuel `sol_symex` gives the strategy. -/
def fuel : Nat := 5000

/-- Run a scoped tactic `k` on its goal `g`, an error logged where the
tactic is and the goal closed by `sorry`, so that the rest of the proof is
still checked.  Where errors are not
recovered from (`fail_if_success`, `first`'s alternatives), the error is
thrown instead, so that the tactic fails there; an abort keeps the errors
it logged. -/
def reporting (g : MVarId) (k : TacticM Unit) : TacticM Unit := do
  let rest := (← getUnsolvedGoals).erase g
  let s ← saveState
  tryCatchRuntimeEx k fun e => do
    unless (← read).recover do throw e
    -- an abort comes with its errors logged and its goals admitted
    -- (`all_goals` in today's closers): keep them
    if let .internal id _ := e then
      if id == abortTacticExceptionId then setGoals rest; return
    s.restore (restoreInfo := true)
    logException e
    g.admit
    setGoals rest

end Symex

open Lean Elab Tactic Meta in
/-- `sol_step` on a scoped goal `Valid φ`: fire the rule of the first
statement. -/
@[tactic Solidity.tacticSol_step]
def evalSolStepCore : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let some (C, _) ← Symex.validGoal? g
    | throwError m!"sol_step: expected a goal `⊨ φ`{indentExpr (← g.getType)}"
  let lem := mkApp (mkConst ``Fml.step_valid) C
  Symex.reporting g do
    replaceMainGoal [← Symex.applyValid "sol_step" g lem (some m!"no modality left")]

open Lean Elab Tactic Meta in
/-- `sol_symex` on a scoped goal `Valid φ`: run the strategy until no
modality is left. -/
@[tactic Solidity.tacticSol_symex]
def evalSolSymexCore : Tactic := fun _ => withMainContext do
  if (← getUnsolvedGoals).isEmpty then return
  let g ← getMainGoal
  let some (C, _) ← Symex.validGoal? g | throwUnsupportedSyntax
  let lem := mkApp2 (mkConst ``symex_valid) C (mkRawNatLit Symex.fuel)
  Symex.reporting g do replaceMainGoal [← Symex.applyValid "sol_symex" g lem]

end Solidity
