import Solidity.Calculus.Close
import Solidity.Calculus.UpdateRules
import Solidity.Calculus.TheoryRewrite

/-!
# The steps after the program, KeY's way

What symbolic execution leaves is closed as KeY closes it: the updates
merged, the terms rewritten inside the sequent, the goal closed.  The
merging, applying and rewriting are rules of the calculus, constructors of
`Proves` (`Calculus/Logic.lean`): `Proves.merge`, `Proves.mergeStorage`,
`Proves.applyOnRigidBox`, `Proves.applyStorageBox`, and the rewrites
`Proves.rewrite` (a term taclet, in every equation of the sequent) and
`Proves.updRw` (the same, in the right-hand sides of the box updates, when
the result cannot halt).  Each is sound once; the term taclets
(`Calculus/TermTaclets.lean`: `findOnSave`, `findOnDelAt`, the frames) are
sound by the Theory's own lemmas (`TermTaclet.sound`).  So a
derivation may merge and rewrite with a modality still in the goal, as in
mini-solkey.  This module adds

* `rw [h]`/`sol_rw [h]` on a sequent, `h` a term taclet or a law of the
  Theory itself: the sequent rewritten by `Proves.rewrite` and
  `Proves.updRw`, and computed;
* `sol_apply_upd`: the last update applied to a first-order goal and dropped;
* `Proves.eqClose`, `v ≐ v` behind a context with no diamond, and
  `Proves.eqDClose`, the same for `v = v` (`Fml.eqD`);
* the closing steps under the box, derived through `close`: `a = b` split
  into `defined(a)`, `defined(b)` and `a ≐ b` (`Proves.eqDSplit`,
  `Proves.andSplit`), `defined(x)` from the update that wrote `x`
  (`Proves.definedWritten`), `t ≐ t` (`Proves.eqRefl`);
* `sol_upd` and `sol_merge`, the update rules on `⊨` goals.

KeY applies the updates to the formula and drops them (`applyOnRigid`).
Here a dropped update that could halt takes with it the fact that it did
not, which is no loss under the box — a halting box update proves what
follows — for the Theory equation, total, whose terms need not return.  What
does need the run, a `defined` conjunct, is proved first, from the update
that wrote the local (`Proves.definedWritten`), or the local's right-hand
side is rewritten to a literal first (`Proves.updRw`), whose `defined` is
free.
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## Closing -/

/-- **`eqClose`**: `v ≐ v`, behind a context with no diamond. -/
theorem Proves.eqClose {R : RuleSet} {Γ : List (Hyp C)} {v : Value}
    (hb : Hyp.boxOnly Γ = true := by rfl)
    (hφ : (Hyp.wrap Γ (.eq (.lit v) (.lit v))).modalFree = true := by first | rfl | decide) :
    Proves R Γ (.eq (.lit v) (.lit v)) :=
  .close (fun σ => Hyp.wrap_of_reaches Γ hb σ (fun _ _ => Theory.StValue.Equiv.refl _)) hφ

/-- **`eqDClose`**: `v = v` as a program comparison writes it (`Fml.eqD`),
behind a context with no diamond: a literal is defined everywhere. -/
theorem Proves.eqDClose {R : RuleSet} {Γ : List (Hyp C)} {v : Value}
    (hb : Hyp.boxOnly Γ = true := by rfl)
    (hφ : (Hyp.wrap Γ (Fml.eqD (.lit v) (.lit v))).modalFree = true := by first | rfl | decide) :
    Proves R Γ (Fml.eqD (.lit v) (.lit v)) :=
  .close (fun σ => Hyp.wrap_of_reaches Γ hb σ (fun _ _ => holds_eqD_iff.2 ⟨v, rfl, rfl⟩)) hφ

/-! ## `rw` on a sequent

`rw [r]`, with `r` a term taclet (`findOnSave`, named bare, is
`TermTaclet.findOnSave`) or `h : Term.Theq t t'` rather than an `=`, is
`Proves.rewrite r`: `t` becomes `t'` in every equation of the sequent at
once, so there is no position to find.  It fails when the sequent does not
change.  `rw [← r]` is `TermTaclet.symm r`, and `rw [h₁, h₂]` is one rewrite after the other.  Scoped
to `Proves`, where the derivations are written; elsewhere, and for an `=`,
`rw` is Lean's.

A rule may also be a law of the Theory itself, an `=` of its values
(`find_copyTo_same`, `delValueDefault`) or a definition to unfold
(`copyVal`): a run of them is one rewrite of every `find` of the sequent they
turn into a term (`theoryRewrite`, `Calculus/TheoryRewrite.lean`), the
sequent computed first (`normProves`).  `sol_rw [h₁, …]` is the same with no
fallback to Lean's `rw`. -/

open Lean Elab Tactic Meta in
/-- The goal with its terms folded back to their constructors' names
(`foldTms`, `Calculus/RuleSyntax.lean`): a `simp` over the generic term
functions leaves `Tm.app2 C Op2.find s p`, which `rw` would not find. -/
elab "sol_fold_terms" : tactic => withMainContext do
  let g ← getMainGoal
  replaceMainGoal [← g.replaceTargetDefEq (← foldTms (← instantiateMVars (← g.getType)))]

open Lean Elab Tactic Meta in
/-- Close a side condition of a law, `h : p.hasSeg = true` and the like, by
`rfl` and then `decide`: once the law's terms are known the condition is a
closed `Bool` computation.  A failure is `sol_rw`'s, naming the condition,
rather than the error of whichever tactic was tried last. -/
def solRwSide (h : Lean.Term) (g : MVarId) : TacticM Unit := do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let g ← g.replaceTargetDefEq ty
  let closed ← try
      let gs ← Term.withoutErrToSorry <|
        Tactic.run g (evalTactic (← `(tactic| first | rfl | decide)))
      pure gs.isEmpty
    catch _ => pure false
  unless closed do
    throwError "sol_rw: the side condition{indentExpr ty}\nof {h} closes by neither \
      `rfl` nor `decide`"

open Lean Elab Tactic Meta in
/-- `pf` as a term taclet: itself, or, for a Theory equation
`Term.Theq t t'`, the rule `TermTaclet.theory` makes of it. -/
def asTaclet (pf : Expr) : MetaM Expr := do
  if (← whnfR (← instantiateMVars (← inferType pf))).isAppOf ``Term.Theq then
    mkAppM ``TermTaclet.theory #[pf]
  else pure pf

open Lean Elab Tactic Meta in
/-- Apply the term taclet `pf : TermTaclet t t'` (or a Theory equation,
`asTaclet`) to the main goal, a sequent, and compute the rewritten sequent;
`h` names it in the error.  With `upd`, the rewrite is the one of the
context's box updates (`Proves.updRw`), which asks `t'` to be a term that
cannot halt. -/
def solRwApply (pf : Expr) (h : MessageData) (upd : Bool := false) : TacticM Unit :=
    withMainContext do
  let before ← instantiateMVars (← getMainTarget)
  let pf ← Term.exprToSyntax (← asTaclet pf)
  -- without recovery, an elaboration error is thrown rather than logged
  withoutRecover <| evalTactic <| ← if upd
    then `(tactic| refine Proves.updRw $pf rfl ?_)
    else `(tactic| refine Proves.rewrite $pf ?_)
  evalTactic (← `(tactic| simp (config := { decide := true }) only
    [Hyp.rwEq, Fml.rwEq, Hyp.rwUpd, Upd.rw, UpdElem.rw, List.map_cons, List.map_nil, Tm.rw,
      Tm.pickAt, Op2.opaque, Term.pick, ↓reduceIte, Bool.false_eq_true, reduceCtorEq, and_true,
      true_and, and_false, false_and, and_self, heq_eq_eq, Tm.pvV.injEq, Tm.pvP.injEq,
      Tm.pvS.injEq, Tm.pvI.injEq, Tm.app0.injEq, Tm.app1.injEq, Tm.app2.injEq, Tm.app3.injEq,
      Op0.lit.injEq, Op0.env.injEq, Op0.root.injEq, Op1.unop.injEq, Op1.netOf.injEq,
      Op1.field.injEq, Op1.select.injEq, Op1.newArr.injEq, Op2.binop.injEq, Op2.pushSlot.injEq,
      Op2.extend.injEq]))
  evalTactic (← `(tactic| sol_fold_terms))
  let after ← instantiateMVars (← getMainTarget)
  if after == before then
    throwError "sol_rw: {h} rewrites nothing in the sequent"
  replaceMainGoal [← snocProves (← getMainGoal)]

open Lean Elab Tactic Meta in
/-- `solRwApply` in the equations of the sequent, then, when `t'` is a
literal, in the right-hand sides of its box updates; fails when neither
changes it. -/
def solRwBoth (pf t' : Expr) (h : MessageData) : TacticM Unit := do
  let mut done := false
  let saved ← saveState
  try
    solRwApply pf h
    done := true
  catch _ => saved.restore
  if (← whnfTm (← instantiateMVars t')).isAppOf ``Term.lit then
    let saved ← saveState
    try
      solRwApply pf h (upd := true)
      done := true
    catch _ => saved.restore
  unless done do throwError "sol_rw: {h} rewrites nothing in the sequent"

open Lean Elab Term Meta in
/-- A term taclet named bare: `findOnSave` is `TermTaclet.findOnSave`, in
`h` or at the head of an application `h a`.  Any other term is left as it
is. -/
def qualifyTaclet (h : Lean.Term) : TermElabM Lean.Term := do
  let qual (id : Syntax) : TermElabM (Option Syntax) := do
    unless id.isIdent do return none
    let n := ``TermTaclet ++ id.getId
    if (← getEnv).contains n then return some (mkCIdentFrom id n) else return none
  if let some q ← qual h.raw then return ⟨q⟩
  if h.raw.isOfKind ``Lean.Parser.Term.app then
    if let some q ← qual h.raw[0] then return ⟨h.raw.setArg 0 q⟩
  return h

open Lean Elab Tactic Meta in
/-- Rewrite the main goal, a sequent, with the term taclet `h` (right to
left if `symm`), or a Theory equation `Term.Theq t t'` (`asTaclet`).  An argument of `h` left open is found as Lean's `rw` finds
it: at the first instance of the left-hand side in the sequent (`kabstract`).
So a bare law's name is elaborated as `@h`, every argument open, and its
side conditions (`hp : p.hasSeg = true`, whose default `by rfl` could not
run before `p` is known) are closed after the match, by `solRwSide`; a
condition left pending by an application `h a` is run then too.
The rewritten sequent is then computed (`Term.rw` unfolded, each `if` decided
where the terms settle it), so the next step sees terms, not a pending
rewrite; an `if` left shows an occurrence that the rewrite could not settle,
such as `find(save(storage, p, w), p)` against `find(save(storage, p, v), p)`
with `w` and `v` unknown. -/
def solRw (h : Lean.Term) (symm : Bool) : TacticM Unit := withMainContext do
  let before ← instantiateMVars (← getMainTarget)
  unless (← whnfR before).isAppOf ``Proves do
    throwError "sol_rw: the goal is not a sequent `Γ ⟹ φ`"
  let h' ← qualifyTaclet h
  let pf ← match h' with
    | `($id:ident) => elabTerm (← `(@$id)) none (mayPostpone := true)
    | _ => elabTerm h' none (mayPostpone := true)
  let (args, _, _) ← forallMetaTelescope (← instantiateMVars (← inferType pf))
  let pf ← asTaclet (mkAppN pf args)
  let pf ← if symm then mkAppM ``TermTaclet.symm #[pf] else pure pf
  let_expr TermTaclet _ lhs rhs ← (← whnfR (← instantiateMVars (← inferType pf)))
    | throwError "sol_rw: {h} is not a term taclet `TermTaclet t t'` or a Theory equation \
        `Term.Theq t t'`"
  let lhs ← instantiateMVars lhs
  if lhs.hasMVar then
    let abst ← kabstract before lhs
    unless abst.hasLooseBVars do
      throwError "sol_rw: {lhs} does not occur in the sequent"
  for a in args do
    let g := a.mvarId!
    if !(← g.isAssigned) && (← isProp (← g.getType)) then solRwSide h g
  try Term.synthesizeSyntheticMVarsNoPostponing
  catch e => throwError "sol_rw: a side condition of {h} failed:{indentD e.toMessageData}"
  let pf ← instantiateMVars pf
  if pf.hasExprMVar then
    throwError "sol_rw: could not instantiate {pf}"
  solRwBoth pf rhs m!"{h}"

open Lean Elab Tactic Meta in
/-- Rewrite the main goal, a sequent, with the Theory lemmas `thms`
(`theoryRewrite`, `Calculus/TheoryRewrite.lean`): every `find` of the sequent
they rewrite to a term, one after the other, until none changes: in the
equations (`Proves.rewrite`), and in the right-hand sides of the box updates
when the result is a literal (`Proves.updRw`).  Fails when nothing is
rewritten. -/
def solRwTheory (thms : SimpTheorems) (names : Array Lean.Term) : TacticM Unit := do
  let mut rounds := 0
  let mut progress := true
  while progress && rounds < 32 do
    progress := false
    replaceMainGoal [← normProves (← getMainGoal)]
    let goal ← instantiateMVars (← getMainTarget)
    unless (← whnfR goal).isAppOf ``Proves do
      throwError "sol_rw: the goal is not a sequent `Γ ⟹ φ`"
    for u in theoryCandidates goal do
      let some C := (← withMainContext (inferType u)).app1? ``Solidity.Term | continue
      let some (u', pf) ← withMainContext (theoryRewrite thms C u) | continue
      let saved ← saveState
      try
        solRwBoth pf u' m!"{names}"
        progress := true
        break
      catch _ => saved.restore
    if progress then rounds := rounds + 1
  if rounds == 0 then
    throwError "sol_rw: no term of the sequent is rewritten to a term by {names}"
  replaceMainGoal [← snocProves (← getMainGoal)]

open Lean Elab Tactic Meta in
/-- `sol_rw`'s and `rw`'s rules, in order: a term taclet `TermTaclet t t'`
or a Theory equation `Term.Theq t t'` is `solRw`; a run of Theory lemmas is one `solRwTheory`, so that a lemma
whose result is not yet a term (`find_delAt_same`) is followed by the one
that makes it one (`delValueDefault`) in the same step.  A definition among
them is unfolded. -/
def solRwRules (rs : Array Syntax) : TacticM Unit := do
  let mut thms : SimpTheorems := {}
  let mut names : Array Lean.Term := #[]
  for r in rs do
    let h : Lean.Term := ⟨r[1]⟩
    let symm := !r[0].isNone
    -- a global constant is a Theory lemma unless it states a `TermTaclet`
    -- or a `Term.Theq`; a term taclet named bare, a local hypothesis or an
    -- application is a rule
    let isTheq ← withMainContext do
      unless h.raw.isIdent do return true
      if (← getEnv).contains (``TermTaclet ++ h.raw.getId) then return true
      let some n ← (try some <$> realizeGlobalConstNoOverloadWithInfo h
          catch _ => pure none) | return true
      forallTelescope (← getConstInfo n).type fun _ ty => do
        let ty ← whnfR ty
        return ty.isAppOf ``Solidity.Term.Theq || ty.isAppOf ``Solidity.TermTaclet
    if isTheq then
      unless names.isEmpty do
        solRwTheory thms names
        thms := {}; names := #[]
      withRef r <| solRw h symm
    else
      let n ← realizeGlobalConstNoOverloadWithInfo h
      thms ← match (← getConstInfo n) with
        | .defnInfo _ => thms.addDeclToUnfold n
        | _ => thms.addConst n (inv := symm)
      names := names.push h
  unless names.isEmpty do solRwTheory thms names

/-- `sol_rw [h₁, ← h₂, …]`: rewrite a sequent with each rule in turn.  A rule
is a term taclet (`findOnSave`, `TermTaclet`) or a Theory equation
`h : Term.Theq t t'`, which rewrites every equation of the sequent
(`Proves.rewrite`), or a law of the Theory itself — an `=` of
its values, `find_copyTo_same` — which rewrites every term it turns into a
term (`Calculus/TheoryRewrite.lean`). -/
syntax "sol_rw " "[" Lean.Parser.Tactic.rwRule,+ "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| sol_rw [$rs,*]) => solRwRules (rs.getElems.map (·.raw))

namespace Proves

open Lean Elab Tactic Meta in
/-- `rw [h₁, …]` on a sequent is `sol_rw h₁; …`.  An elaborator, not a
macro: Lean tries a tactic's macros first and its elaborators after, and
reports the error of the last one tried, so as an elaborator this rule runs
after Lean's `rw` (which keeps an `=` rewrite on a sequent Lean's) and its
error is the one shown.  On a goal that is not a sequent it steps aside
(`throwUnsupportedSyntax`), leaving Lean's error. -/
scoped elab_rules : tactic
  | `(tactic| rw [$rs,*]) => do
    let isSeq ← try
        withMainContext do pure ((← whnfR (← instantiateMVars (← getMainTarget))).isAppOf ``Proves)
      catch _ => pure false
    unless isSeq do throwUnsupportedSyntax
    solRwRules (rs.getElems.map (·.raw))

end Proves

/-! ## Under the box: splitting, closing, applying a storage write

The steps that finish a goal once the program is gone, in KeY's order: a
program comparison `a = b` (`Fml.eqD`) splits into its two `defined`
conjuncts and its Theory equation (`Proves.eqDSplit`, `Proves.andSplit`);
a local's `defined` is proved from the update that wrote it
(`Proves.definedWritten`, `Calculus/UpdateRules.lean`) and a literal's from
nothing (`Proves.definedLit`); the updates are applied to the equation and
dropped (`Proves.applyOnRigidBox` for locals, or locals and a storage write
under a storage-free goal; `Proves.applyStorageBox` for a storage write, both
rules of the calculus), the Theory rewrites it (`rw [h]`), and `t ≐ t` closes
(`Proves.eqRefl`).  The splitting and closing steps are derived through
`close`, so they apply to a sequent with no modality left; each needs only
that the context has no diamond (`Hyp.boxOnly`), since behind a halting box
update everything holds. -/

/-- **`andRight`**: a conjunction from each conjunct, in the same context. -/
theorem Proves.andSplit {R : RuleSet} {Γ : List (Hyp C)} {φ ψ : Fml C}
    (h₁ : Proves R Γ φ) (h₂ : Proves R Γ ψ)
    (hφ : (Hyp.wrap Γ (.and φ ψ)).modalFree = true := by first | rfl | decide) :
    Proves R Γ (.and φ ψ) :=
  .close (fun σ => Hyp.wrap_mono₃ (ψ₁ := φ) (ψ₂ := ψ) (ψ₃ := φ) (φ := .and φ ψ)
    (fun _ a b _ => ⟨a, b⟩) Γ σ (h₁.sound σ) (h₂.sound σ)
    (h₁.sound σ)) hφ

/-- A program comparison `a = b` (`Fml.eqD`) from its three parts: `a` and
`b` return, and they are equal in the Theory.

Example: `x = 42` from `defined(x)`, `defined(42)` and `x ≐ 42`. -/
theorem Proves.eqDSplit {R : RuleSet} {Γ : List (Hyp C)} {a b : Term C}
    (ha : Proves R Γ (.defined a)) (hb : Proves R Γ (.defined b)) (he : Proves R Γ (.eq a b))
    (hφ : (Hyp.wrap Γ (Fml.eqD a b)).modalFree = true := by first | rfl | decide) :
    Proves R Γ (Fml.eqD a b) :=
  .close (fun σ => Hyp.wrap_mono₃ (ψ₁ := .defined a) (ψ₂ := .defined b) (ψ₃ := .eq a b)
    (φ := Fml.eqD a b) (fun _ x y z => ⟨x, y, z⟩) Γ σ (ha.sound σ) (hb.sound σ)
    (he.sound σ)) hφ

/-- **`eqClose`** for any term: `t ≐ t`, behind a context with no diamond.
The Theory equation is total, so a term that halts is equal to itself too
(`StValue.Equiv.refl`). -/
theorem Proves.eqRefl {R : RuleSet} {Γ : List (Hyp C)} {t : Term C}
    (hb : Hyp.boxOnly Γ = true := by first | rfl | decide)
    (hφ : (Hyp.wrap Γ (.eq t t)).modalFree = true := by first | rfl | decide) :
    Proves R Γ (.eq t t) :=
  .close (fun σ => Hyp.wrap_of_reaches Γ hb σ (fun _ _ => Theory.StValue.Equiv.refl _)) hφ

/-- A literal is defined, behind a context with no diamond. -/
theorem Proves.definedLit {R : RuleSet} {Γ : List (Hyp C)} {v : Value}
    (hb : Hyp.boxOnly Γ = true := by first | rfl | decide)
    (hφ : (Hyp.wrap Γ (.defined (.lit v))).modalFree = true := by first | rfl | decide) :
    Proves R Γ (.defined (.lit v)) :=
  .close (fun σ => Hyp.wrap_of_reaches Γ hb σ (fun _ _ => ⟨v, rfl⟩)) hφ

/-- `sol_apply_upd`: apply the last update of the context to the first-order
goal and drop it — `Proves.applyStorageBox` for `{storage := s}`,
`Proves.applyOnRigidBox` for an update of locals, or the merged update of
`mergeStorage` under a goal that reads no storage — then compute the
substituted goal, so that the next `rw [h]` finds its terms (it matches
syntactically, and `Fml.subst`/`Fml.withSt` left folded hide them). -/
macro "sol_apply_upd" : tactic => `(tactic| (
  first
    | refine Proves.applyStorageBox ?_
    | refine Proves.applyOnRigidBox ?_
  simp (config := { decide := true }) only [Fml.withSt, Tm.withSt, Op2.opaque, Fml.subst,
    Tm.subst, Upd.valOf, Upd.pathOf, Upd.refOf, Upd.storOf, Upd.lastWrite, UpdElem.var?,
    Upd.withSt, UpdElem.withSt, List.map_cons, List.map_nil, ↓reduceIte, Bool.false_eq_true]
  sol_fold_terms))

/-- **`defined(x)` after `x := t`**: behind a box update whose last binder of
`x` is `x := t`, in a context with no diamond, `x` is defined.  This keeps
what `Proves.applyOnRigidBox` forgets, that the update ran.

Example: `{ storage := S }, { x := find(storage, alice.age) } ⟹ defined(x)`. -/
theorem Proves.definedWritten {R : RuleSet} {Γ : List (Hyp C)} {U : Upd C} {x : Var}
    (hw : U.bindsVal x = true := by first | rfl | decide)
    (hb : Hyp.boxOnly Γ = true := by first | rfl | decide)
    (hφ : (Hyp.wrap (Γ ++ [.upd .box U]) (.defined (.pv x))).modalFree = true := by
      first | rfl | decide) :
    Proves R (Γ ++ [.upd .box U]) (.defined (.pv x)) :=
  .close (fun σ => by
    rw [Hyp.wrap_append]
    exact Hyp.wrap_of_reaches Γ hb σ (fun τ _ => Upd.defined_box hw τ)) hφ

/-- **`{U}(φ ∧ ψ)` from `{U}φ` and `{U}ψ`**, under either modality: where
`U` runs both hold after it, where it halts both judge the halt alike.

Example: `⟹ [{ x := t }](defined(x) ∧ x ≐ 42)` from
`⟹ [{ x := t }] defined(x)` and `⟹ [{ x := t }] x ≐ 42`. -/
theorem Proves.andSplitUpd {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U : Upd C}
    {φ ψ : Fml C} (h₁ : Proves R Γ (.upd m U φ)) (h₂ : Proves R Γ (.upd m U ψ))
    (hφ : (Hyp.wrap Γ (.upd m U (.and φ ψ))).modalFree = true := by first | rfl | decide) :
    Proves R Γ (.upd m U (.and φ ψ)) :=
  .close (fun σ => Hyp.wrap_mono₃ (fun τ a b _ => by
      simp only [holds] at a b ⊢
      cases hU : U.apply τ with
      | error _ => rw [hU] at a; exact a
      | ok ρ => rw [hU] at a b; exact ⟨a, b⟩) Γ σ (h₁.sound σ) (h₂.sound σ) (h₁.sound σ)) hφ

open Lean Elab Tactic Meta in
/-- `sol_upd r`: apply the update rule `r` at the first update where it fits. -/
elab "sol_upd " r:term : tactic => do
  applyValid "sol_upd" (← `(Fml.updAt_valid $r)) (some m!"rule {r} does not apply here")

open Lean Elab Tactic Meta in
/-- `sol_merge`: merge every stack of updates into one and drop what is dead
(`Fml.simpUpds`). -/
elab "sol_merge" : tactic => do
  applyValid "sol_merge" (← `(Fml.simpUpds_valid))

end Solidity
