import Solidity.Calculus.Logic
import Solidity.Calculus.Completeness
import Solidity.Calculus.Quote

/-!
# Symbolic execution

Every statement has exactly one rule (`Stmt.step`, `Completeness.lean`), so
the strategy has nothing to choose: take the first active statement of the
formula and fire its rule, numbering the fresh names above every index in
sight.  Repeating that until no modality is left is symbolic execution; what
remains is a first-order formula under a stack of updates (mini-solkey's
`Ch07_Symex`).

* `sol_step` fires one rule on a `⊨ φ` goal and shows the new goal;
  `sol_symex` runs the strategy to the end.  Both are sound by
  `Fml.stepAt_sound`: nothing the tactic computes is trusted, the kernel
  re-checks the result.
* `sol_close` (`Close.lean`) finishes a goal whose modalities are gone:
  it applies the updates in an arbitrary state and reads back the writes.

After a branch the formula is `(c → ⟨…⟩ φ) ∧ ((c' → ⟨…⟩ φ) ∧ cover)`; the
strategy runs the `then` goal to its end, then the `else` goal.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-- A modality is left: a statement to run, or a `⟨⟩` (or `[]`) to drop. -/
def Fml.active : Fml C → Bool
  | .upd _ _ φ | .imp _ φ | .havoc φ | .all _ _ φ => φ.active
  | .and φ ψ => φ.active || ψ.active
  | .modal .. => true
  | _ => false

/-- Fire the rule of the first active statement, looking through updates, a
precondition and the goals of a branch; fresh names get index `k`. -/
def Fml.stepAt (k : Nat) : Fml C → Option (Fml C)
  | .upd m U φ => (φ.stepAt k).map (.upd m U)
  | .imp a φ => (φ.stepAt k).map (.imp a)
  | .havoc φ => (φ.stepAt k).map .havoc
  | .all x p φ => (φ.stepAt k).map (.all x p)
  | .and φ ψ =>
    if φ.active then (φ.stepAt k).map (.and · ψ) else (ψ.stepAt k).map (.and φ)
  | .modal _ [] φ => some φ
  | .modal m (s :: ω) φ => some ((s.step k m).premise.fml m ω φ)
  | _ => none

/-- Fresh names are numbered one above every index in the whole formula. -/
def Fml.step (φ : Fml C) : Option (Fml C) := φ.stepAt φ.fresh

theorem maxIdx_lt_of_sub {φ ψ : Fml C} {k : Nat} (h : ∀ x ∈ φ.vars, x ∈ ψ.vars)
    (hk : maxIdx ψ.vars < k) : maxIdx φ.vars < k :=
  Nat.lt_of_le_of_lt (maxIdx_le h) hk

/-- One step with index `k` is sound when `k` is above every index in the
formula: what it leaves implies what it started from.

Example: `⟨ uint x = 10; ⟩ x == 10` steps to `⟨ x = 10; ⟩ x == 10`
(`localValueDeclInitDrop`), and wherever the second holds, so does the first. -/
theorem Fml.stepAt_sound {k : Nat} :
    ∀ {φ ψ : Fml C}, maxIdx φ.vars < k → φ.stepAt k = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | .upd m U φ, ψ, hk, h, σ => by
    simp only [Fml.stepAt, Option.map_eq_some_iff] at h
    obtain ⟨ψ', h', rfl⟩ := h
    have := maxIdx_lt_of_sub (φ := φ) (fun x hx => by simp [Fml.vars, hx]) hk
    simp only [holds]
    cases U.apply σ with
    | error _ => exact id
    | ok τ => exact Fml.stepAt_sound this h' τ
  | .imp a φ, ψ, hk, h, σ => by
    simp only [Fml.stepAt, Option.map_eq_some_iff] at h
    obtain ⟨ψ', h', rfl⟩ := h
    have := maxIdx_lt_of_sub (φ := φ) (fun x hx => by simp [Fml.vars, hx]) hk
    exact fun hψ ha => Fml.stepAt_sound this h' σ (hψ ha)
  | .havoc φ, ψ, hk, h, σ => by
    simp only [Fml.stepAt, Option.map_eq_some_iff] at h
    obtain ⟨ψ', h', rfl⟩ := h
    have := maxIdx_lt_of_sub (φ := φ) (fun x hx => by simp [Fml.vars, hx]) hk
    exact fun hψ st nt => Fml.stepAt_sound this h' _ (hψ st nt)
  | .all x p φ, ψ, hk, h, σ => by
    simp only [Fml.stepAt, Option.map_eq_some_iff] at h
    obtain ⟨ψ', h', rfl⟩ := h
    have := maxIdx_lt_of_sub (φ := φ) (fun x hx => by simp [Fml.vars, hx]) hk
    exact fun hψ v hv => Fml.stepAt_sound this h' _ (hψ v hv)
  | .and φ₁ φ₂, ψ, hk, h, σ => by
    have h₁ := maxIdx_lt_of_sub (φ := φ₁) (fun x hx => by simp [Fml.vars, hx]) hk
    have h₂ := maxIdx_lt_of_sub (φ := φ₂) (fun x hx => by simp [Fml.vars, hx]) hk
    simp only [Fml.stepAt] at h
    split at h <;> simp only [Option.map_eq_some_iff] at h <;> obtain ⟨ψ', h', rfl⟩ := h
    · exact fun ⟨hl, hr⟩ => ⟨Fml.stepAt_sound h₁ h' σ hl, hr⟩
    · exact fun ⟨hl, hr⟩ => ⟨hl, Fml.stepAt_sound h₂ h' σ hr⟩
  | .modal m [] φ, ψ, _, h, σ => by
    simp only [Fml.stepAt, Option.some.injEq] at h
    subst h
    cases m <;> exact fun h => ⟨h, nofun⟩
  | .modal m (s :: ω) φ, ψ, hk, h, σ => by
    simp only [Fml.stepAt, Option.some.injEq] at h
    subst h
    exact Premise.sound_above (s.step k m).rule.sound hk (fun _ h => h) σ
  | .tt, _, _, h, _ | .eq _ _, _, _, h, _ | .not _, _, _, h, _ => by
    simp [Fml.stepAt] at h

/-- A step is sound, with no side condition: `Fml.step` numbers the fresh
names above every index in `φ`. -/
theorem Fml.step_sound {φ ψ : Fml C} (h : φ.step = some ψ) (σ : State) :
    holds σ ψ → holds σ φ :=
  Fml.stepAt_sound (Nat.lt_succ_self _) h σ

/-- Run the strategy for at most `n` steps. -/
def symex : Nat → Fml C → Fml C
  | 0, φ => φ
  | n + 1, φ => match φ.step with
    | some ψ => symex n ψ
    | none => φ

/-- Symbolic execution is sound: where what `symex` leaves holds, the original
formula holds. -/
theorem symex_sound : ∀ (n : Nat) (φ : Fml C) (σ : State), holds σ (symex n φ) → holds σ φ
  | 0, _, _, h => h
  | n + 1, φ, σ, h => by
    simp only [symex] at h
    split at h
    · exact Fml.step_sound (by assumption) σ (symex_sound n _ σ h)
    · exact h

/-! ## Tactics -/

/-- One step backwards: proving what `φ` steps to proves `φ`. -/
theorem Fml.step_valid {φ : Fml C} (h : Valid ((φ.step).getD φ)) : Valid φ := by
  intro σ
  cases hs : φ.step with
  | none => simpa [hs] using h σ
  | some ψ => exact Fml.step_sound hs σ (by simpa [hs] using h σ)

/-- To prove `φ` valid, prove what `symex n` leaves of it valid. -/
theorem symex_valid (n : Nat) {φ : Fml C} (h : Valid (symex n φ)) : Valid φ :=
  fun σ => symex_sound n φ σ (h σ)

open Lean Elab Tactic Meta in
/-- Compute the formula inside a `⊨ _` goal, so the goal shows the result of
the rule rather than the call; the kernel re-checks it (`replaceTargetDefEq`).

A closed formula of a named contract — what `dl[C]{ … }` gives — is run by
the compiled code and quoted back (`Fml.quote`), as mini-solkey's
`normValid` does: `Meta.reduce` would unfold `symex 200 φ` by the
interpreter of `whnf`, which takes a minute on three storage writes.  Any
other formula (a variable in it, or an anonymous contract) falls back to
`Meta.reduce`. -/
def normValid (g : MVarId) : TacticM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let_expr Valid C φ := ty | throwError "expected a goal `Valid φ`"
  let φ ← instantiateMVars φ
  let φ' ← match C.constName?, φ.hasFVar || φ.hasMVar with
    | some n, false =>
      unsafe evalExpr Lean.Expr (mkConst ``Lean.Expr)
        (mkApp3 (mkConst ``Fml.quote) C (quoteConstName n) φ)
    | _, _ => withTransparency .all <| Meta.reduce φ (skipTypes := true) (skipProofs := true)
  g.replaceTargetDefEq (mkApp2 (mkConst ``Valid) C φ')

open Lean Elab Tactic Meta in
/-- The shape of the formula tactics: apply `lem`, a lemma `Valid ψ → Valid φ`
with `ψ` computed from `φ`, to the main goal, and compute `ψ` (`normValid`).
With `unchanged` given, a goal left as it was is an error, `tac: unchanged`. -/
def applyValid (tac : String) (lem : Lean.Term) (unchanged : Option MessageData := none) :
    TacticM Unit := do
  let g ← getMainGoal
  let before ← instantiateMVars (← g.getType)
  let [g'] ← g.apply (← elabTerm lem none) | throwError "{tac}: unexpected goals"
  let g'' ← normValid g'
  if let some msg := unchanged then
    if (← instantiateMVars (← g''.getType)) == before then throwError "{tac}: {msg}"
  replaceMainGoal [g'']

open Lean Elab Tactic Meta in
/-- `sol_step`: fire the rule of the first active statement. -/
elab "sol_step" : tactic => do
  applyValid "sol_step" (← `(Fml.step_valid)) (some m!"no modality left")

open Lean Elab Tactic Meta in
/-- `sol_symex`: run the strategy until no modality is left.  With no goal
left it does nothing, as `sol_close` does. -/
elab "sol_symex" : tactic => do
  if (← getUnsolvedGoals).isEmpty then return
  applyValid "sol_symex" (← `(symex_valid 200))


/-! ## The strategy as a derivation

`sol_symex` runs the strategy on a formula, and its soundness is
`symex_sound`.  `sol_derive` runs it on a sequent instead: each step is a
constructor of `Proves`, with the rule `Stmt.step` picks, so what it builds
is a derivation, and `close` takes over only once no modality is left.  The
five lemmas below are `Proves.unfoldRule` for the other premises; a rule
solkey lacks only ever unfolds. -/

namespace Proves

variable {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}

/-- `update` by whichever rule `Rule` names. -/
theorem updateRule {U : Upd C} (d : Rule C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s (.update U))
    (h : Proves .all (Γ ++ [.upd m U]) (.modal m ω φ)) : Proves .all Γ (.modal m (s :: ω) φ) := by
  rcases d with d | d
  · exact .update d h
  · cases d

/-- `split` by whichever rule `Rule` names. -/
theorem splitRule {c c' : Fml C} {P Q : Prog C}
    (d : Rule C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s (.split c c' P Q))
    (thn : Proves .all (Γ ++ [.pre c]) (.modal m (P ++ ω) φ))
    (els : Proves .all (Γ ++ [.pre c']) (.modal m (Q ++ ω) φ))
    (cov : Proves .all Γ (Premise.cover m c c')) : Proves .all Γ (.modal m (s :: ω) φ) := by
  rcases d with d | d
  · exact .split d thn els cov
  · cases d

/-! ### A box split in KeY's two branches

Under the box, `Proves.split`'s third goal is `Γ ⟹ true` (`Premise.cover`),
which KeY's `ifElseSplit` and `requireSimple` do not have.  `closeTrue`
proves it behind a context with no diamond update and no modality, so
`splitBox` is the split with KeY's two goals.  The strategy splits so under
the box (`sol_derive`, `Derive.residue`, the proof tree), and falls back to
`split` where `closeTrue` does not apply. -/

/-- `closeTrue`: `true` holds behind a context with no diamond update
(`Hyp.boxOnly`) and no modality. -/
theorem closeTrue {R : RuleSet} {Γ : List (Hyp C)}
    (hb : Hyp.boxOnly Γ = true := by first | rfl | decide)
    (hm : (Hyp.wrap Γ .tt).modalFree = true := by first | rfl | decide) :
    dl{ ..Γ ⟹[R] true } :=
  .close (Hyp.valid_wrap hb fun _ => trivial) hm

/-- `split` under the box, with KeY's two goals: the third is `closeTrue`'s. -/
theorem splitBox {R : RuleSet} {Γ : List (Hyp C)} {s : Stmt C} {ω : Prog C} {φ : Fml C}
    {c c' : Fml C} {P Q : Prog C}
    (d : Taclet C (Hyp.fresh Γ dl_schema{ [ s; ..ω ] φ }) .box s (.split c c' P Q))
    (thn : dl{ ..Γ, c ⟹[R] [ P; ..ω ] φ })
    (els : dl{ ..Γ, c' ⟹[R] [ Q; ..ω ] φ })
    (hb : Hyp.boxOnly Γ = true := by first | rfl | decide)
    (hm : (Hyp.wrap Γ .tt).modalFree = true := by first | rfl | decide) :
    dl{ ..Γ ⟹[R] [ s; ..ω ] φ } :=
  .split d thn els (closeTrue hb hm)

/-- `splitBox` by whichever rule `Rule` names. -/
theorem splitBoxRule {c c' : Fml C} {P Q : Prog C}
    (d : Rule C (Hyp.fresh Γ (.modal .box (s :: ω) φ)) .box s (.split c c' P Q))
    (thn : Proves .all (Γ ++ [.pre c]) (.modal .box (P ++ ω) φ))
    (els : Proves .all (Γ ++ [.pre c']) (.modal .box (Q ++ ω) φ))
    (hb : Hyp.boxOnly Γ = true := by first | rfl | decide)
    (hm : (Hyp.wrap Γ .tt).modalFree = true := by first | rfl | decide) :
    Proves .all Γ (.modal .box (s :: ω) φ) :=
  splitRule d thn els (closeTrue hb hm)

/-- `check` by whichever rule `Rule` names. -/
theorem checkRule {c : Fml C} {P : Prog C}
    (d : Rule C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s (.check c P))
    (thn : Proves .all (Γ ++ [.pre c]) (.modal m (P ++ ω) φ))
    (els : Proves .all Γ c) : Proves .all Γ (.modal m (s :: ω) φ) := by
  rcases d with d | d
  · exact .check d thn els
  · cases d

/-- `done` by whichever rule `Rule` names. -/
theorem doneRule {b : Bool} (d : Rule C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s (.done b))
    (h : Proves .all Γ ((Premise.done b).fml m ω φ)) : Proves .all Γ (.modal m (s :: ω) φ) := by
  rcases d with d | d
  · exact .done d h
  · exact .doneLean d h

/-- `branches` by whichever rule `Rule` names. -/
theorem branchesRule {bs : List (List (PrimTy × Var) × Prog C)}
    (d : Rule C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s (.branches bs))
    (h : ∀ b ∈ bs, Proves .all Γ (.alls b.1 (.modal m (b.2 ++ ω) φ))) :
    Proves .all Γ (.modal m (s :: ω) φ) := by
  rcases d with d | d
  · exact .branches d h
  · cases d

/-- `cases` by whichever rule `Rule` names. -/
theorem casesRule {fs : List (Fml C)} {us : List (Upd C)}
    (d : Rule C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s (.cases fs us))
    (fml : ∀ f ∈ fs, Proves .all Γ f)
    (upd : ∀ U ∈ us, Proves .all (Γ ++ [.upd m U]) (.modal m ω φ)) :
    Proves .all Γ (.modal m (s :: ω) φ) := by
  rcases d with d | d
  · exact .cases d fml upd
  · cases d

end Proves

/-- `sol_derive`: run the strategy as a derivation.  On every goal it drops
an empty modality, fires the rule `Stmt.step` picks (as `update`, `unfold`,
`split`, `check`, `done`, `branches` or `cases`; a split under the box as
`splitBox`, with KeY's two goals, where it applies), or moves a precondition, a quantified local
or an update in front of the formula into the context, until no goal has a modality left; what
is left is for `close`. -/
macro "sol_derive" : tactic => `(tactic| repeat' (first
  | apply Proves.empty
  | apply Proves.updateRule (Stmt.step _ _ _).rule
  | apply Proves.unfoldRule (Stmt.step _ _ _).rule
  | apply Proves.splitBoxRule (Stmt.step _ _ _).rule
  | apply Proves.splitRule (Stmt.step _ _ _).rule
  | apply Proves.checkRule (Stmt.step _ _ _).rule
  | apply Proves.doneRule (Stmt.step _ _ _).rule
  | (apply Proves.branchesRule (Stmt.step _ _ _).rule
     simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
       Fml.alls, codeBinders, Option.toList, List.map]
     refine ⟨?_, ?_, ?_, ?_⟩)
  | (apply Proves.casesRule (Stmt.step _ _ _).rule
     all_goals (try simp only [List.forall_mem_cons, List.not_mem_nil, false_implies,
       implies_true, and_true])
     all_goals (try and_intros))
  | apply Proves.intro
  | apply Proves.allIntro
  | apply Proves.updIntro))

end Solidity
