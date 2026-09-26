import Solidity.Calculus.RuleSoundness

/-!
# The calculus as a judgement: `Γ ⊢ φ`

A taclet rewrites one statement (`Rules.lean`); this module puts the taclets
to work on formulas (mini-solkey's `Ch06_Taclets`, its last part).  A rule's
premise is read as a formula in front of the rest of the program
(`Premise.fml`), `Premise.sound` says that formula implies the one the rule
fired on, and `Proves Γ φ` is the calculus as an inductive judgement, in the
style of PLFA's `Γ ⊢ M ⦂ A`: a theorem is stated as `⊢ φ` and proved by a
derivation built with `apply`.

The context `Γ` holds what sits in front of the current formula: the
preconditions and the updates generated so far.  A rule that produces an
update moves it into the context, so the next rule sees the statement at the
front again, with nothing to look through.  `Proves.sound` says once and for
all that a derivation is a proof.

Fresh names are numbered above every index in sight (`Hyp.fresh`), which is
what discharges the freshness hypothesis of `Taclet.sound`: no rule of a
derivation carries a side condition.

A branch (`ifElseSplit`, `requireSimple`, `assertSimple`) has two goals, one
per condition.  A condition can be stuck (a local read before it is bound),
so the two conditions need not cover every state: a box goal is true of a
stuck run anyway, and a diamond goal owes that one of them holds
(`Premise.cover`).
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## A premise as a formula -/

/-- What a diamond branch owes besides its two goals: one of its conditions
holds.  A box branch owes nothing. -/
def Premise.cover (m : Modality) (c c' : Fml C) : Fml C :=
  match m with
  | .diamond => .not (.and (.not c) (.not c'))
  | .box => .tt

/-- The premise as one formula, under the modality `m` the rule found, in
front of the rest `ω` of the program and the postcondition `φ`. -/
def Premise.fml (m : Modality) : Premise C → Prog C → Fml C → Fml C
  | .update U, ω, φ => .upd m U (.modal m ω φ)
  | .unfold P, ω, φ => .modal m (P ++ ω) φ
  | .split c c' P Q, ω, φ =>
    .and (.imp c (.modal m (P ++ ω) φ))
      (.and (.imp c' (.modal m (Q ++ ω) φ)) (Premise.cover m c c'))
  | .done true, _, _ => .tt
  | .done false, _, _ => .ff

theorem Prog.run_append (σ : State) :
    (P Q : Prog C) → Prog.run σ (P ++ Q) = (do Prog.run (← Prog.run σ P) Q)
  | [], Q => by simp [Prog.run]
  | s :: P, Q => by
    simp only [List.cons_append, Prog.run, bind_assoc]
    cases s.run σ with
    | error _ => rfl
    | ok τ => exact Prog.run_append τ P Q

/-- A modality after a run that continues: a halt anywhere is a halt. -/
theorem Modality.after_bind (m : Modality) (p : State → Prop) (r : Res State)
    (f : State → Res State) :
    m.after (fun x => m.after p (f x)) r = m.after p (r >>= f) := by
  cases r <;> rfl

/-- Two runs that end alike off `ns` satisfy the same modal formula, when
neither the rest of the program nor the postcondition mentions `ns`. -/
theorem Modality.after_sameOk (m : Modality) {ns : List Var} {r r' : Res State}
    (hr : SameOk ns r r') {ω : Prog C} {φ : Fml C} (hω : Avoids (Prog.vars ω ++ φ.vars) ns) :
    m.after (holds · φ) (do Prog.run (← r) ω) ↔ m.after (holds · φ) (do Prog.run (← r') ω) := by
  match r, r', hr with
  | .error _, .error _, _ => exact Iff.rfl
  | .ok a, .ok b, h =>
    exact m.after_frame (Prog.run_frame h ω hω.left) fun _ _ h' => holds_frame φ hω.right h'

/-- **A premise implies its rule's conclusion**: in front of any rest `ω` and
postcondition `φ` that do not mention the rule's fresh names.

Example: `storageFieldWrite_unfold_leftFst` turns
`⟨ people[i].age = 10; ⟩ x == 10` into
`⟨ uint se1 = 10; Person storage sp1 = people[i]; sp1.age = se1; ⟩ x == 10`,
whose run differs from the statement's only on `se1` and `sp1`; neither the
rest of the program nor `x == 10` mentions them. -/
theorem Premise.sound {k : Nat} {m : Modality} {s : Stmt C} {pr : Premise C}
    (h : pr.Correct k m s) (ω : Prog C) (φ : Fml C)
    (hω : Avoids (Prog.vars ω ++ φ.vars) (freshVars k)) (σ : State) :
    holds σ (pr.fml m ω φ) → holds σ (.modal m (s :: ω) φ) := by
  have h₀ : Avoids (Prog.vars ω ++ φ.vars) [] := fun _ _ h => by simp at h
  cases pr with
  | update U =>
    simp only [Premise.fml, holds, Prog.run, Modality.after_bind]
    exact (m.after_sameOk (h σ) h₀).1
  | unfold P =>
    simp only [Premise.fml, holds, Prog.run, Prog.run_append]
    exact (m.after_sameOk (h σ) hω).1
  | split c c' P Q =>
    simp only [Premise.fml, holds, Prog.run_append]
    intro ⟨hP, hQ, hcov⟩
    by_cases hc : holds σ c
    · exact (m.after_sameOk ((h σ).1 hc) hω).1 (hP hc)
    by_cases hc' : holds σ c'
    · exact (m.after_sameOk ((h σ).2.1 hc') hω).1 (hQ hc')
    obtain ⟨e, he⟩ := (h σ).2.2 hc hc'
    cases m with
    | box => simp only [Prog.run, he, bind, Except.bind, Modality.after, Modality.onHalt]
    | diamond =>
      simp only [Premise.cover, holds, not_and, Classical.not_not] at hcov
      exact absurd (hcov hc) hc'
  | done b =>
    obtain ⟨⟨e, he⟩, hb⟩ := h σ
    simp only [holds, Prog.run, he, bind, Except.bind]
    cases b with
    | true => exact fun _ => by cases m <;> simp_all [Modality.after, Modality.onHalt]
    | false => exact fun hf => absurd trivial (by simp [Premise.fml, holds] at hf)

/-! ## Fresh names -/

/-- The largest index of a list of variables. -/
def maxIdx : List Var → Nat
  | [] => 0
  | x :: xs => max x.idx (maxIdx xs)

/-- Every variable's index is at most the largest index in the list.

Example: after Step 2 on `alice.account.balance = 10; uint x = alice.account.balance;`
the formula mentions `sp1`, so `maxIdx` is at least `1`, and the read's
receiver is captured as `sp2`, not as `sp1` again. -/
theorem le_maxIdx {x : Var} : ∀ {xs : List Var}, x ∈ xs → x.idx ≤ maxIdx xs
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (le_maxIdx h) (Nat.le_max_right _ _)

/-- A list whose variables all occur in another has no larger `maxIdx`. -/
theorem maxIdx_le {xs ys : List Var} (h : ∀ x ∈ ys, x ∈ xs) : maxIdx ys ≤ maxIdx xs := by
  induction ys with
  | nil => exact Nat.zero_le _
  | cons y ys ih =>
    simp only [maxIdx]
    exact Nat.max_le.2 ⟨le_maxIdx (h y (.head _)), ih (fun x hx => h x (.tail _ hx))⟩

/-- Indices above every index in sight give fresh names.

Example: in `alice.account.balance = x;` every variable has index `0` (`x` is
a user variable), so `k = 1` will do: `se1`, `sp1`, `ie1`, `mv1` cannot clash
with `x`. -/
theorem freshVars_avoid {vs : List Var} {k : Nat} (hk : maxIdx vs < k) :
    Avoids vs (freshVars k) := by
  intro x hx hF
  have := le_maxIdx hx
  simp only [freshVars, List.mem_cons, List.not_mem_nil] at hF
  rcases hF with rfl | rfl | rfl | rfl | hF <;> simp_all [Var.idx] <;> omega

/-! ## The judgement -/

/-- One entry of the context. -/
inductive Hyp (C : Contract) where
  /-- `a → …` -/
  | pre (a : Fml C)
  /-- `{U} …`, produced under the modality `m` -/
  | upd (m : Modality) (U : Upd C)

/-- Put the context back in front of a formula. -/
def Hyp.wrap : List (Hyp C) → Fml C → Fml C
  | [], φ => φ
  | .pre a :: Γ, φ => .imp a (Hyp.wrap Γ φ)
  | .upd m U :: Γ, φ => .upd m U (Hyp.wrap Γ φ)

/-- Fresh names are numbered one above every index in the whole sequent. -/
def Hyp.fresh (Γ : List (Hyp C)) (φ : Fml C) : Nat := maxIdx (Hyp.wrap Γ φ).vars + 1

/-- `Γ ⊢ φ`: the calculus proves `φ` in the context `Γ`. -/
inductive Proves : List (Hyp C) → Fml C → Prop
  /-- `impRight`: the precondition moves into the context. -/
  | intro {Γ : List (Hyp C)} {a φ : Fml C} (h : Proves (Γ ++ [.pre a]) φ) : Proves Γ (.imp a φ)
  /-- A taclet that produces an update: the update joins the context. -/
  | update {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C} {U : Upd C}
      (d : Taclet C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s (.update U))
      (h : Proves (Γ ++ [.upd m U]) (.modal m ω φ)) : Proves Γ (.modal m (s :: ω) φ)
  /-- A taclet that produces statements: they replace the first one. -/
  | unfold {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C} {P : Prog C}
      (d : Taclet C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s (.unfold P))
      (h : Proves Γ (.modal m (P ++ ω) φ)) : Proves Γ (.modal m (s :: ω) φ)
  /-- A taclet that branches: two goals, one per condition, and under the
  diamond the fact that one of the conditions holds. -/
  | split {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}
      {c c' : Fml C} {P Q : Prog C}
      (d : Taclet C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s (.split c c' P Q))
      (thn : Proves (Γ ++ [.pre c]) (.modal m (P ++ ω) φ))
      (els : Proves (Γ ++ [.pre c']) (.modal m (Q ++ ω) φ))
      (cov : Proves Γ (Premise.cover m c c')) : Proves Γ (.modal m (s :: ω) φ)
  /-- A taclet that closes the modality (`revertBox`, `revertDiamond`): what
  is left is `true` or `false`. -/
  | done {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C} {b : Bool}
      (d : Taclet C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s (.done b))
      (h : Proves Γ ((Premise.done b).fml m ω φ)) : Proves Γ (.modal m (s :: ω) φ)
  /-- `emptyModality`: `⟨⟩ φ` and `[] φ` are `φ`. -/
  | empty {Γ : List (Hyp C)} {m : Modality} {φ : Fml C} (h : Proves Γ φ) :
      Proves Γ (.modal m [] φ)
  /-- Leave the calculus: what is left is proved in the logic. -/
  | close {Γ : List (Hyp C)} {φ : Fml C} (h : Valid (Hyp.wrap Γ φ)) : Proves Γ φ

namespace Proves
scoped notation:25 Γ:26 " ⊢ " φ:26 => Proves Γ φ
scoped notation:25 "⊢ " φ:26 => Proves [] φ
end Proves

theorem Hyp.wrap_append (Γ Δ : List (Hyp C)) (φ : Fml C) :
    Hyp.wrap (Γ ++ Δ) φ = Hyp.wrap Γ (Hyp.wrap Δ φ) := by
  induction Γ with
  | nil => rfl
  | cons h Γ ih => cases h <;> simp [Hyp.wrap, ih]

/-- An implication between two formulas survives wrapping both in the same
context. -/
theorem Hyp.wrap_mono {ψ φ : Fml C} (h : ∀ σ, holds σ ψ → holds σ φ) :
    (Γ : List (Hyp C)) → ∀ σ, holds σ (Hyp.wrap Γ ψ) → holds σ (Hyp.wrap Γ φ)
  | [] => h
  | .pre _ :: Γ => fun σ hψ ha => Hyp.wrap_mono h Γ σ (hψ ha)
  | .upd m U :: Γ => fun σ => by
    simp only [Hyp.wrap, holds]
    cases U.apply σ with
    | error _ => exact id
    | ok τ => exact Hyp.wrap_mono h Γ τ

/-- `Hyp.wrap_mono` for three premises, as a branch has. -/
theorem Hyp.wrap_mono₃ {ψ₁ ψ₂ ψ₃ φ : Fml C}
    (h : ∀ σ, holds σ ψ₁ → holds σ ψ₂ → holds σ ψ₃ → holds σ φ) :
    (Γ : List (Hyp C)) → ∀ σ, holds σ (Hyp.wrap Γ ψ₁) → holds σ (Hyp.wrap Γ ψ₂) →
      holds σ (Hyp.wrap Γ ψ₃) → holds σ (Hyp.wrap Γ φ)
  | [] => h
  | .pre _ :: Γ => fun σ h₁ h₂ h₃ ha => Hyp.wrap_mono₃ h Γ σ (h₁ ha) (h₂ ha) (h₃ ha)
  | .upd m U :: Γ => fun σ => by
    simp only [Hyp.wrap, holds]
    cases U.apply σ with
    | error _ => exact fun h _ _ => h
    | ok τ => exact Hyp.wrap_mono₃ h Γ τ

/-- A variable of a formula is a variable of the formula wrapped in a context. -/
theorem Hyp.vars_wrap {x : Var} {φ : Fml C} :
    (Γ : List (Hyp C)) → x ∈ φ.vars → x ∈ (Hyp.wrap Γ φ).vars
  | [], h => h
  | .pre _ :: Γ, h | .upd _ _ :: Γ, h => by simp [Hyp.wrap, Fml.vars, Hyp.vars_wrap Γ h]

/-- A taclet applied in a context is sound: its fresh names are fresh.

Example: `apply Proves.update .storageFieldWriteSave` on
`{ se1 := 10 }, { sp1 := alice.account } ⟹ ⟨ sp1.balance = se1; ⟩ φ` is sound:
the taclet's index is `Hyp.fresh` of the whole sequent, so the names it could
introduce avoid `se1`, `sp1` and every other name in sight. -/
theorem Taclet.sound_in {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}
    {p : Premise C} (d : Taclet C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s p) :
    ∀ σ, holds σ (p.fml m ω φ) → holds σ (.modal m (s :: ω) φ) := by
  have hv := freshVars_avoid (Nat.lt_succ_self (maxIdx (Hyp.wrap Γ (.modal m (s :: ω) φ)).vars))
  intro σ
  refine Premise.sound (d.sound ?_) ω φ ?_ σ <;>
    intro y hy <;> exact hv y (Hyp.vars_wrap Γ (by simp [Fml.vars, Prog.vars, hy]))

open Proves in
/-- **Soundness of the calculus**: a derivation of `Γ ⊢ φ` proves `φ`
wrapped in its context `Γ`.

Example: from the derivation of `a == 1 ⟹ ⟨ x = a; ⟩ x == 1` (one
`localValueAssign`, `empty`, then `close`) follows
`⊨ a == 1 → ⟨ x = a; ⟩ x == 1`. -/
theorem Proves.sound {Γ : List (Hyp C)} {φ : Fml C} (h : Γ ⊢ φ) : Valid (Hyp.wrap Γ φ) := by
  induction h with
  | intro _ ih => simpa [Hyp.wrap_append, Hyp.wrap] using ih
  | update d _ ih =>
    rw [Hyp.wrap_append] at ih
    exact fun σ => Hyp.wrap_mono d.sound_in _ σ (ih σ)
  | unfold d _ ih | done d _ ih => exact fun σ => Hyp.wrap_mono d.sound_in _ σ (ih σ)
  | split d _ _ _ ih₁ ih₂ ih₃ =>
    rw [Hyp.wrap_append] at ih₁ ih₂
    exact fun σ => Hyp.wrap_mono₃ (fun τ h₁ h₂ h₃ => d.sound_in τ ⟨h₁, h₂, h₃⟩) _ σ
      (ih₁ σ) (ih₂ σ) (ih₃ σ)
  | @empty Γ m φ _ ih =>
    exact fun σ => Hyp.wrap_mono (ψ := φ) (φ := .modal m [] φ)
      (fun _ h => by cases m <;> exact h) Γ σ (ih σ)
  | close h => exact h

open Proves in
/-- A derivation from the empty context proves validity: `⊢ φ` gives `⊨ φ`. -/
theorem Proves.valid {φ : Fml C} (h : ⊢ φ) : Valid φ := h.sound

/-! ## Printing sequents

`Proves Γ φ` prints as the sequent `dl{ Γ ⟹ φ }`, so every goal of an
`apply` derivation reads as the line of the derivation it is: the context
left of `⟹`, in order, and the formula still to prove right of it. -/

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr
set_option hygiene false

def ppHyp? (e : Lean.Expr) : MetaM (Option (TSyntax `dl_hyp)) := do
  match_expr (← whnf (← instantiateMVars e)) with
  | Hyp.pre _ a => return some (← `(dl_hyp| $(← ppFml a):dl_fml))
  | Hyp.upd _ _ U => return some (← `(dl_hyp| $(← ppUpd U):dl_upd))
  | _ => return none

/-- `Proves Γ φ`: `dl{ Γ ⟹ φ }`. -/
@[delab app.Solidity.Proves]
def delabProves : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let some hs ← listElems? (e.getArg! 1) | failure
  let mut out := #[]
  for h in hs do
    let some h ← ppHyp? h | failure
    out := out.push h
  let φ ← ppFml (e.getArg! 2)
  guard !(isEscape φ)
  `(dl{ $[$out],* ⟹ $φ:dl_fml })

end Print

end Solidity
