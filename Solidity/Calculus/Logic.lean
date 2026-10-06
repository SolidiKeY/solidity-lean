import Solidity.Calculus.RuleSoundness
import Solidity.Calculus.UpdateRules
import Solidity.Calculus.TermTaclets

/-!
# The calculus as a judgement: `Γ ⊢ φ`

A taclet rewrites one statement (`Rules.lean`); this module puts the taclets
to work on formulas (mini-solkey's `Ch06_Taclets`, its last part).  A rule's
premise is read as a formula in front of the rest of the program
(`Premise.fml`), `Premise.sound` says that formula implies the one the rule
fired on, and `Proves Γ φ` is the calculus as an inductive judgement, in the
style of PLFA's `Γ ⊢ M ⦂ A`: a theorem is stated as `⊢ φ` and proved by a
derivation built with `apply`.  Each constructor is written as KeY writes a
sequent rule, its premises above its conclusion:
`dl{ ..Γ, c ⟹[R] ⟨[ P; ..ω ]⟩ φ }` is `Proves R (Γ ++ [.pre c]) (.modal m (P ++ ω) φ)`
(`RuleSyntax.lean`), and the rules KeY names otherwise have its names too
(`Proves.impRight` for `intro`).

The context `Γ` holds what sits in front of the current formula: the
preconditions and the updates generated so far.  A rule that produces an
update moves it into the context, so the next rule sees the statement at the
front again, with nothing to look through.  `Proves.sound` says once and for
all that a derivation is a proof.

The judgement is indexed by the rules it may use (`RuleSet`): every
constructor takes solkey's `Taclet`s, and `unfoldLean` alone the rule solkey
lacks (`LeanTaclet`), at `.all`.  `Γ ⊢ φ` is the whole calculus, `Γ ⊢ₖ φ`
solkey's; `Calculus/SolkeyFragment.lean` says when the two agree.

Fresh names are numbered above every index in sight (`Hyp.fresh`), which is
what discharges the freshness hypothesis of `Taclet.sound`: no rule of a
derivation carries a side condition.

A branch (`ifElseSplit`, `requireSimple`) has two goals, one
per condition.  A condition can be stuck (a local read before it is bound),
so the two conditions need not cover every state: a box goal is true of a
stuck run anyway, and a diamond goal owes that one of them holds
(`Premise.cover`, the third goal of `Proves.split`).  The premise formula
says the same without looking at the modality, `⟨[ revert(); ]⟩ false ∨ c ∨ c'`
(`Premise.coverFml`): so every premise but a revert's is one formula under
either modality, and a line of a derivation at a
modality `m` goes on through a branch.

A check (`assertSimple`) has two goals too, KeY's: the rest with the
condition assumed, and the condition itself.  A failed `assert` panics, and a
panic satisfies neither modality (`Modality.afterRun`), so the condition is
owed under the box as well.  An update never panics (`Upd.apply_ne_panic`),
which is what lets an update rule's premise read a halt as the box reads a
revert.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## A premise as a formula -/

/-- What a diamond branch owes besides its two goals: one of its conditions
holds.  A box branch owes nothing. -/
def Premise.cover (m : Modality) (c c' : Fml C) : Fml C :=
  match m with
  | .diamond => dl_schema{ c ∨ c' }
  | .box => dl_schema{ true }

/-- The cover as a branch's premise formula carries it, one formula under
either modality: `⟨[ revert(); ]⟩ false ∨ c ∨ c'`.  A halted run satisfies
`⟨[ revert(); ]⟩ false` under the box and not under the diamond, so it
holds exactly where `Premise.cover m c c'` does (`Premise.coverFml_holds`).
It is no goal of the strategy: under its negation it is not active. -/
def Premise.coverFml (m : Modality) (c c' : Fml C) : Fml C :=
  dl_schema{ ⟨[ revert(); ]⟩ ‹.ff› ∨ c ∨ c' }

/-- The premise's cover says what the third goal of a branch says. -/
theorem Premise.coverFml_holds (m : Modality) (c c' : Fml C) (σ : State) :
    holds σ (Premise.coverFml m c c') ↔ holds σ (Premise.cover m c c') := by
  cases m <;> simp only [Premise.coverFml, Premise.cover, holds, Prog.run, Stmt.run, bind,
    Except.bind, Modality.afterRun, Modality.after, Modality.onHalt, not_and, ne_eq,
    reduceCtorEq, Except.error.injEq, and_true,
    Classical.not_not, not_true_eq_false, not_false_eq_true, false_implies, true_implies]

/-- The premise as one formula, under the modality `m` the rule found, in
front of the rest `ω` of the program and the postcondition `φ`. -/
def Premise.fml (m : Modality) : Premise C → Prog C → Fml C → Fml C
  | .update U, ω, φ => dl_schema{ {U} ⟨[ ..ω ]⟩ φ }
  | .unfold P, ω, φ => dl_schema{ ⟨[ P; ..ω ]⟩ φ }
  | .split c c' P Q, ω, φ =>
    dl_schema{ (c → ⟨[ P; ..ω ]⟩ φ) ∧ (c' → ⟨[ Q; ..ω ]⟩ φ) ∧ ‹Premise.coverFml m c c'› }
  | .check c P, ω, φ => dl_schema{ (c → ⟨[ P; ..ω ]⟩ φ) ∧ c }
  | .done true, _, _ => dl_schema{ true }
  | .done false, _, _ => .ff
  | .branches bs, ω, φ => .conj (bs.map fun b => .alls b.1 (.modal m (b.2 ++ ω) φ))
  | .cases fs us, ω, φ => .conj (fs ++ us.map fun U => .upd m U (.modal m ω φ))

/-- Two runs that end alike off `ns` satisfy the same modal formula, when
neither the rest of the program nor the postcondition mentions `ns`. -/
theorem Modality.after_sameOk (m : Modality) {ns : List Var} {r r' : Res State}
    (hr : SameOk ns r r') {ω : Prog C} {φ : Fml C} (hω : Avoids (Prog.vars ω ++ φ.vars) ns) :
    m.afterRun (holds · φ) (do Prog.run (← r) ω) ↔ m.afterRun (holds · φ) (do Prog.run (← r') ω) := by
  match r, r', hr with
  | .error a, .error b, h =>
    simp only [bind, Except.bind, Modality.afterRun, Modality.after, ne_eq, Except.error.injEq]
    exact and_congr_right' (not_congr h)
  | .ok a, .ok b, h =>
    exact m.afterRun_frame (Prog.run_frame h ω hω.left) fun _ _ h' => holds_frame φ hω.right h'

/-- A run that halts, not in a panic, satisfies what its modality says of a
revert: every box formula. -/
theorem Modality.afterRun_error {m : Modality} {p : State → Prop} {e : Halt} (he : e ≠ .panic) :
    m.afterRun p (.error e) ↔ m.onHalt := by
  simp only [Modality.afterRun, Modality.after, ne_eq, Except.error.injEq, he, not_false_eq_true,
    and_true]

/-- An update that runs as the statement does, off no name: its goal gives
the statement's. -/
theorem Premise.sound_upd {m : Modality} {s : Stmt C} {U : Upd C} {σ : State}
    (hs : SameOk [] (U.apply σ) (s.run σ)) (ω : Prog C) (φ : Fml C) :
    holds σ (.upd m U (.modal m ω φ)) → holds σ (.modal m (s :: ω) φ) := by
  have h₀ : Avoids (Prog.vars ω ++ φ.vars) [] := fun _ _ h => by simp only [List.not_mem_nil] at h
  simp only [holds]
  intro hU
  cases hu : U.apply σ with
  | error e =>
    have hp : e ≠ .panic := NoPanic.ne_of_eq (Upd.apply_ne_panic U σ) hu
    rw [hu] at hs
    cases hr : s.run σ with
    | ok _ => rw [hr] at hs; exact hs.elim
    | error e' =>
      rw [hr] at hs
      have hp' : e' ≠ .panic := fun hp' => hp (hs.2 hp')
      rw [hu] at hU
      simp only [Prog.run, hr, bind, Except.bind, Modality.afterRun_error hp']
      exact hU
  | ok τ =>
    rw [hu] at hU hs
    have hk := (m.after_sameOk (r := .ok τ) (r' := s.run σ) hs h₀ (ω := ω) (φ := φ)).1 hU
    simpa only [Prog.run, bind, Except.bind] using hk

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
  | update U => exact Premise.sound_upd (h σ) ω φ
  | unfold P =>
    simp only [Premise.fml, holds, Prog.run, SemanticsProperties.Prog.run_append]
    exact (m.after_sameOk (h σ) hω).1
  | split c c' P Q =>
    simp only [Premise.fml, holds, SemanticsProperties.Prog.run_append]
    intro ⟨hP, hQ, hcov⟩
    by_cases hc : holds σ c
    · exact (m.after_sameOk ((h σ).1 hc) hω).1 (hP hc)
    by_cases hc' : holds σ c'
    · exact (m.after_sameOk ((h σ).2.1 hc') hω).1 (hQ hc')
    obtain ⟨e, he, hp⟩ := (h σ).2.2 hc hc'
    cases m with
    | box => simp only [Prog.run, he, bind, Except.bind, Modality.afterRun_error hp, Modality.onHalt]
    | diamond =>
      rw [Premise.coverFml_holds] at hcov
      simp only [Premise.cover, holds, not_and, Classical.not_not] at hcov
      exact absurd (hcov hc) hc'
  | check c P =>
    simp only [Premise.fml, holds, SemanticsProperties.Prog.run_append]
    intro ⟨hP, hc⟩
    exact (m.after_sameOk (h σ hc) hω).1 (hP hc)
  | done b =>
    cases b with
    | true =>
      obtain ⟨rfl, hb⟩ := h rfl
      obtain ⟨e, he, hp⟩ := hb σ
      simp only [holds, Prog.run, he, bind, Except.bind]
      exact fun _ => by simp [Modality.afterRun_error hp, Modality.onHalt]
    | false => exact fun hf => absurd trivial (by simp [Premise.fml, holds] at hf)
  | branches bs =>
    simp only [Premise.fml, holds_conj, List.mem_map]
    intro hb
    rcases h σ with ⟨rfl, e, he, hp⟩ | ⟨b, hmem, σ', hbind, hrun⟩
    · simp only [holds, Prog.run, he, bind, Except.bind, Modality.afterRun_error hp,
        Modality.onHalt]
    · have hφ := holds_alls.1 (hb _ ⟨b, hmem, rfl⟩) σ' hbind
      simp only [holds, SemanticsProperties.Prog.run_append, hrun] at hφ
      simpa only [holds, Prog.run] using hφ
  | cases fs us =>
    simp only [Premise.fml, holds_conj, List.mem_append, List.mem_map]
    intro hall
    obtain ⟨U, hU, hs⟩ := h σ
    exact Premise.sound_upd hs ω φ (hall _ (.inr ⟨U, hU, rfl⟩))

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

/-- The largest index of two lists is the larger of theirs: `[x, se1] ++ [sp2]`
has `2`.  With it the fresh index of a line whose postcondition `φ` names no
fresh variable is computed without knowing `φ` (`Chains.lean`). -/
theorem maxIdx_append (xs ys : List Var) : maxIdx (xs ++ ys) = max (maxIdx xs) (maxIdx ys) := by
  induction xs with
  | nil => exact (Nat.zero_max _).symm
  | cons x xs ih => simp only [List.cons_append, maxIdx, ih, Nat.max_assoc]

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

/-- Fresh names are numbered one above every index in the formula. -/
abbrev Fml.fresh (φ : Fml C) : Nat := maxIdx φ.vars + 1

/-- An index `k` above every variable of `vs`, among them those of
`⟨[ s; ω ]⟩ φ`, gives names that the statement, the rest of the program and
the postcondition all avoid: what `Taclet.sound` and `Premise.sound` ask. -/
theorem freshVars_avoid_modal {k : Nat} {vs : List Var} {m : Modality} {s : Stmt C}
    {ω : Prog C} {φ : Fml C} (hk : maxIdx vs < k)
    (hsub : ∀ y ∈ (Fml.modal m (s :: ω) φ).vars, y ∈ vs) :
    Avoids s.vars (freshVars k) ∧ Avoids (Prog.vars ω ++ φ.vars) (freshVars k) := by
  have hv := freshVars_avoid hk
  constructor <;> intro y hy <;> exact hv y (hsub y (by simp [Fml.vars, Prog.vars, hy]))

/-- A rule fired on `⟨[ s; ω ]⟩ φ` with its fresh names above every index in
sight is sound: its premise, in front of `ω` and `φ`, implies the formula.

Example: `localValueAssign` fired on `⟨ x = a; ⟩ x == 1` at index `1`. -/
theorem Premise.sound_above {k : Nat} {vs : List Var} {m : Modality} {s : Stmt C} {ω : Prog C}
    {φ : Fml C} {p : Premise C} (hc : Avoids s.vars (freshVars k) → p.Correct k m s)
    (hk : maxIdx vs < k) (hsub : ∀ y ∈ (Fml.modal m (s :: ω) φ).vars, y ∈ vs) (σ : State) :
    holds σ (p.fml m ω φ) → holds σ (.modal m (s :: ω) φ) :=
  let h := freshVars_avoid_modal hk hsub
  Premise.sound (hc h.1) ω φ h.2 σ

/-! ## The judgement -/

/-- One entry of the context. -/
inductive Hyp (C : Contract) where
  /-- `a → …` -/
  | pre (a : Fml C)
  /-- `{U} …`, produced under the modality `m` -/
  | upd (m : Modality) (U : Upd C)
  /-- `{havoc} …`: any storage and ledger a callee may leave, as
  KeY's anonymising update with fresh skolem symbols. -/
  | havoc
  /-- `∀ p x. …`: the local `x` holds any value of the type `p`, as KeY's
  skolem constant for a quantified variable (a `try`'s return values). -/
  | all (x : Var) (p : PrimTy)

/-- Put the context back in front of a formula. -/
def Hyp.wrap : List (Hyp C) → Fml C → Fml C
  | [], φ => φ
  | .pre a :: Γ, φ => dl_schema{ a → ‹Hyp.wrap Γ φ› }
  | .upd m U :: Γ, φ => dl_schema{ {U} ‹Hyp.wrap Γ φ› }
  | .havoc :: Γ, φ => dl_schema{ { havoc } ‹Hyp.wrap Γ φ› }
  | .all x p :: Γ, φ => .all x p (Hyp.wrap Γ φ)

/-- A Theory rewrite of the context (`Fml.rwEq`): in every precondition; an
update or a `havoc` stays as it is, since its right-hand sides run in the
interpreter. -/
def Hyp.rwEq (q : Term C × Term C) : List (Hyp C) → List (Hyp C)
  | [] => []
  | .pre a :: Γ => .pre (a.rwEq q) :: Hyp.rwEq q Γ
  | .upd m U :: Γ => .upd m U :: Hyp.rwEq q Γ
  | .havoc :: Γ => .havoc :: Hyp.rwEq q Γ
  | .all x p :: Γ => .all x p :: Hyp.rwEq q Γ

/-- An update rewrite of the context (`Upd.rw`): in the right-hand sides of
every box update.  A precondition, a diamond update or a `havoc` stays as it
is: a rewritten diamond update would also have to return where the old one
does, which `Term.EvalRefines` does not say. -/
def Hyp.rwUpd (q : Term C × Term C) : List (Hyp C) → List (Hyp C)
  | [] => []
  | .pre a :: Γ => .pre a :: Hyp.rwUpd q Γ
  | .upd .box U :: Γ => .upd .box (U.rw q) :: Hyp.rwUpd q Γ
  | .upd .diamond U :: Γ => .upd .diamond U :: Hyp.rwUpd q Γ
  | .havoc :: Γ => .havoc :: Hyp.rwUpd q Γ
  | .all x p :: Γ => .all x p :: Hyp.rwUpd q Γ

/-- Fresh names are numbered one above every index in the whole sequent. -/
def Hyp.fresh (Γ : List (Hyp C)) (φ : Fml C) : Nat := (Hyp.wrap Γ φ).fresh

/-- Which rules a derivation may use: solkey's (`Taclet`), or all of them
(`LeanTaclet` too). -/
inductive RuleSet where
  | solkey
  | all
  deriving DecidableEq, Repr

/-- `Γ ⊢ φ`: the calculus proves `φ` in the context `Γ`; `Γ ⊢ₖ φ`: solkey's
rules alone do. -/
inductive Proves : RuleSet → List (Hyp C) → Fml C → Prop
  /-- `impRight`: the precondition moves into the context. -/
  | intro {R : RuleSet} {Γ : List (Hyp C)} {a φ : Fml C} (h : dl{ ..Γ, a ⟹[R] φ }) :
      dl{ ..Γ ⟹[R] a → φ }
  /-- A taclet that produces an update: the update joins the context. -/
  | update {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}
      {U : Upd C}
      (d : Taclet C (Hyp.fresh Γ dl_schema{ ⟨[ s; ..ω ]⟩ φ }) m s (.update U))
      (h : dl{ ..Γ, {U} ⟹[R] ⟨[ ..ω ]⟩ φ }) : dl{ ..Γ ⟹[R] ⟨[ s; ..ω ]⟩ φ }
  /-- A taclet that produces statements: they replace the first one. -/
  | unfold {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}
      {P : Prog C}
      (d : Taclet C (Hyp.fresh Γ dl_schema{ ⟨[ s; ..ω ]⟩ φ }) m s (.unfold P))
      (h : dl{ ..Γ ⟹[R] ⟨[ P; ..ω ]⟩ φ }) : dl{ ..Γ ⟹[R] ⟨[ s; ..ω ]⟩ φ }
  /-- A taclet that branches: two goals, one per condition, and under the
  diamond the fact that one of the conditions holds. -/
  | split {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}
      {c c' : Fml C} {P Q : Prog C}
      (d : Taclet C (Hyp.fresh Γ dl_schema{ ⟨[ s; ..ω ]⟩ φ }) m s (.split c c' P Q))
      (thn : dl{ ..Γ, c ⟹[R] ⟨[ P; ..ω ]⟩ φ })
      (els : dl{ ..Γ, c' ⟹[R] ⟨[ Q; ..ω ]⟩ φ })
      (cov : dl{ ..Γ ⟹[R] ‹Premise.cover m c c'› }) : dl{ ..Γ ⟹[R] ⟨[ s; ..ω ]⟩ φ }
  /-- A taclet that checks (`assertSimple`): the goal with the condition
  assumed, and the condition — KeY's "Holds" and "Violated". -/
  | check {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}
      {c : Fml C} {P : Prog C}
      (d : Taclet C (Hyp.fresh Γ dl_schema{ ⟨[ s; ..ω ]⟩ φ }) m s (.check c P))
      (thn : dl{ ..Γ, c ⟹[R] ⟨[ P; ..ω ]⟩ φ })
      (els : dl{ ..Γ ⟹[R] c }) : dl{ ..Γ ⟹[R] ⟨[ s; ..ω ]⟩ φ }
  /-- A taclet that closes the modality (`revertBox`, `revertDiamond`): what
  is left is `true` or `false`. -/
  | done {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}
      {b : Bool}
      (d : Taclet C (Hyp.fresh Γ dl_schema{ ⟨[ s; ..ω ]⟩ φ }) m s (.done b))
      (h : dl{ ..Γ ⟹[R] ‹(Premise.done b).fml m ω φ› }) : dl{ ..Γ ⟹[R] ⟨[ s; ..ω ]⟩ φ }
  /-- A taclet with a goal per way an external call may end
  (`tryCallNoCallbackBox`): each clause's block in the statement's place, for
  every value of the locals the outcome binds. -/
  | branches {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C}
      {φ : Fml C} {bs : List (List (PrimTy × Var) × Prog C)}
      (d : Taclet C (Hyp.fresh Γ dl_schema{ ⟨[ s; ..ω ]⟩ φ }) m s (.branches bs))
      (h : ∀ b ∈ bs, dl{ ..Γ ⟹[R] ‹.alls b.1 (.modal m (b.2 ++ ω) φ)› }) :
      dl{ ..Γ ⟹[R] ⟨[ s; ..ω ]⟩ φ }
  /-- A taclet with labelled goals (`sendNoCallbackBox`): each formula, and the
  rest after each update. -/
  | cases {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C}
      {φ : Fml C} {fs : List (Fml C)} {us : List (Upd C)}
      (d : Taclet C (Hyp.fresh Γ dl_schema{ ⟨[ s; ..ω ]⟩ φ }) m s (.cases fs us))
      (fml : ∀ f ∈ fs, dl{ ..Γ ⟹[R] f })
      (upd : ∀ U ∈ us, dl{ ..Γ, {U} ⟹[R] ⟨[ ..ω ]⟩ φ }) :
      dl{ ..Γ ⟹[R] ⟨[ s; ..ω ]⟩ φ }
  /-- `allRight`: a quantified local joins the context, holding any value of
  its type. -/
  | allIntro {R : RuleSet} {Γ : List (Hyp C)} {x : Var} {p : PrimTy} {φ : Fml C}
      (h : dl{ ..Γ, ∀ p x ⟹[R] φ }) : dl{ ..Γ ⟹[R] ‹.all x p φ› }
  /-- An update in front of the formula joins the context: `⟹ {U} φ` is
  `{U} ⟹ φ`, the sequent KeY writes with the update on the formula.  The
  snapshot `{ old := storage }` of a specification (`Calculus/Spec.lean`)
  enters the derivation so. -/
  | updIntro {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U : Upd C} {φ : Fml C}
      (h : dl{ ..Γ, {U} ⟹[R] φ }) : dl{ ..Γ ⟹[R] {U} φ }
  /-- A rule solkey does not have, closing the modality (`tryCallDiamond`). -/
  | doneLean {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C} {b : Bool}
      (d : LeanTaclet C (Hyp.fresh Γ dl_schema{ ⟨[ s; ..ω ]⟩ φ }) m s (.done b))
      (h : dl{ ..Γ ⟹ ‹(Premise.done b).fml m ω φ› }) : dl{ ..Γ ⟹ ⟨[ s; ..ω ]⟩ φ }
  /-- A rule solkey does not have, producing statements. -/
  | unfoldLean {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}
      {P : Prog C} (d : LeanTaclet C (Hyp.fresh Γ dl_schema{ ⟨[ s; ..ω ]⟩ φ }) m s (.unfold P))
      (h : dl{ ..Γ ⟹ ⟨[ P; ..ω ]⟩ φ }) : dl{ ..Γ ⟹ ⟨[ s; ..ω ]⟩ φ }
  /-- `emptyModality`: `⟨⟩ φ` and `[] φ` are `φ`. -/
  | empty {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {φ : Fml C} (h : dl{ ..Γ ⟹[R] φ }) :
      dl{ ..Γ ⟹[R] ⟨[ ]⟩ φ }
  /-- A term taclet as a rewrite rule (`TermTaclet`, `Calculus/TermTaclets.lean`):
  `t` becomes `t'` in every equation of the sequent, at any depth
  (`Hyp.rwEq`, `Fml.rwEq`).  The derivation names the taclet; why it is
  sound is `TermTaclet.sound`, on the `⊨` side. -/
  | rewrite {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} {t t' : Term C}
      (r : TermTaclet t t') (d : dl{ ..(Hyp.rwEq (t, t') Γ) ⟹[R] ‹Fml.rwEq (t, t') φ› }) :
      dl{ ..Γ ⟹[R] φ }
  /-- A term taclet inside the context's updates: `t` becomes `t'` in the
  right-hand sides of every box update (`Hyp.rwUpd`), where `t'` cannot halt
  (`Tm.total`), so returns whatever `t` returns.  With `rewrite` it reaches
  the whole sequent, as mini-solkey's `rewrite` does. -/
  | updRw {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} {t t' : Term C}
      (r : TermTaclet t t') (ht : t'.total = true) (d : dl{ ..(Hyp.rwUpd (t, t') Γ) ⟹[R] φ }) :
      dl{ ..Γ ⟹[R] φ }
  /-- `sequentialToParallel`: the last two updates of the context merge into
  one parallel update, the first substituted into the second, when the first
  writes only locals (`UpdRule.sequentialToParallel`). -/
  | merge {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U V : Upd C} {φ : Fml C}
      (hU : U.envOnly = true) (h : dl{ ..Γ, {U ‖ {U}V} ⟹[R] φ }) :
      dl{ ..Γ, {U}, {V} ⟹[R] φ }
  /-- `sequentialToParallel` over a storage write, `{storage := s ‖ {storage := s}V}`,
  for a `V` whose storage reads are all `storage` terms (`Upd.mergeStorage_holds`). -/
  | mergeStorage {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {s : STerm C} {V : Upd C}
      {φ : Fml C} (h : Proves R (Γ ++ [.upd m (.storage s :: V.withSt s)]) φ)
      (hV : V.all (·.stExplicit) = true := by rfl) :
      dl{ ..Γ, {storage := s}, {V} ⟹[R] φ }
  /-- `simplifyUpdate`: the effectless elements of the last update are
  dropped (`Upd.dropEffectless`). -/
  | simplify {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U : Upd C} {φ : Fml C}
      (h : Proves R (Γ ++ [.upd m (U.dropEffectless φ.vars)]) φ) : dl{ ..Γ, {U} ⟹[R] φ }
  /-- `applyOnRigidFormula` under the box: the last update, of locals (or
  locals and a storage write, under a goal that reads no storage), applied to
  a first-order goal and dropped (`Fml.subst_box`, `Fml.subst_box_st`). -/
  | applyOnRigidBox {R : RuleSet} {Γ : List (Hyp C)} {U : Upd C} {φ : Fml C}
      (h : dl{ ..Γ ⟹[R] ‹φ.subst U› })
      (hU : (U.envOnly || U.localsOrStorage && φ.stFree) = true := by first | rfl | decide)
      (hr : φ.rigid = true := by first | rfl | decide)
      (hs : φ.sortedFor U = true := by first | rfl | decide) :
      dl{ ..Γ, {U} [ ] ⟹[R] φ }
  /-- `applyOnRigidFormula` for a storage write under the box: `s` for every
  `storage` of a first-order goal (`Fml.withSt_box`). -/
  | applyStorageBox {R : RuleSet} {Γ : List (Hyp C)} {s : STerm C} {φ : Fml C}
      (h : dl{ ..Γ ⟹[R] ‹φ.withSt s› })
      (hr : φ.rigid = true := by first | rfl | decide)
      (he : φ.stExplicit = true := by first | rfl | decide) :
      dl{ ..Γ, {storage := s} [ ] ⟹[R] φ }
  /-- Leave the calculus: with no modality left anywhere in the sequent, what
  is left is proved in the logic. -/
  | close {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} (h : Valid (Hyp.wrap Γ φ))
      (hφ : (Hyp.wrap Γ φ).modalFree = true := by first | rfl | decide) : dl{ ..Γ ⟹[R] φ }

namespace Proves
scoped notation:25 Γ:26 " ⊢ " φ:26 => Proves RuleSet.all Γ φ
scoped notation:25 "⊢ " φ:26 => Proves RuleSet.all [] φ
scoped notation:25 Γ:26 " ⊢ₖ " φ:26 => Proves RuleSet.solkey Γ φ
scoped notation:25 "⊢ₖ " φ:26 => Proves RuleSet.solkey [] φ
end Proves

/-! ### The rules by solkey's names

The constructors whose rule KeY has under another name, under that name too:
`apply Proves.impRight` is `apply Proves.intro`. -/

/-- `impRight` (`intro`). -/
theorem Proves.impRight {R : RuleSet} {Γ : List (Hyp C)} {a φ : Fml C}
    (h : dl{ ..Γ, a ⟹[R] φ }) : dl{ ..Γ ⟹[R] a → φ } := .intro h

/-- `allRight` (`allIntro`). -/
theorem Proves.allRight {R : RuleSet} {Γ : List (Hyp C)} {x : Var} {p : PrimTy} {φ : Fml C}
    (h : dl{ ..Γ, ∀ p x ⟹[R] φ }) : dl{ ..Γ ⟹[R] ‹.all x p φ› } := .allIntro h

/-- `emptyModality` (`empty`). -/
theorem Proves.emptyModality {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {φ : Fml C}
    (h : dl{ ..Γ ⟹[R] φ }) : dl{ ..Γ ⟹[R] ⟨[ ]⟩ φ } := .empty h

/-- `sequentialToParallel` (`merge`). -/
theorem Proves.sequentialToParallel {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U V : Upd C}
    {φ : Fml C} (hU : U.envOnly = true) (h : dl{ ..Γ, {U ‖ {U}V} ⟹[R] φ }) :
    dl{ ..Γ, {U}, {V} ⟹[R] φ } := .merge hU h

/-- `sequentialToParallel` over a storage write (`mergeStorage`). -/
theorem Proves.sequentialToParallelStorage {R : RuleSet} {Γ : List (Hyp C)} {m : Modality}
    {s : STerm C} {V : Upd C} {φ : Fml C}
    (h : Proves R (Γ ++ [.upd m (.storage s :: V.withSt s)]) φ)
    (hV : V.all (·.stExplicit) = true := by rfl) :
    dl{ ..Γ, {storage := s}, {V} ⟹[R] φ } := .mergeStorage h hV

/-- `simplifyUpdate` (`simplify`). -/
theorem Proves.simplifyUpdate {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U : Upd C}
    {φ : Fml C} (h : Proves R (Γ ++ [.upd m (U.dropEffectless φ.vars)]) φ) :
    dl{ ..Γ, {U} ⟹[R] φ } := .simplify h

/-- `applyOnRigidFormula` under the box (`applyOnRigidBox`). -/
theorem Proves.applyOnRigidFormula {R : RuleSet} {Γ : List (Hyp C)} {U : Upd C} {φ : Fml C}
    (h : dl{ ..Γ ⟹[R] ‹φ.subst U› })
    (hU : (U.envOnly || U.localsOrStorage && φ.stFree) = true := by first | rfl | decide)
    (hr : φ.rigid = true := by first | rfl | decide)
    (hs : φ.sortedFor U = true := by first | rfl | decide) :
    dl{ ..Γ, {U} [ ] ⟹[R] φ } := .applyOnRigidBox h hU hr hs

theorem Hyp.wrap_append (Γ Δ : List (Hyp C)) (φ : Fml C) :
    Hyp.wrap (Γ ++ Δ) φ = Hyp.wrap Γ (Hyp.wrap Δ φ) := by
  induction Γ with
  | nil => rfl
  | cons h Γ ih => cases h <;> simp [Hyp.wrap, ih]

/-! ## The states a context leads to -/

/-- `Reaches Γ σ τ`: running the context `Γ` from `σ` ends in `τ` — every
update returns, every precondition holds where it is met, and a `havoc`
leaves any storage and ledger. -/
def Hyp.Reaches : List (Hyp C) → State → State → Prop
  | [], σ, τ => τ = σ
  | .pre a :: Γ, σ, τ => holds σ a ∧ Hyp.Reaches Γ σ τ
  | .upd _ U :: Γ, σ, τ => ∃ ρ, U.apply σ = .ok ρ ∧ Hyp.Reaches Γ ρ τ
  | .havoc :: Γ, σ, τ => ∃ st nt, Hyp.Reaches Γ (σ.havoc st nt) τ
  | .all x p :: Γ, σ, τ => ∃ v, p.admits v ∧ Hyp.Reaches Γ (σ.setEnv x (.val v)) τ

/-- What follows a context is judged only in the states it leads to. -/
theorem Hyp.wrap_reach {A B : Fml C} : (Γ : List (Hyp C)) → ∀ σ,
    (∀ τ, Hyp.Reaches Γ σ τ → holds τ A → holds τ B) →
      holds σ (Hyp.wrap Γ A) → holds σ (Hyp.wrap Γ B)
  | [], σ, h => h σ rfl
  | .pre _ :: Γ, σ, h => fun hA ha => Hyp.wrap_reach Γ σ (fun τ hr => h τ ⟨ha, hr⟩) (hA ha)
  | .upd m U :: Γ, σ, h => by
    simp only [Hyp.wrap, holds]
    cases hU : U.apply σ with
    | error _ => exact id
    | ok ρ => exact Hyp.wrap_reach Γ ρ (fun τ hr => h τ ⟨ρ, hU, hr⟩)
  | .havoc :: Γ, σ, h => fun hA st nt =>
    Hyp.wrap_reach Γ _ (fun τ hr => h τ ⟨st, nt, hr⟩) (hA st nt)
  | .all _ _ :: Γ, σ, h => fun hA v hv =>
    Hyp.wrap_reach Γ _ (fun τ hr => h τ ⟨v, hv, hr⟩) (hA v hv)

/-- An implication between two formulas survives wrapping both in the same
context. -/
theorem Hyp.wrap_mono {ψ φ : Fml C} (h : ∀ σ, holds σ ψ → holds σ φ) (Γ : List (Hyp C))
    (σ : State) : holds σ (Hyp.wrap Γ ψ) → holds σ (Hyp.wrap Γ φ) :=
  Hyp.wrap_reach Γ σ fun τ _ => h τ

/-- A state `Γ ++ Δ` leads to is one `Δ` leads to from a state `Γ` leads to. -/
theorem Hyp.reaches_append : (Γ Δ : List (Hyp C)) → ∀ σ τ,
    Hyp.Reaches (Γ ++ Δ) σ τ → ∃ ρ, Hyp.Reaches Γ σ ρ ∧ Hyp.Reaches Δ ρ τ
  | [], _, σ, _, h => ⟨σ, rfl, h⟩
  | .pre _ :: Γ, Δ, σ, τ, ⟨ha, h⟩ =>
    let ⟨ρ, h₁, h₂⟩ := Hyp.reaches_append Γ Δ σ τ h
    ⟨ρ, ⟨ha, h₁⟩, h₂⟩
  | .upd _ _ :: Γ, Δ, _, τ, ⟨ρ', hU, h⟩ =>
    let ⟨ρ, h₁, h₂⟩ := Hyp.reaches_append Γ Δ ρ' τ h
    ⟨ρ, ⟨ρ', hU, h₁⟩, h₂⟩
  | .havoc :: Γ, Δ, _, τ, ⟨st, nt, h⟩ =>
    let ⟨ρ, h₁, h₂⟩ := Hyp.reaches_append Γ Δ _ τ h
    ⟨ρ, ⟨st, nt, h₁⟩, h₂⟩
  | .all _ _ :: Γ, Δ, _, τ, ⟨v, hv, h⟩ =>
    let ⟨ρ, h₁, h₂⟩ := Hyp.reaches_append Γ Δ _ τ h
    ⟨ρ, ⟨v, hv, h₁⟩, h₂⟩

/-- No diamond update in the context: a halting update proves what follows. -/
def Hyp.boxOnly : List (Hyp C) → Bool
  | [] => true
  | .upd .diamond _ :: _ => false
  | _ :: Γ => Hyp.boxOnly Γ

/-- Behind a context with no diamond, what holds in every state it leads to
holds. -/
theorem Hyp.wrap_of_reaches {φ : Fml C} : (Γ : List (Hyp C)) → Hyp.boxOnly Γ = true → ∀ σ,
    (∀ τ, Hyp.Reaches Γ σ τ → holds τ φ) → holds σ (Hyp.wrap Γ φ)
  | [], _, σ, h => h σ rfl
  | .pre _ :: Γ, hb, σ, h => fun ha => Hyp.wrap_of_reaches Γ hb σ (fun τ hr => h τ ⟨ha, hr⟩)
  | .upd .box U :: Γ, hb, σ, h => by
    simp only [Hyp.wrap, holds]
    cases hU : U.apply σ with
    | error _ => trivial
    | ok ρ => exact Hyp.wrap_of_reaches Γ hb ρ (fun τ hr => h τ ⟨ρ, hU, hr⟩)
  | .upd .diamond _ :: _, hb, _, _ => by cases hb
  | .havoc :: Γ, hb, σ, h => fun st nt =>
    Hyp.wrap_of_reaches Γ hb _ (fun τ hr => h τ ⟨st, nt, hr⟩)
  | .all _ _ :: Γ, hb, σ, h => fun v hv =>
    Hyp.wrap_of_reaches Γ hb _ (fun τ hr => h τ ⟨v, hv, hr⟩)

/-- What is valid is valid behind a context with no diamond. -/
theorem Hyp.valid_wrap {φ : Fml C} {Γ : List (Hyp C)} (hb : Hyp.boxOnly Γ = true) (h : Valid φ) :
    Valid (Hyp.wrap Γ φ) :=
  fun σ => Hyp.wrap_of_reaches Γ hb σ fun τ _ => h τ

/-- Past a `havoc`, what came before is forgotten: a sequent valid from the
`havoc` on is valid behind a context with no diamond in front of it. -/
theorem Hyp.valid_after_havoc {φ : Fml C} {Γ Δ : List (Hyp C)} (hb : Hyp.boxOnly Γ = true)
    (h : Valid (Hyp.wrap Δ φ)) : Valid (Hyp.wrap (Γ ++ .havoc :: Δ) φ) := by
  rw [Hyp.wrap_append]
  exact Hyp.valid_wrap hb fun σ _ _ => h _

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
  | .havoc :: Γ => fun σ h₁ h₂ h₃ st nt =>
    Hyp.wrap_mono₃ h Γ _ (h₁ st nt) (h₂ st nt) (h₃ st nt)
  | .all _ _ :: Γ => fun σ h₁ h₂ h₃ v hv =>
    Hyp.wrap_mono₃ h Γ _ (h₁ v hv) (h₂ v hv) (h₃ v hv)

/-- `Hyp.wrap_mono` for two premises. -/
theorem Hyp.wrap_mono₂ {ψ₁ ψ₂ φ : Fml C} (h : ∀ σ, holds σ ψ₁ → holds σ ψ₂ → holds σ φ)
    (Γ : List (Hyp C)) (σ : State) (h₁ : holds σ (Hyp.wrap Γ ψ₁)) (h₂ : holds σ (Hyp.wrap Γ ψ₂)) :
    holds σ (Hyp.wrap Γ φ) :=
  Hyp.wrap_mono₃ (ψ₃ := .tt) (fun σ h₁ h₂ _ => h σ h₁ h₂) Γ σ h₁ h₂
    (Hyp.wrap_mono (ψ := ψ₁) (φ := .tt) (fun _ _ => trivial) Γ σ h₁)

/-- A conjunction holds behind a context where each of its conjuncts does. -/
theorem Hyp.wrap_conj (Γ : List (Hyp C)) : (φs : List (Fml C)) →
    (∀ φ ∈ φs, Valid (Hyp.wrap Γ φ)) → φs ≠ [] → ∀ σ, holds σ (Hyp.wrap Γ (Fml.conj φs))
  | [φ], h, _, σ => h φ List.mem_cons_self σ
  | φ :: ψ :: φs, h, _, σ =>
    Hyp.wrap_mono₂ (fun _ h₁ h₂ => by simp only [Fml.conj, holds] at h₂ ⊢; exact ⟨h₁, h₂⟩) Γ σ
      (h φ List.mem_cons_self σ) (Hyp.wrap_conj Γ (ψ :: φs) (fun χ hχ => h χ (List.mem_cons_of_mem _ hχ)) (by simp) σ)

/-- A variable of a formula is a variable of the formula wrapped in a context. -/
theorem Hyp.vars_wrap {x : Var} {φ : Fml C} :
    (Γ : List (Hyp C)) → x ∈ φ.vars → x ∈ (Hyp.wrap Γ φ).vars
  | [], h => h
  | .pre _ :: Γ, h | .upd _ _ :: Γ, h | .havoc :: Γ, h | .all _ _ :: Γ, h => by
    simp [Hyp.wrap, Fml.vars, Hyp.vars_wrap Γ h]

/-- A taclet applied in a context is sound: its fresh names are fresh.

Example: `apply Proves.update .storageFieldWriteSave` on
`{ se1 := 10 }, { sp1 := alice.account } ⟹ ⟨ sp1.balance = se1; ⟩ φ` is sound:
the taclet's index is `Hyp.fresh` of the whole sequent, so the names it could
introduce avoid `se1`, `sp1` and every other name in sight. -/
theorem Taclet.sound_in {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}
    {p : Premise C} (d : Taclet C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s p) :
    ∀ σ, holds σ (p.fml m ω φ) → holds σ (.modal m (s :: ω) φ) :=
  Premise.sound_above d.sound (Nat.lt_succ_self _) fun _ => Hyp.vars_wrap Γ

/-- `Taclet.sound_in` for a rule solkey does not have. -/
theorem LeanTaclet.sound_in {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C}
    {φ : Fml C} {p : Premise C} (d : LeanTaclet C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s p) :
    ∀ σ, holds σ (p.fml m ω φ) → holds σ (.modal m (s :: ω) φ) :=
  Premise.sound_above d.sound (Nat.lt_succ_self _) fun _ => Hyp.vars_wrap Γ

/-! ### The Theory rewrite -/

/-- Rewriting the context and the goal is rewriting the sequent. -/
theorem Hyp.wrap_rwEq (q : Term C × Term C) (φ : Fml C) :
    (Γ : List (Hyp C)) → Hyp.wrap (Hyp.rwEq q Γ) (φ.rwEq q) = (Hyp.wrap Γ φ).rwEq q
  | [] => rfl
  | .pre _ :: Γ | .upd _ _ :: Γ | .havoc :: Γ | .all _ _ :: Γ => by
    simp only [Hyp.rwEq, Hyp.wrap, Fml.rwEq, Hyp.wrap_rwEq q φ Γ]

/-- A sequent rewritten by a Theory equation holds where the sequent does. -/
theorem Proves.rewrite_sound {Γ : List (Hyp C)} {φ : Fml C} {t t' : Term C}
    (h : Term.Theq t t') (d : Valid (Hyp.wrap (Hyp.rwEq (t, t') Γ) (Fml.rwEq (t, t') φ))) :
    Valid (Hyp.wrap Γ φ) := fun σ => by
  have hσ : holds σ (Hyp.wrap (Hyp.rwEq (t, t') Γ) (Fml.rwEq (t, t') φ)) := d σ
  rw [Hyp.wrap_rwEq] at hσ
  exact (Fml.rwEq_holds (q := (t, t')) h _ σ).1 hσ

/-! ### The update rules -/

/-- A context whose box updates are rewritten gives the context: each
rewritten box update gives the update (`Upd.rw_box`). -/
theorem Hyp.rwUpd_wrap {q : Term C × Term C} (hq : Term.EvalRefines q.1 q.2) {φ : Fml C} :
    (Γ : List (Hyp C)) → ∀ σ, holds σ (Hyp.wrap (Hyp.rwUpd q Γ) φ) → holds σ (Hyp.wrap Γ φ)
  | [], _, h => h
  | .pre _ :: Γ, σ, h => fun ha => Hyp.rwUpd_wrap hq Γ σ (h ha)
  | .upd .box _ :: Γ, σ, h => Upd.rw_box hq (Hyp.rwUpd_wrap hq Γ) σ h
  | .upd .diamond U :: Γ, σ, h => by
    simp only [Hyp.rwUpd, Hyp.wrap, holds] at h ⊢
    cases hU : U.apply σ with
    | error _ => rw [hU] at h; exact h
    | ok τ => rw [hU] at h; exact Hyp.rwUpd_wrap hq Γ τ h
  | .havoc :: Γ, σ, h => fun st nt => Hyp.rwUpd_wrap hq Γ _ (h st nt)
  | .all _ _ :: Γ, σ, h => fun v hv => Hyp.rwUpd_wrap hq Γ _ (h v hv)

theorem Proves.merge_sound {Γ : List (Hyp C)} {m : Modality} {U V : Upd C} {φ : Fml C}
    (hU : U.envOnly = true) (d : Valid (Hyp.wrap (Γ ++ [.upd m (U ++ V.subst U)]) φ)) :
    Valid (Hyp.wrap (Γ ++ [.upd m U] ++ [.upd m V]) φ) := fun σ => by
  have hσ : holds σ (Hyp.wrap (Γ ++ [.upd m (U ++ V.subst U)]) φ) := d σ
  simp only [List.append_assoc, List.cons_append, List.nil_append, Hyp.wrap_append,
    Hyp.wrap] at hσ ⊢
  exact Hyp.wrap_mono (fun τ hτ => ((UpdRule.sequentialToParallel (u2 := V) (φ := φ) hU).sound τ).1 hτ)
    Γ σ hσ

theorem Proves.mergeStorage_sound {Γ : List (Hyp C)} {m : Modality} {s : STerm C} {V : Upd C}
    {φ : Fml C} (hV : V.all (·.stExplicit) = true)
    (d : Valid (Hyp.wrap (Γ ++ [.upd m (.storage s :: V.withSt s)]) φ)) :
    Valid (Hyp.wrap (Γ ++ [.upd m [.storage s]] ++ [.upd m V]) φ) := fun σ => by
  have hσ : holds σ (Hyp.wrap (Γ ++ [.upd m (.storage s :: V.withSt s)]) φ) := d σ
  simp only [List.append_assoc, List.cons_append, List.nil_append, Hyp.wrap_append,
    Hyp.wrap] at hσ ⊢
  exact Hyp.wrap_mono (fun τ hτ => (Upd.mergeStorage_holds m s V hV φ τ).1 hτ) Γ σ hσ

theorem Proves.simplify_sound {Γ : List (Hyp C)} {m : Modality} {U : Upd C} {φ : Fml C}
    (d : Valid (Hyp.wrap (Γ ++ [.upd m (U.dropEffectless φ.vars)]) φ)) :
    Valid (Hyp.wrap (Γ ++ [.upd m U]) φ) := fun σ => by
  have hσ : holds σ (Hyp.wrap (Γ ++ [.upd m (U.dropEffectless φ.vars)]) φ) := d σ
  simp only [Hyp.wrap_append, Hyp.wrap] at hσ ⊢
  exact Hyp.wrap_mono (fun τ hτ => (Upd.dropEffectless_holds m U φ τ).1 hτ) Γ σ hσ

theorem Proves.applyOnRigidBox_sound {Γ : List (Hyp C)} {U : Upd C} {φ : Fml C}
    (hU : (U.envOnly || U.localsOrStorage && φ.stFree) = true) (hr : φ.rigid = true)
    (hs : φ.sortedFor U = true) (d : Valid (Hyp.wrap Γ (φ.subst U))) :
    Valid (Hyp.wrap (Γ ++ [.upd .box U]) φ) := fun σ => by
  rw [Hyp.wrap_append]
  refine Hyp.wrap_mono (fun τ hτ => ?_) Γ σ (d σ)
  rcases Bool.or_eq_true_iff.1 hU with hU | hU
  · exact Fml.subst_box hU hr hs τ hτ
  · simp only [Bool.and_eq_true] at hU
    exact Fml.subst_box_st hU.1 hU.2 hs τ hτ

theorem Proves.applyStorageBox_sound {Γ : List (Hyp C)} {s : STerm C} {φ : Fml C}
    (hr : φ.rigid = true) (he : φ.stExplicit = true) (d : Valid (Hyp.wrap Γ (φ.withSt s))) :
    Valid (Hyp.wrap (Γ ++ [.upd .box [.storage s]]) φ) := fun σ => by
  rw [Hyp.wrap_append]
  exact Hyp.wrap_mono (fun τ hτ => Fml.withSt_box hr he τ hτ) Γ σ (d σ)

open Proves in
/-- **Soundness of the calculus**: a derivation of `Γ ⊢ φ` proves `φ`
wrapped in its context `Γ`.

Example: from the derivation of `a == 1 ⟹ ⟨ x = a; ⟩ x == 1` (one
`localValueAssign`, `empty`, then `close`) follows
`⊨ a == 1 → ⟨ x = a; ⟩ x == 1`. -/
theorem Proves.sound {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} (h : Proves R Γ φ) :
    Valid (Hyp.wrap Γ φ) := by
  induction h with
  | intro _ ih => simpa [Hyp.wrap_append, Hyp.wrap] using ih
  | update d _ ih =>
    rw [Hyp.wrap_append] at ih
    exact fun σ => Hyp.wrap_mono d.sound_in _ σ (ih σ)
  | unfold d _ ih | done d _ ih => exact fun σ => Hyp.wrap_mono d.sound_in _ σ (ih σ)
  | unfoldLean d _ ih | doneLean d _ ih => exact fun σ => Hyp.wrap_mono d.sound_in _ σ (ih σ)
  | @branches _ Γ m s ω φ bs d _ ih =>
    have hne : bs ≠ [] := by cases d; simp
    exact fun σ => Hyp.wrap_mono d.sound_in _ σ (Hyp.wrap_conj _ _
      (fun ψ hψ => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hψ
        exact ih b hb) (by simpa using hne) σ)
  | @cases _ Γ m s ω φ fs us d _ _ ih₁ ih₂ =>
    have hne : fs ++ us.map (fun U => Fml.upd m U (.modal m ω φ)) ≠ [] := by
      cases d <;> simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        ne_eq, reduceCtorEq, not_false_eq_true]
    exact fun σ => Hyp.wrap_mono d.sound_in _ σ (Hyp.wrap_conj _ _
      (fun ψ hψ => by
        rcases List.mem_append.1 hψ with hf | hu
        · exact ih₁ ψ hf
        · obtain ⟨U, hU, rfl⟩ := List.mem_map.1 hu
          have := ih₂ U hU
          rw [Hyp.wrap_append] at this
          exact this) hne σ)
  | allIntro _ ih => simpa [Hyp.wrap_append, Hyp.wrap] using ih
  | updIntro _ ih => simpa [Hyp.wrap_append, Hyp.wrap] using ih
  | split d _ _ _ ih₁ ih₂ ih₃ =>
    rw [Hyp.wrap_append] at ih₁ ih₂
    exact fun σ => Hyp.wrap_mono₃ (fun τ h₁ h₂ h₃ => d.sound_in τ ⟨h₁, h₂, (Premise.coverFml_holds _ _ _ τ).2 h₃⟩) _ σ
      (ih₁ σ) (ih₂ σ) (ih₃ σ)
  | check d _ _ ih₁ ih₂ =>
    rw [Hyp.wrap_append] at ih₁
    exact fun σ => Hyp.wrap_mono₂ (fun τ h₁ h₂ => d.sound_in τ ⟨h₁, h₂⟩) _ σ (ih₁ σ) (ih₂ σ)
  | @empty _ Γ m φ _ ih =>
    exact fun σ => Hyp.wrap_mono (ψ := φ) (φ := .modal m [] φ)
      (fun _ h => ⟨by cases m <;> exact h, nofun⟩) Γ σ (ih σ)
  | rewrite r _ ih => exact Proves.rewrite_sound r.sound ih
  | updRw r ht _ ih => exact fun σ => Hyp.rwUpd_wrap (Term.EvalRefines.of_theq r.sound ht) _ σ (ih σ)
  | merge hU _ ih => exact Proves.merge_sound hU ih
  | mergeStorage _ hV ih => exact Proves.mergeStorage_sound hV ih
  | simplify _ ih => exact Proves.simplify_sound ih
  | applyOnRigidBox _ hU hr hs ih => exact Proves.applyOnRigidBox_sound hU hr hs ih
  | applyStorageBox _ hr he ih => exact Proves.applyStorageBox_sound hr he ih
  | close h _ => exact h

open Proves in
/-- A derivation from the empty context proves validity: `⊢ φ` gives `⊨ φ`. -/
theorem Proves.valid {φ : Fml C} (h : ⊢ φ) : Valid φ := h.sound

/-- `unfold` by whichever rule `Rule` names: `apply unfoldRule
(Stmt.step _ _ _).rule` takes the strategy's rule without naming it. -/
theorem Proves.unfoldRule {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C}
    {φ : Fml C} {P : Prog C} (d : Rule C (Hyp.fresh Γ (.modal m (s :: ω) φ)) m s (.unfold P))
    (h : Proves .all Γ (.modal m (P ++ ω) φ)) : Proves .all Γ (.modal m (s :: ω) φ) := by
  cases d with
  | key d => exact .unfold d h
  | lean d => exact .unfoldLean d h

/-- solkey's rules are some of the rules: `Γ ⊢ₖ φ` gives `Γ ⊢ φ`. -/
theorem Proves.toAll {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} (h : Proves R Γ φ) :
    Proves .all Γ φ := by
  induction h with
  | intro _ ih => exact .intro ih
  | update d _ ih => exact .update d ih
  | unfold d _ ih => exact .unfold d ih
  | unfoldLean d h _ => exact .unfoldLean d h
  | doneLean d h _ => exact .doneLean d h
  | branches d _ ih => exact .branches d ih
  | cases d _ _ ih₁ ih₂ => exact .cases d ih₁ ih₂
  | allIntro _ ih => exact .allIntro ih
  | updIntro _ ih => exact .updIntro ih
  | split d _ _ _ ih₁ ih₂ ih₃ => exact .split d ih₁ ih₂ ih₃
  | check d _ _ ih₁ ih₂ => exact .check d ih₁ ih₂
  | done d _ ih => exact .done d ih
  | empty _ ih => exact .empty ih
  | rewrite r _ ih => exact .rewrite r ih
  | updRw r ht _ ih => exact .updRw r ht ih
  | merge hU _ ih => exact .merge hU ih
  | mergeStorage _ hV ih => exact .mergeStorage ih hV
  | simplify _ ih => exact .simplify ih
  | applyOnRigidBox _ hU hr hs ih => exact .applyOnRigidBox ih hU hr hs
  | applyStorageBox _ hr he ih => exact .applyStorageBox ih hr he
  | close h hφ => exact .close h hφ

/-! ## Printing sequents

`Proves Γ φ` prints as the sequent `dl{ Γ ⟹ φ }`, so every goal of an
`apply` derivation reads as the line of the derivation it is: the context
left of `⟹`, in order, and the formula still to prove right of it.  A goal
of `⊢ₖ`, solkey's rules alone, prints as `dl{ Γ ⟹ₖ φ }`; both read back. -/

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr
set_option hygiene false

def ppHyp? (e : Lean.Expr) : MetaM (Option (TSyntax `dl_hyp)) := do
  match_expr (← whnf (← instantiateMVars e)) with
  | Hyp.pre _ a => return some (← `(dl_hyp| $(← ppFml a):dl_fml))
  | Hyp.upd _ m U =>
    let u ← ppUpd U
    -- an escaped update would read back as a precondition
    if isEscape u then return none
    -- a rule's update, at a fixed modality: `{U} [ ]`, `{U} ⟨ ⟩`
    if (← instantiateMVars U).hasFVar then
      match_expr (← whnf m) with
      | Modality.box => return some (← `(dl_hyp| $u:dl_upd [ ]))
      | Modality.diamond => return some (← `(dl_hyp| $u:dl_upd ⟨ ⟩))
      | _ => pure ()
    return some (← `(dl_hyp| $u:dl_upd))
  | Hyp.havoc _ => return some (← `(dl_hyp| { havoc }))
  | Hyp.all _ x p =>
    let some x ← ppVar? x | return none
    let some T ← (do pure ((← primName? p) <|> (← fvarName? p))) | return none
    return some (← `(dl_hyp| ∀ $(mkIdent (Name.mkSimple T)):ident $x:ident))
  | _ => return none

/-- A context: the rest `..Γ` when it is a variable, then its entries, read
off the spine `Γ ++ [h₁] ++ …` the rules write. -/
partial def hypSpine? (e : Lean.Expr) : MetaM (Option (Option Ident × Array Lean.Expr)) := do
  let e ← instantiateMVars e
  if let some n ← fvarName? e then return some (some (nameIdent n), #[])
  if e.isAppOfArity ``HAppend.hAppend 6 then
    let some (Γ, hs) ← hypSpine? (e.getArg! 4) | return none
    let some hs' ← listElems? (e.getArg! 5) | return none
    return some (Γ, hs ++ hs')
  let some hs ← listElems? e | return none
  return some (none, hs)

/-- `Proves .all Γ φ`: `dl{ Γ ⟹ φ }`; `Proves .solkey Γ φ`: `dl{ Γ ⟹ₖ φ }`;
over a rule set `R` that is a variable, `dl{ Γ ⟹[R] φ }`.  A context `Γ ++ […]`
prints `..Γ` first. -/
@[delab app.Solidity.Proves]
def delabProves : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  let R ← whnf (e.getArg! 1)
  let some (rest, hs) ← hypSpine? (e.getArg! 2) | failure
  let mut out := #[]
  if let some Γ := rest then out := out.push (← `(dl_hyp| ..$Γ:ident))
  for h in hs do
    let some h ← ppHyp? h | failure
    out := out.push h
  let φ ← ppFml (e.getArg! 3)
  guard !(isEscape φ)
  if R.isConstOf ``RuleSet.all then `(dl{ $[$out],* ⟹ $φ:dl_fml })
  else if R.isConstOf ``RuleSet.solkey then `(dl{ $[$out],* ⟹ₖ $φ:dl_fml })
  else if let some r ← fvarName? R then `(dl{ $[$out],* ⟹[$(nameIdent r)] $φ:dl_fml })
  else failure

end Print

end Solidity
