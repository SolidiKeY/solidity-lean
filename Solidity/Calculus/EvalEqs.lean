import Solidity.Calculus.TermAgree

/-!
# Equations read by the interpreter, for the closer

An equation `a = b` is read in the Theory (`Tm.denote`), total as KeY's
`=`; the closer computes the typed reading (`Tm.eval`).  `Fml.evalEqs`
reads each equation the closer is to prove by an update, as the rules read
a condition: `{ x := a ‖ y := b } (x = y)` under the diamond, which implies
it (both sides return, with one value, `Tm.denote_eval`).  It goes down the
goal only (a conjunct, the conclusion of an implication, under an update or
a binder), not into an assumption or under a negation, which the closer
reads as it is.  An equation of terms the Theory reads as the
interpreter does (`Tm.agreeB`, `Calculus/TermAgree.lean`) is marked so,
which the closer reads by value (`Fml.eqT`, `Fml.eqA`; of locals and
literals `Fml.eqAtom`, which needs no proof), and one with a side that may
exhaust (`Tm.pushFree`) is left as it is.  So the closer's leaf implies the
formula (`Fml.evalEqs_sound`).
-/

namespace Solidity

variable {C : Contract}


/-- A local, a literal or a value of the transaction: a term that returns in
every state, read by value. -/
inductive Fml.Atom (C : Contract) (Γ : Ctx) : PrimTy → Type where
  | loc {p : PrimTy} (i : Idx Γ (.val p)) : Fml.Atom C Γ p
  | lit {p : PrimTy} (v : p.Denote) : Fml.Atom C Γ p
  | env (k : EnvKey) : Fml.Atom C Γ .uint

/-- The atom's term. -/
def Fml.Atom.tm {Γ : Ctx} : {p : PrimTy} → Fml.Atom C Γ p → Tm C Γ (.val p)
  | _, .loc i => .pvV i
  | _, .lit v => .app0 (.lit v)
  | _, .env k => .app0 (.env k)

/-- An atom returns its value in every state. -/
theorem Fml.Atom.eval_some {Γ : Ctx} {p : PrimTy} (x : Fml.Atom C Γ p) (σ : State C Γ) :
    ∃ v, x.tm.eval σ = some v := by
  cases x <;> exact ⟨_, rfl⟩

/-- `a = b` of two atoms, marked for the closer (`CloseS.holds_eqAtom`):
the equation itself. -/
def Fml.eqAtom {Γ : Ctx} {p : PrimTy} (x y : Fml.Atom C Γ p) : Fml C Γ := .eq x.tm y.tm

/-- `{ x := a ‖ y := b } (x = y)`, the update under `m`, its equation one
of atoms. -/
def Fml.eqCap {Γ : Ctx} {p : PrimTy} (m : Modality) (a b : Tm C Γ (.val p)) : Fml C Γ :=
  .upd m ((Upd.nil.decl (fse 0) (.val a)).decl (fse 1) (.val b))
    (Fml.eqAtom (.loc (.there .here)) (.loc .here))

/-- `a = b` where the Theory reads both sides as the interpreter does and one
of them returns (`Tm.agreeB`, `Tm.totB`): the equation itself, marked with
the proof for the closer (`CloseS.holds_eqT`). -/
def Fml.eqT {Γ : Ctx} {p : PrimTy} (a b : Tm C Γ (.val p))
    (_ : (a.agreeB && b.agreeB && (a.totB || b.totB)) = true) : Fml C Γ := .eq a b

/-- `a = b` where the Theory reads both sides as the interpreter does
(`Tm.agreeB`): the equation itself, marked (`CloseS.holds_eqA`). -/
def Fml.eqA {Γ : Ctx} {p : PrimTy} (a b : Tm C Γ (.val p))
    (_ : (a.agreeB && b.agreeB) = true) : Fml C Γ := .eq a b

/-- An equation for the closer: marked where its sides agree; else, where it
is to be proved (`goal`), read by the interpreter under the diamond. -/
def Fml.eqFor {Γ : Ctx} {p : PrimTy} (goal : Bool) (a b : Tm C Γ (.val p)) : Fml C Γ :=
  if h : (a.agreeB && b.agreeB && (a.totB || b.totB)) = true then .eqT a b h
  else if h : (a.agreeB && b.agreeB) = true then .eqA a b h
  else if goal && a.pushFree && b.pushFree then .eqCap .diamond a b
  else .eq a b

/-- Every equation for the closer (`Fml.eqFor`), `goal` where it is to be
proved: a conjunct, the conclusion of an implication, under an update or a
binder, not under a negation or in an assumption. -/
def Fml.evalEqs : Bool → {Γ : Ctx} → Fml C Γ → Fml C Γ
  | goal, _, .eq a b => Fml.eqFor goal a b
  | _, _, .not φ => .not (Fml.evalEqs false φ)
  | goal, _, .and φ ψ => .and (Fml.evalEqs goal φ) (Fml.evalEqs goal ψ)
  | goal, _, .imp φ ψ => .imp (Fml.evalEqs false φ) (Fml.evalEqs goal ψ)
  | goal, _, .upd m U φ => .upd m U (Fml.evalEqs goal φ)
  | goal, _, .all x p φ => .all x p (Fml.evalEqs goal φ)
  | goal, _, .bind m x t φ => .bind m x t (Fml.evalEqs goal φ)
  | goal, _, .havoc φ => .havoc (Fml.evalEqs goal φ)
  | goal, _, .anon xs φ => .anon xs (Fml.evalEqs goal φ)
  | goal, _, .allocAll x A φ => .allocAll x A (Fml.evalEqs goal φ)
  | _, _, φ => φ

/-- The update of `Fml.eqCap` returns where both sides do. -/
theorem Fml.eqCap_globT {Γ : Ctx} {p : PrimTy} (a b : Tm C Γ (.val p)) (σ : State C Γ) :
    ((Upd.nil.decl (fse 0) (.val a)).decl (fse 1) (.val b)).globT σ =
      ((a.eval σ).bind fun _ => some σ.globG).bind fun g => (b.eval σ).bind fun _ => some g :=
  rfl

/-- **`Fml.eqCap` under the diamond gives the equation.** -/
theorem Fml.eqCap_holds {Γ : Ctx} {p : PrimTy} (a b : Tm C Γ (.val p))
    (hf : (a.pushFree && b.pushFree) = true) (σ : State C Γ) :
    holds σ (Fml.eqCap .diamond a b) → holds σ (.eq a b) := by
  have hx : ((Upd.nil.decl (fse 0) (.val a)).decl (fse 1) (.val b)).exh σ = false :=
    Upd.exh_of_pushFree (by
      simp only [Bool.and_eq_true] at hf
      simp only [Upd.pushFree, Rhs.pushFree, hf.1, hf.2, Bool.and_self])
  cases ha : a.eval σ with
  | none =>
    have hg : ((Upd.nil.decl (fse 0) (.val a)).decl (fse 1) (.val b)).globT σ = none := by
      rw [Fml.eqCap_globT, ha]; rfl
    exact fun h => (h.of_noExh hg hx).elim
  | some x =>
    cases hb : b.eval σ with
    | none =>
      have hg : ((Upd.nil.decl (fse 0) (.val a)).decl (fse 1) (.val b)).globT σ = none := by
        rw [Fml.eqCap_globT, ha, hb]; rfl
      exact fun h => (h.of_noExh hg hx).elim
    | some y =>
      have hl := Upd.lands_decl (Upd.lands_decl (Upd.lands_nil σ) (fse 0)
        (show (Rhs.val a).eval σ = some (LTy.VDen.ofT (H := σ.H) (.val p) x) from ha)) (fse 1)
        (show (Rhs.val b).eval σ = some (LTy.VDen.ofT (H := σ.H) (.val p) y) from hb)
      exact fun h => (holds_eq_of_eval ha hb).2 (Option.some.inj (h.of_lands hl))

/-- An equation for the closer: as a goal it gives the equation, elsewhere it
is the equation. -/
theorem Fml.eqFor_holds {Γ : Ctx} {p : PrimTy} (a b : Tm C Γ (.val p)) (σ : State C Γ) :
    (holds σ (Fml.eqFor true a b) → holds σ (.eq a b)) ∧
      (holds σ (Fml.eqFor false a b) ↔ holds σ (.eq a b)) := by
  unfold Fml.eqFor
  split
  · exact ⟨id, Iff.rfl⟩
  split
  · exact ⟨id, Iff.rfl⟩
  constructor
  · split
    · rename_i hf
      simp only [Bool.true_and, Bool.and_eq_true] at hf
      exact Fml.eqCap_holds a b (by rw [hf.1, hf.2]; rfl) σ
    · exact id
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- **The closer's leaf implies the formula**, and off the goal is it. -/
theorem Fml.evalEqs_sound : (goal : Bool) → {Γ : Ctx} → (φ : Fml C Γ) → ∀ σ : State C Γ,
    (goal = true → holds σ (Fml.evalEqs goal φ) → holds σ φ) ∧
      (goal = false → (holds σ (Fml.evalEqs goal φ) ↔ holds σ φ))
  | goal, _, .eq a b, σ => by
    obtain ⟨h₁, h₂⟩ := Fml.eqFor_holds a b σ
    exact ⟨fun hg => by subst hg; exact h₁, fun hg => by subst hg; exact h₂⟩
  | _, _, .not φ, σ =>
    have ih := (Fml.evalEqs_sound false φ σ).2 rfl
    ⟨fun _ h hφ => h (ih.2 hφ), fun _ => not_congr ih⟩
  | goal, _, .and φ ψ, σ => by
    obtain ⟨i₁, j₁⟩ := Fml.evalEqs_sound goal φ σ
    obtain ⟨i₂, j₂⟩ := Fml.evalEqs_sound goal ψ σ
    exact ⟨fun hg h => ⟨i₁ hg h.1, i₂ hg h.2⟩, fun hg => and_congr (j₁ hg) (j₂ hg)⟩
  | goal, _, .imp φ ψ, σ => by
    have ih := (Fml.evalEqs_sound false φ σ).2 rfl
    obtain ⟨i₂, j₂⟩ := Fml.evalEqs_sound goal ψ σ
    exact ⟨fun hg h hφ => i₂ hg (h (ih.2 hφ)), fun hg => imp_congr ih (j₂ hg)⟩
  | goal, _, .upd m U φ, σ =>
    ⟨fun hg h => Upd.afterT_imp h fun τ => (Fml.evalEqs_sound goal φ τ).1 hg,
      fun hg => ⟨fun h => Upd.afterT_imp h fun τ => ((Fml.evalEqs_sound goal φ τ).2 hg).1,
        fun h => Upd.afterT_imp h fun τ => ((Fml.evalEqs_sound goal φ τ).2 hg).2⟩⟩
  | goal, _, .all x p φ, σ =>
    ⟨fun hg h v => (Fml.evalEqs_sound goal φ _).1 hg (h v),
      fun hg => forall_congr' fun v => (Fml.evalEqs_sound goal φ _).2 hg⟩
  | goal, _, .bind m x t φ, σ =>
    ⟨fun hg h => Modality.forallB_imp (fun _ => (Fml.evalEqs_sound goal φ _).1 hg) h,
      fun hg => ⟨Modality.forallB_imp (fun _ => ((Fml.evalEqs_sound goal φ _).2 hg).1),
        Modality.forallB_imp (fun _ => ((Fml.evalEqs_sound goal φ _).2 hg).2)⟩⟩
  | goal, _, .havoc φ, σ =>
    ⟨fun hg h st nt => (Fml.evalEqs_sound goal φ _).1 hg (h st nt),
      fun hg => forall_congr' fun st => forall_congr' fun nt => (Fml.evalEqs_sound goal φ _).2 hg⟩
  | goal, _, .anon xs φ, σ =>
    ⟨fun hg h b => (Fml.evalEqs_sound goal φ _).1 hg (h b),
      fun hg => forall_congr' fun b => (Fml.evalEqs_sound goal φ _).2 hg⟩
  | goal, _, .allocAll x A φ, σ =>
    ⟨fun hg h o => (Fml.evalEqs_sound goal φ _).1 hg (h o),
      fun hg => forall_congr' fun o => (Fml.evalEqs_sound goal φ _).2 hg⟩
  | _, _, .tt, _ | _, _, .wellFormed _, _ | _, _, .modal .., _ => ⟨fun _ => id, fun _ => Iff.rfl⟩

/-- A formula is valid where its closer's leaf is. -/
theorem Valid.of_evalEqs {φ : Fml C []} (h : Valid (Fml.evalEqs true φ)) : Valid φ :=
  fun σ => (Fml.evalEqs_sound true φ σ).1 rfl (h σ)

end Solidity
