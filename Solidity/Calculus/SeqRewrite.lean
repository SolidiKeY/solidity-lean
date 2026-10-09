import Solidity.Calculus.Graft

/-!
# A Theory equation in every equation of a scoped sequent

The scoped twin of `NFml.rwEq` and `Hyp.rwEq` (`Calculus/Hyp.lean`), the
rewrite of today's `Proves.rewrite` (`Calculus/NFmlLogic.lean`): a side of
an equation that is a closed term reading `q.1` on its erasure becomes
`q.2` (`Tm.sideC`), in every equation of the formula, at any depth of its
connectives, updates, quantifiers and hidden binders, and in the
postcondition of a modality still open (`Fml.rwEqC`).  A Theory equation
holds in every state (`Term.Theq`), so the formula rewritten holds exactly
where it does (`Fml.rwEqC_holds`): under a modality, in every state its
program ends in.  An update's right-hand sides and a `defined` are not
rewritten: they are read by the interpreter, which a Theory equation does
not preserve (`Proves.updRw` rewrites the former with a refinement).
`Proves.rewrite` (`Calculus/Proves.lean`) rewrites the context's
preconditions and the goal at once (`Hyps.rwEqC`), as today's does.

The kernel unfolds `Fml.rwEqC` and `Hyps.rwEqC` where `Proves.rewrite'`
checks the rewritten sequent (`rfl`), so both are written by the
recursors (Gate G0, conditions 1 and 2), each with its `match` form as the
compiled twin (`Fml.rwEqCM`, `Hyps.rwEqCM`) and a link theorem; the
recursor's clauses are stated by hand (`Fml.rwEqC_not`, …), by `rfl`.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)
open Theory Theory.StValue

variable {C : Contract}

section RwEq

variable {Γ : Ctx}

/-- A closed term denotes its erasure in the global part. -/
theorem Tm.denote_toNil (σ : EState C Γ) : {s : Srt} → (t : Tm C Γ s) → {t₀ : Tm C [] s} →
    t.toNil? = some t₀ → t.denote σ = (t.erase []).denote σ.glob
  | _, .pvV _, _, h | _, .pvP _, _, h | _, .pvS _, _, h | _, .pvI _, _, h | _, .netOf .., _, h =>
    nomatch h
  | _, .app0 _, _, _ => rfl
  | _, .app1 o _ x, _, h => by
    obtain ⟨x₀, hx, -⟩ := Option.map_eq_some_iff.1 h
    show o.denote σ.glob (x.denote σ) = o.denote σ.glob ((x.erase []).denote σ.glob)
    rw [Tm.denote_toNil σ x hx]
  | _, .app2 o x y, _, h => by
    obtain ⟨x₀, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y₀, hy, -⟩ := Option.bind_eq_some_iff.1 h
    show o.denote σ.glob (x.eval σ) (y.eval σ) (x.denote σ) (y.denote σ) =
      o.denote σ.glob ((x.erase []).eval σ.glob) ((y.erase []).eval σ.glob)
        ((x.erase []).denote σ.glob) ((y.erase []).denote σ.glob)
    rw [Tm.denote_toNil σ x hx, Tm.denote_toNil σ y hy, Tm.eval_toNil σ x hx, Tm.eval_toNil σ y hy]
  | _, .app3 o x y z, _, h => by
    obtain ⟨x₀, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y₀, hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z₀, hz, -⟩ := Option.bind_eq_some_iff.1 h
    show o.denote (x.denote σ) (y.denote σ) (z.denote σ) =
      o.denote ((x.erase []).denote σ.glob) ((y.erase []).denote σ.glob) ((z.erase []).denote σ.glob)
    rw [Tm.denote_toNil σ x hx, Tm.denote_toNil σ y hy, Tm.denote_toNil σ z hz]

/-- Today's closed term, at a scope, denotes itself in the global part. -/
theorem Tm.denote_ofClosed (σ : EState C Γ) : {s : Srt} → (q : Surface.Tm C s) →
    {t : Tm C Γ s} → Tm.ofClosed? q = some t → t.denote σ = q.denote σ.glob
  | _, .pvV _, _, h | _, .pvP _, _, h | _, .pvS _, _, h | _, .pvI _, _, h => nomatch h
  | _, .app0 _, _, h => by cases h; rfl
  | _, .app1 o x, _, h => by
    simp only [Tm.ofClosed?] at h
    split at h
    · obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
      show o.denote σ.glob (x'.denote σ) = o.denote σ.glob (x.denote σ.glob)
      rw [Tm.denote_ofClosed σ x hx]
    · cases h
  | _, .app2 o x y, _, h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.denote σ.glob (x'.eval σ) (y'.eval σ) (x'.denote σ) (y'.denote σ) =
      o.denote σ.glob (x.eval σ.glob) (y.eval σ.glob) (x.denote σ.glob) (y.denote σ.glob)
    rw [Tm.denote_ofClosed σ x hx, Tm.denote_ofClosed σ y hy, Tm.eval_ofClosed σ x hx,
      Tm.eval_ofClosed σ y hy]
  | _, .app3 o x y z, _, h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.denote (x'.denote σ) (y'.denote σ) (z'.denote σ) =
      o.denote (x.denote σ.glob) (y.denote σ.glob) (z.denote σ.glob)
    rw [Tm.denote_ofClosed σ x hx, Tm.denote_ofClosed σ y hy, Tm.denote_ofClosed σ z hz]

/-- A side of an equation, made `q.2` where it is a closed term reading
`q.1` on its erasure. -/
def Tm.sideC (q : Solidity.Term C × Solidity.Term C) (t : Tm C Γ .val) : Tm C Γ .val :=
  if (t.toNil?).isSome && t.erase [] == q.1 then (Tm.ofClosed? q.2).getD t else t

/-- `Fml.rwEqC`'s compiled twin. -/
def Fml.rwEqCM (q : Solidity.Term C × Solidity.Term C) : {Γ : Ctx} → Fml C Γ → Fml C Γ
  | _, .tt => .tt
  | _, .eq a b => .eq (a.sideC q) (b.sideC q)
  | _, .defined t => .defined t
  | _, .not φ => .not (Fml.rwEqCM q φ)
  | _, .and φ ψ => .and (Fml.rwEqCM q φ) (Fml.rwEqCM q ψ)
  | _, .imp φ ψ => .imp (Fml.rwEqCM q φ) (Fml.rwEqCM q ψ)
  | _, .upd m U φ => .upd m U (Fml.rwEqCM q φ)
  | _, .modal m P κ φ => .modal m P κ (Fml.rwEqCM q φ)
  | _, .havoc φ => .havoc (Fml.rwEqCM q φ)
  | _, .all x p φ => .all x p (Fml.rwEqCM q φ)
  | _, .bind m x t φ => .bind m x t (Fml.rwEqCM q φ)
  | _, .anon xs φ => .anon xs (Fml.rwEqCM q φ)

/-- Every equation of a formula, rewritten: both sides by `Tm.sideC`,
through every connective, update, quantifier and hidden binder, and into the
postcondition of a modality; by the recursor. -/
@[implemented_by Fml.rwEqCM]
def Fml.rwEqC (q : Solidity.Term C × Solidity.Term C) {Γ : Ctx} (φ : Fml C Γ) : Fml C Γ :=
  Fml.rec (motive := fun Γ _ => Fml C Γ)
    (tt := .tt) (eq := fun a b => .eq (a.sideC q) (b.sideC q)) (defined := fun t => .defined t)
    (not := fun _ ih => .not ih) (and := fun _ _ ihφ ihψ => .and ihφ ihψ)
    (imp := fun _ _ ihφ ihψ => .imp ihφ ihψ) (upd := fun m U _ ih => .upd m U ih)
    (modal := fun m P κ _ ih => .modal m P κ ih) (havoc := fun _ ih => .havoc ih)
    (all := fun x p _ ih => .all x p ih) (bind := fun m x t _ ih => .bind m x t ih)
    (anon := fun xs _ ih => .anon xs ih) φ

section Clauses

variable (q : Solidity.Term C × Solidity.Term C)

theorem Fml.rwEqC_not (φ : Fml C Γ) : (Fml.not φ).rwEqC q = .not (φ.rwEqC q) := rfl
theorem Fml.rwEqC_and (φ ψ : Fml C Γ) : (Fml.and φ ψ).rwEqC q = .and (φ.rwEqC q) (ψ.rwEqC q) :=
  rfl
theorem Fml.rwEqC_imp (φ ψ : Fml C Γ) : (Fml.imp φ ψ).rwEqC q = .imp (φ.rwEqC q) (ψ.rwEqC q) :=
  rfl
theorem Fml.rwEqC_upd {Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    (Fml.upd m U φ).rwEqC q = .upd m U (φ.rwEqC q) := rfl
theorem Fml.rwEqC_modal {Γ₁ Γ₂ : Ctx} (m : Modality) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₂)
    (φ : Fml C Γ₂) : (Fml.modal m P κ φ).rwEqC q = .modal m P κ (φ.rwEqC q) := rfl
theorem Fml.rwEqC_havoc (φ : Fml C Γ) : (Fml.havoc φ).rwEqC q = .havoc (φ.rwEqC q) := rfl
theorem Fml.rwEqC_all (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    (Fml.all x p φ).rwEqC q = .all x p (φ.rwEqC q) := rfl
theorem Fml.rwEqC_bind (m : Modality) (x : Var) (t : LTy) (φ : Fml C (t :: Γ)) :
    (Fml.bind m x t φ).rwEqC q = .bind m x t (φ.rwEqC q) := rfl
theorem Fml.rwEqC_anon (xs : List ((t : LTy) × Idx Γ t)) (φ : Fml C Γ) :
    (Fml.anon xs φ).rwEqC q = .anon xs (φ.rwEqC q) := rfl

/-- The recursor's rewrite is the twin's. -/
theorem Fml.rwEqC_eq_rwEqCM (φ : Fml C Γ) : φ.rwEqC q = φ.rwEqCM q := by
  induction φ with
  | tt | eq | defined => rfl
  | not φ ih | upd m U φ ih | modal m P κ φ ih | havoc φ ih | all x p φ ih | bind m x t φ ih
  | anon xs φ ih => simp only [Fml.rwEqCM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [Fml.rwEqCM, ← ihφ, ← ihψ]; rfl

end Clauses

theorem Tm.sideC_denote {q : Solidity.Term C × Solidity.Term C} (hq : Term.Theq q.1 q.2)
    (σ : EState C Γ) (t : Tm C Γ .val) : Equiv ((t.sideC q).denote σ) (t.denote σ) := by
  unfold Tm.sideC
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Option.isSome_iff_exists, beq_iff_eq] at hc
    obtain ⟨⟨t₀, ht₀⟩, he⟩ := hc
    cases ho : Tm.ofClosed? (Γ := Γ) q.2 with
    | none => exact Equiv.refl _
    | some u =>
      show Equiv (u.denote σ) (t.denote σ)
      rw [Tm.denote_toNil σ t ht₀, he, Tm.denote_ofClosed σ q.2 ho]
      exact (hq σ.glob).symm
  · exact Equiv.refl _

/-- **A formula rewritten by a Theory equation holds where it does.** -/
theorem Fml.rwEqC_holds {q : Solidity.Term C × Solidity.Term C} (hq : Term.Theq q.1 q.2) :
    {Γ : Ctx} → (φ : Fml C Γ) → ∀ σ : State C Γ, (holds σ (φ.rwEqC q) ↔ holds σ φ)
  | _, .tt, _ => Iff.rfl
  | _, .eq a b, σ => by
    show Equiv ((a.sideC q).denote σ.erase) ((b.sideC q).denote σ.erase) ↔
      Equiv (a.denote σ.erase) (b.denote σ.erase)
    have ha := Tm.sideC_denote hq σ.erase a
    have hb := Tm.sideC_denote hq σ.erase b
    exact ⟨fun h => (ha.symm.trans h).trans hb, fun h => (ha.trans h).trans hb.symm⟩
  | _, .defined _, _ => Iff.rfl
  | _, .not φ, σ => not_congr (Fml.rwEqC_holds hq φ σ)
  | _, .and φ ψ, σ => and_congr (Fml.rwEqC_holds hq φ σ) (Fml.rwEqC_holds hq ψ σ)
  | _, .imp φ ψ, σ => imp_congr (Fml.rwEqC_holds hq φ σ) (Fml.rwEqC_holds hq ψ σ)
  | _, .upd m U φ, σ => by
    have ih := Fml.rwEqC_holds hq φ
    simp only [Fml.rwEqC_upd, holds, ih]
  | _, .modal m P κ φ, σ => by
    have ih := Fml.rwEqC_holds hq φ
    simp only [Fml.rwEqC_modal, holds, ih]
  | _, .havoc φ, σ => by
    have ih := Fml.rwEqC_holds hq φ
    simp only [Fml.rwEqC_havoc, holds, ih]
  | _, .all x p φ, σ => by
    have ih := Fml.rwEqC_holds hq φ
    simp only [Fml.rwEqC_all, holds, ih]
  | _, .bind m x t φ, σ => by
    have ih := Fml.rwEqC_holds hq φ
    simp only [Fml.rwEqC_bind, holds, ih]
  | _, .anon xs φ, σ => by
    have ih := Fml.rwEqC_holds hq φ
    simp only [Fml.rwEqC_anon, holds, ih]

end RwEq

end Solidity
