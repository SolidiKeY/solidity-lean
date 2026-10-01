import Solidity.Update
import Solidity.Semantics.Properties
import Solidity.Theory.Bridge.Denote

/-!
# Theory equations as rewrite rules

KeY closes the first-order goal a program leaves by rewriting its terms with
theory taclets — `find(save(storage, p, v), p) ⇝ v` — inside the sequent,
at any step.  Here a taclet needs no soundness proof of its own: an equation
`a ≐ b` reads its sides in the Theory (`Tm.denote`, `holds`), so any two
terms with the same Theory value in every state (`Term.Theq`) may replace
each other in every equation of a sequent.  A law proved in
`Theory/Storage.lean` is such a fact about the terms that denote its sides,
so it is a sound rewrite.  A derivation names the rule instead
(`TermTaclet`, `Calculus/TermTaclets.lean`, applied by `Proves.rewrite`),
and `TermTaclet.sound` is where this module's `Term.Theq` comes in;
`Term.Theq.of_eq` with the `denote_*` lemmas below is how `sol_rw` lifts a
Theory lemma on the spot (`TermTaclet.theory`, `Calculus/TheoryRewrite.lean`).

**Where a rewrite reaches** (`Fml.rwEq`): every total equation, at any depth
— under a connective, behind an update, inside a modality's postcondition,
under a quantifier or `havoc`.  `Term.Theq` quantifies over every state, so
the state a subformula is judged in does not matter.  It does not reach:

* `defined t`, which is read by the interpreter (`eval`), not the Theory —
  two terms with one Theory value can differ in whether they halt;
* an update's right-hand sides or a program, which run in the interpreter
  (`Proves.updRw` reaches the first, for a rewrite that keeps what a run
  returns, `Calculus/UpdateRules.lean`);
* a memory term (`read`, `mlen`, `copyMem`), which `denote`s through `eval`:
  an equality of denotations says nothing about its subterms' evaluations.
  `Tm.rw` replaces such a term as a whole, but never looks inside it.

So the congruence (`Term.rw_denote`) needs only the equivalence of the
replaced term's denotations, and holds up to `StValue.Equiv`, the Theory's
observational equality, through the congruences of `Theory/Observe.lean`.
-/

namespace Solidity

open Semantics SemanticsProperties Theory

variable {C : Contract}

/-! ## Terms equal in the Theory -/

/-- The two terms have the same Theory value in every state: what a law of
the Theory says about the terms that denote its sides. -/
def Term.Theq (t t' : Term C) : Prop := ∀ σ, Theory.StValue.Equiv (t.denote σ) (t'.denote σ)

theorem Term.Theq.refl (t : Term C) : Term.Theq t t := fun _ => StValue.Equiv.refl _

theorem Term.Theq.symm {t t' : Term C} (h : Term.Theq t t') : Term.Theq t' t :=
  fun σ => (h σ).symm

theorem Term.Theq.trans {t₁ t₂ t₃ : Term C} (h₁ : Term.Theq t₁ t₂) (h₂ : Term.Theq t₂ t₃) :
    Term.Theq t₁ t₃ :=
  fun σ => (h₁ σ).trans (h₂ σ)

/-- Terms up to their Theory value: `t ≈ t'` is `Term.Theq t t'`. -/
instance Term.setoid : Setoid (Term C) :=
  ⟨Term.Theq, ⟨Term.Theq.refl, Term.Theq.symm, Term.Theq.trans⟩⟩

/-- Terms whose Theory values are equal are equal in the Theory: how a law of
the Theory, an `=` of its values, becomes a rewrite rule (`sol_rw`,
`Calculus/TheoryRewrite.lean`). -/
theorem Term.Theq.of_eq {t t' : Term C} (h : ∀ σ, t.denote σ = t'.denote σ) : Term.Theq t t' :=
  fun σ => h σ ▸ StValue.Equiv.refl _

/-! ### One constructor's denotation

The arms of `denote` that `sol_rw` unfolds before a Theory law is applied,
one lemma each: the terms it can read back (`Calculus/TheoryRewrite.lean`).
Any other term stays folded, `t.denote σ`, and reads back as itself. -/

theorem Term.denote_lit (σ : State) (v : Value) : (Term.lit v : Term C).denote σ = .prim v := rfl
theorem Term.denote_find (σ : State) (s : STerm C) (p : PTerm C) :
    (Term.find s p).denote σ = StValue.findSt (s.denote σ) (p.denote σ) := rfl
theorem Term.denote_len (σ : State) (s : STerm C) (p : PTerm C) :
    (Term.len s p).denote σ = StValue.findSt (s.denote σ) (p.denote σ ++ [StValue.lengthSeg]) := rfl
theorem STerm.denote_storage (σ : State) : (STerm.storage : STerm C).denote σ = σ.abs := rfl
theorem STerm.denote_save (σ : State) (s : STerm C) (p : PTerm C) (v : SValT C) :
    (STerm.save s p v).denote σ = StValue.copyTo (s.denote σ) (p.denote σ) (v.denote σ) := rfl
theorem STerm.denote_delAt (σ : State) (s : STerm C) (p : PTerm C) :
    (STerm.delAt s p).denote σ = StValue.delAt (s.denote σ) (p.denote σ) := rfl
theorem SValT.denote_val (σ : State) (t : Term C) : (SValT.val t).denote σ = t.denote σ := rfl
theorem SValT.denote_find (σ : State) (s : STerm C) (p : PTerm C) :
    (SValT.find s p).denote σ = StValue.findSt (s.denote σ) (p.denote σ) := rfl
theorem PTerm.denote_root (σ : State) (r : Name) :
    (PTerm.root r : PTerm C).denote σ = [.field r] := rfl
theorem PTerm.denote_field (σ : State) (p : PTerm C) (f : Name) :
    (PTerm.field p f).denote σ = p.denote σ ++ [.field f] := rfl
theorem PTerm.denote_at (σ : State) (p : PTerm C) (i : Term C) :
    (PTerm.at p i).denote σ = p.denote σ ++ [.at (StValue.asInt (i.denote σ))] := rfl

instance : Trans (@Term.Theq C) (@Term.Theq C) (@Term.Theq C) := ⟨Term.Theq.trans⟩

/-! ## Replacing a term -/

/-- `q.2` where the term is `q.1`, and `d` elsewhere. -/
def Term.pick (q : Term C × Term C) (e d : Term C) : Term C := if e = q.1 then q.2 else d

/-- `q.2` where the term is `q.1`, at a value term; any other sort is left as
it is. -/
def Tm.pickAt (q : Term C × Term C) : {s : Srt} → Tm C s → Tm C s → Tm C s
  | .val, e, d => Term.pick q e d
  | .path, _, d | .st, _, d | .sv, _, d | .ident, _, d | .addr, _, d | .mem, _, d | .mv, _, d => d

/-- A memory read (`read`, `mlen`, `copyMem`): its denotation is its
evaluation, so a rewrite never looks inside it. -/
def Op2.opaque : Op2 a b s → Bool
  | .read | .mlen | .copyMem => true
  | _ => false

/-- Every occurrence of `q.1` in a term, replaced by `q.2` — not looking
inside a memory read (`Op2.opaque`), whose denotation is its evaluation. -/
def Tm.rw (q : Term C × Term C) : Tm C s → Tm C s
  | .pvV x => Tm.pickAt q (.pvV x) (.pvV x)
  | .pvP x => .pvP x
  | .pvS x => .pvS x
  | .pvI x => .pvI x
  | .app0 o => Tm.pickAt q (.app0 o) (.app0 o)
  | .app1 o a => Tm.pickAt q (.app1 o a) (.app1 o (a.rw q))
  | .app2 o a b =>
    Tm.pickAt q (.app2 o a b) (if o.opaque then .app2 o a b else .app2 o (a.rw q) (b.rw q))
  | .app3 o a b c => Tm.pickAt q (.app3 o a b c) (.app3 o (a.rw q) (b.rw q) (c.rw q))

/-! ### Replacing an equivalent term keeps the denotation

`denote` reads a subterm's value only through operations that respect
`StValue.Equiv`: `toRes` and the `match`es on a primitive (a value
equivalent to a primitive is it, `Equiv.prim_iff`), the `int` cast of an
index (`Equiv.asInt`), and the storage operations (`Struct.Equiv.copyTo` and
the rest of `Theory/Observe.lean`). -/

/-- Two equivalent values are one primitive, or two nodes. -/
theorem Theory.StValue.Equiv.eq_or_st {v w : StValue} (h : StValue.Equiv v w) :
    v = w ∨ ∃ s t, v = .st s ∧ w = .st t := by
  cases v with
  | prim p => exact Or.inl (StValue.Equiv.prim_iff.1 h.symm).symm
  | st s => cases w with
    | prim p => cases StValue.Equiv.prim_iff.1 h
    | st t => exact Or.inr ⟨s, t, rfl, rfl⟩

/-- Equivalent values are one interpreter result. -/
theorem Theory.StValue.Equiv.toRes {v w : StValue} (h : StValue.Equiv v w) :
    v.toRes = w.toRes := by
  rcases h.eq_or_st with rfl | ⟨s, t, rfl, rfl⟩ <;> rfl

section Denote

variable {q : Term C × Term C} {σ : State}

theorem Term.pick_denote (hd : StValue.Equiv (q.1.denote σ) (q.2.denote σ)) {e d : Term C}
    (h : StValue.Equiv (d.denote σ) (e.denote σ)) :
    StValue.Equiv ((Term.pick q e d).denote σ) (e.denote σ) := by
  unfold Term.pick
  split
  · next he => rw [he]; exact hd.symm
  · exact h

/-- Two denotations of a sort agree in the Theory: `Equiv` for a value or a
storage, equal paths. -/
def Srt.DEquiv : (s : Srt) → s.Den → s.Den → Prop
  | .val => StValue.Equiv
  | .path => Eq
  | .st => Struct.Equiv
  | .sv => StValue.Equiv
  | .ident | .addr | .mem | .mv => fun _ _ => True

theorem Srt.DEquiv.refl : (s : Srt) → (d : s.Den) → Srt.DEquiv s d d
  | .val, _ | .st, _ | .sv, _ => StValue.Equiv.refl _
  | .path, _ => rfl
  | .ident, _ | .addr, _ | .mem, _ | .mv, _ => trivial

theorem Tm.pickAt_denote (hd : StValue.Equiv (q.1.denote σ) (q.2.denote σ)) :
    {s : Srt} → {e d : Tm C s} → Srt.DEquiv s (d.denote σ) (e.denote σ) →
      Srt.DEquiv s ((Tm.pickAt q e d).denote σ) (e.denote σ)
  | .val, _, _, h => Term.pick_denote hd h
  | .path, _, _, h | .st, _, _, h | .sv, _, _, h | .ident, _, _, h | .addr, _, _, h
  | .mem, _, _, h | .mv, _, _, h => h

/-- A unary symbol respects `Equiv` of its argument's denotation. -/
theorem Op1.denote_congr : (o : Op1 a s) → {d d' : a.Den} →
    Srt.DEquiv a d d' → Srt.DEquiv s (o.denote σ d) (o.denote σ d')
  | .unop .., _, _, h => by
    simp only [Srt.DEquiv, Op1.denote] at h ⊢
    rw [h.toRes]
    exact StValue.Equiv.refl _
  | .net, _, _, h => by
    simp only [Srt.DEquiv] at h ⊢
    rcases h.eq_or_st with h | ⟨s, t, hs, ht⟩
    · rw [h]; exact StValue.Equiv.refl _
    · simp only [Op1.denote, hs, ht]; exact StValue.Equiv.refl _
  | .netOf x, _, _, h => by
    simp only [Srt.DEquiv] at h ⊢
    rcases h.eq_or_st with h | ⟨s, t, hs, ht⟩
    · rw [h]; exact StValue.Equiv.refl _
    · simp only [Op1.denote, hs, ht]
      rcases σ.getEnv x with _ | b
      · exact StValue.Equiv.refl _
      · cases b <;> exact StValue.Equiv.refl _
  | .field _, _, _, h | .next, _, _, h => by
    simp only [Srt.DEquiv] at h ⊢; rw [h]
  | .select _, _, _, h => by
    simp only [Srt.DEquiv, Op1.denote] at h ⊢
    exact StValue.Equiv.asStruct (StValue.Equiv.findSt h [_])
  | .sval, _, _, h => h
  | .newArr _, _, _, h => by
    simp only [Srt.DEquiv, Op1.denote] at h ⊢
    rw [h.asInt]
    exact StValue.Equiv.refl _
  | .alloc _, _, _, _ | .mfield _, _, _, _ | .addM _, _, _, _
  | .mval, _, _, _ | .ref, _, _, _ => trivial

/-- A binary symbol that is no memory read respects `Equiv` of its
arguments' denotations, whatever their readings. -/
theorem Op2.denote_congr : (o : Op2 a b s) → o.opaque = false → {ra ra' : a.Ev} →
    {rb rb' : b.Ev} → {da da' : a.Den} → {db db' : b.Den} → Srt.DEquiv a da da' →
    Srt.DEquiv b db db' → Srt.DEquiv s (o.denote σ ra rb da db) (o.denote σ ra' rb' da' db')
  | .binop .., _, _, _, _, _, _, _, _, _, ha, hb => by
    simp only [Srt.DEquiv, Op2.denote] at ha hb ⊢
    rw [ha.toRes, hb.toRes]
    exact StValue.Equiv.refl _
  | .find, _, _, _, _, _, _, _, _, _, hs, hp | .sfind, _, _, _, _, _, _, _, _, _, hs, hp
  | .len, _, _, _, _, _, _, _, _, _, hs, hp => by
    simp only [Srt.DEquiv, Op2.denote] at hs hp ⊢
    rw [hp]
    exact StValue.Equiv.findSt hs _
  | .at, _, _, _, _, _, _, _, _, _, hp, hi => by
    simp only [Srt.DEquiv, Op2.denote] at hp hi ⊢
    rw [hp, hi.asInt]
  | .delAt, _, _, _, _, _, _, _, _, _, hs, hp => by
    simp only [Srt.DEquiv, Op2.denote] at hs hp ⊢
    rw [hp]
    exact Struct.Equiv.delAt hs _
  | .pushSlot _, _, _, _, _, _, _, _, _, _, hs, hp
  | .extend _, _, _, _, _, _, _, _, _, _, hs, hp => by
    simp only [Srt.DEquiv, Op2.denote] at hs hp ⊢
    rw [hp]
    exact Struct.Equiv.pushSlotT _ _ hs _
  | .pop, _, _, _, _, _, _, _, _, _, hs, hp => by
    simp only [Srt.DEquiv, Op2.denote] at hs hp ⊢
    rw [hp]
    exact Struct.Equiv.popT hs _
  | .shrink, _, _, _, _, _, _, _, _, _, hs, hp => by
    simp only [Srt.DEquiv, Op2.denote] at hs hp ⊢
    rw [hp]
    exact Struct.Equiv.shrinkT hs _
  | .iread, _, _, _, _, _, _, _, _, _, _, _ | .copy, _, _, _, _, _, _, _, _, _, _, _
  | .mat, _, _, _, _, _, _, _, _, _, _, _ | .copySt, _, _, _, _, _, _, _, _, _, _, _ => trivial

/-- A ternary symbol respects `Equiv` of its arguments' denotations. -/
theorem Op3.denote_congr : (o : Op3 a b c s) → {da da' : a.Den} → {db db' : b.Den} →
    {dc dc' : c.Den} → Srt.DEquiv a da da' → Srt.DEquiv b db db' → Srt.DEquiv c dc dc' →
    Srt.DEquiv s (o.denote da db dc) (o.denote da' db' dc')
  | .ite, _, _, _, _, _, _, hc, ha, hb => by
    simp only [Srt.DEquiv, Op3.denote] at hc ha hb ⊢
    rcases hc.eq_or_st with h | ⟨s, t, hs, ht⟩
    · rw [h]
      split
      · exact ha
      · exact hb
      · exact StValue.Equiv.refl _
    · simp only [hs, ht]
      exact StValue.Equiv.refl _
  | .save, _, _, _, _, _, _, hs, hp, hv => by
    simp only [Srt.DEquiv, Op3.denote] at hs hp hv ⊢
    rw [hp]
    exact Struct.Equiv.copyTo hs hv _
  | .push, _, _, _, _, _, _, hs, hp, hv => by
    simp only [Srt.DEquiv, Op3.denote] at hs hp hv ⊢
    rw [hp]
    exact Struct.Equiv.pushT hs (StValue.Equiv.stripVal hv) _
  | .write, _, _, _, _, _, _, _, _, _ => trivial

/-- **Replacing an equivalent term keeps the denotation**, up to `Equiv`. -/
theorem Tm.rw_denote (hd : StValue.Equiv (q.1.denote σ) (q.2.denote σ)) :
    (e : Tm C s) → Srt.DEquiv s ((e.rw q).denote σ) (e.denote σ)
  | .pvV _ | .app0 _ => Tm.pickAt_denote hd (Srt.DEquiv.refl _ _)
  | .pvP _ | .pvS _ | .pvI _ => Srt.DEquiv.refl _ _
  | .app1 o a => Tm.pickAt_denote hd (o.denote_congr (a.rw_denote hd))
  | .app2 o a b => Tm.pickAt_denote hd (by
      cases ho : o.opaque
      · simp only [Bool.false_eq_true, ↓reduceIte, Tm.denote]
        exact o.denote_congr ho (a.rw_denote hd) (b.rw_denote hd)
      · simp only [↓reduceIte]
        exact Srt.DEquiv.refl _ _)
  | .app3 o a b c => Tm.pickAt_denote hd
      (o.denote_congr (a.rw_denote hd) (b.rw_denote hd) (c.rw_denote hd))

theorem Term.rw_denote (hd : StValue.Equiv (q.1.denote σ) (q.2.denote σ)) (e : Term C) :
    StValue.Equiv ((e.rw q).denote σ) (e.denote σ) := Tm.rw_denote hd e
theorem PTerm.rw_denote (hd : StValue.Equiv (q.1.denote σ) (q.2.denote σ)) (p : PTerm C) :
    (p.rw q).denote σ = p.denote σ := Tm.rw_denote hd p
theorem STerm.rw_denote (hd : StValue.Equiv (q.1.denote σ) (q.2.denote σ)) (s : STerm C) :
    Struct.Equiv ((s.rw q).denote σ) (s.denote σ) := Tm.rw_denote hd s
theorem SValT.rw_denote (hd : StValue.Equiv (q.1.denote σ) (q.2.denote σ)) (v : SValT C) :
    StValue.Equiv ((v.rw q).denote σ) (v.denote σ) := Tm.rw_denote hd v

end Denote

/-! ## Rewriting a formula -/

/-- Every occurrence of `q.1`, replaced by `q.2` in every total equation of
the formula, at any depth; `defined`, update right-hand sides and programs
are left alone (the module docstring says why). -/
def Fml.rwEq (q : Term C × Term C) : Fml C → Fml C
  | .tt => .tt
  | .eq a b => .eq (a.rw q) (b.rw q)
  | .defined t => .defined t
  | .not φ => .not (φ.rwEq q)
  | .and φ ψ => .and (φ.rwEq q) (ψ.rwEq q)
  | .imp φ ψ => .imp (φ.rwEq q) (ψ.rwEq q)
  | .upd m U φ => .upd m U (φ.rwEq q)
  | .modal m P φ => .modal m P (φ.rwEq q)
  | .havoc φ => .havoc (φ.rwEq q)
  | .all x p φ => .all x p (φ.rwEq q)

/-- **A Theory equation rewrites a formula into an equivalent one**, in every
state: the payoff of reading equations in the Theory. -/
theorem Fml.rwEq_holds {q : Term C × Term C} (h : Term.Theq q.1 q.2) :
    (φ : Fml C) → ∀ σ, (holds σ (φ.rwEq q) ↔ holds σ φ)
  | .tt, _ | .defined _, _ => Iff.rfl
  | .eq a b, σ => by
    have ha : StValue.Equiv ((a.rw q).denote σ) (a.denote σ) := a.rw_denote (h σ)
    have hb : StValue.Equiv ((b.rw q).denote σ) (b.denote σ) := b.rw_denote (h σ)
    exact ⟨fun e => ha.symm.trans (e.trans hb), fun e => ha.trans (e.trans hb.symm)⟩
  | .not φ, σ => by simp only [Fml.rwEq, holds, φ.rwEq_holds h σ]
  | .and φ ψ, σ => by simp only [Fml.rwEq, holds, φ.rwEq_holds h σ, ψ.rwEq_holds h σ]
  | .imp φ ψ, σ => by simp only [Fml.rwEq, holds, φ.rwEq_holds h σ, ψ.rwEq_holds h σ]
  | .upd _ _ φ, _ | .modal _ _ φ, _ | .havoc φ, _ | .all _ _ φ, _ => by
    simp only [Fml.rwEq, holds, φ.rwEq_holds h]

end Solidity
