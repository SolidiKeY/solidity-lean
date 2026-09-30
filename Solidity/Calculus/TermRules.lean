import Solidity.Update
import Solidity.Semantics.Properties
import Solidity.Theory.Bridge.Denote

/-!
# Theory equations as rewrite rules

KeY closes the first-order goal a program leaves by rewriting its terms with
theory taclets — `find(save(storage, p, v), p) ⇝ v` — inside the sequent,
at any step.  Here a taclet needs no soundness proof of its own: an equation
`a ≐ b` reads its sides in the Theory (`Term.denote`, `holds`), so any two
terms with the same Theory value in every state (`Term.Theq`) may replace
each other in every equation of a sequent.  A law proved in
`Theory/Storage.lean` is such a fact about the terms that denote its sides,
so it is a rewrite rule for free; `Proves.theoryRw` (`Calculus/Logic.lean`)
applies one, and `Term.Theq.of_eq` with the `denote_*` lemmas below is how
`sol_rw` lifts a named Theory lemma (`Calculus/TheoryRewrite.lean`).

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
  `Term.rw` replaces such a term as a whole, but never looks inside it.

So the congruence (`Term.rw_denote`) needs only the equivalence of the
replaced term's denotations, and holds up to `StValue.Equiv`, the Theory's
observational equality, through the congruences of `Theory/Observe.lean`.
-/

namespace Solidity

open Semantics SemanticsProperties Theory

variable {C : Contract}

deriving instance DecidableEq for Term, PTerm, STerm, SValT, ITerm, MAddr, MTerm, MValT

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

mutual

/-- Every occurrence of `q.1` in a term, replaced by `q.2` — not looking
inside a memory term (`read`, `mlen`), whose denotation is its evaluation. -/
def Term.rw (q : Term C × Term C) : Term C → Term C
  | .lit v => Term.pick q (.lit v) (.lit v)
  | .pv x => Term.pick q (.pv x) (.pv x)
  | .binop op p a b => Term.pick q (.binop op p a b) (.binop op p (a.rw q) (b.rw q))
  | .unop op p a => Term.pick q (.unop op p a) (.unop op p (a.rw q))
  | .find s p => Term.pick q (.find s p) (.find (s.rw q) (p.rw q))
  | .len s p => Term.pick q (.len s p) (.len (s.rw q) (p.rw q))
  | .read m a => Term.pick q (.read m a) (.read m a)
  | .ite c a b => Term.pick q (.ite c a b) (.ite (c.rw q) (a.rw q) (b.rw q))
  | .mlen m i => Term.pick q (.mlen m i) (.mlen m i)
  | .env k => Term.pick q (.env k) (.env k)
  | .net a => Term.pick q (.net a) (.net (a.rw q))
  | .netOf x a => Term.pick q (.netOf x a) (.netOf x (a.rw q))

def PTerm.rw (q : Term C × Term C) : PTerm C → PTerm C
  | .root r => .root r
  | .pv x => .pv x
  | .field p f => .field (p.rw q) f
  | .at p i => .at (p.rw q) (i.rw q)
  | .next p => .next (p.rw q)

def STerm.rw (q : Term C × Term C) : STerm C → STerm C
  | .storage => .storage
  | .pv x => .pv x
  | .save s p v => .save (s.rw q) (p.rw q) (v.rw q)
  | .delAt s p => .delAt (s.rw q) (p.rw q)
  | .push s p v => .push (s.rw q) (p.rw q) (v.rw q)
  | .pushSlot s p E => .pushSlot (s.rw q) (p.rw q) E
  | .pop s p => .pop (s.rw q) (p.rw q)
  | .shrink s p => .shrink (s.rw q) (p.rw q)
  | .extend s p E => .extend (s.rw q) (p.rw q) E

/-- A `copyMem` is left whole: it denotes through `eval`. -/
def SValT.rw (q : Term C × Term C) : SValT C → SValT C
  | .val e => .val (e.rw q)
  | .find s p => .find (s.rw q) (p.rw q)
  | .copyMem m i => .copyMem m i
  | .newArr R n => .newArr R (n.rw q)

end

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

mutual

theorem Term.rw_denote (hd : StValue.Equiv (q.1.denote σ) (q.2.denote σ)) :
    (e : Term C) → StValue.Equiv ((e.rw q).denote σ) (e.denote σ)
  | .lit _ | .pv _ | .env _ | .read _ _ | .mlen _ _ => Term.pick_denote hd (StValue.Equiv.refl _)
  | .binop _ _ a b => Term.pick_denote hd (by
      simp only [Term.denote, (a.rw_denote hd).toRes, (b.rw_denote hd).toRes]
      exact StValue.Equiv.refl _)
  | .unop _ _ a => Term.pick_denote hd (by
      simp only [Term.denote, (a.rw_denote hd).toRes]
      exact StValue.Equiv.refl _)
  | .net a => Term.pick_denote hd (by
      rcases (a.rw_denote hd).eq_or_st with h | ⟨s, t, hs, ht⟩
      · simp only [Term.denote, h]
        exact StValue.Equiv.refl _
      · simp only [Term.denote, hs, ht]
        exact StValue.Equiv.refl _)
  | .netOf x a => Term.pick_denote hd (by
      rcases (a.rw_denote hd).eq_or_st with h | ⟨s, t, hs, ht⟩
      · simp only [Term.denote, h]
        exact StValue.Equiv.refl _
      · simp only [Term.denote, hs, ht]
        rcases σ.getEnv x with _ | b
        · exact StValue.Equiv.refl _
        · cases b <;> exact StValue.Equiv.refl _)
  | .find s p => Term.pick_denote hd (by
      simp only [Term.denote, p.rw_denote hd]
      exact StValue.Equiv.findSt (s.rw_denote hd) _)
  | .len s p => Term.pick_denote hd (by
      simp only [Term.denote, p.rw_denote hd]
      exact StValue.Equiv.findSt (s.rw_denote hd) _)
  | .ite c a b => Term.pick_denote hd (by
      rcases (c.rw_denote hd).eq_or_st with h | ⟨s, t, hs, ht⟩
      · simp only [Term.denote, h]
        split
        · exact a.rw_denote hd
        · exact b.rw_denote hd
        · exact StValue.Equiv.refl _
      · simp only [Term.denote, hs, ht]
        exact StValue.Equiv.refl _)

theorem PTerm.rw_denote (hd : StValue.Equiv (q.1.denote σ) (q.2.denote σ)) :
    (p : PTerm C) → (p.rw q).denote σ = p.denote σ
  | .root _ | .pv _ => rfl
  | .field p _ => by simp only [PTerm.rw, PTerm.denote, p.rw_denote hd]
  | .at p i => by simp only [PTerm.rw, PTerm.denote, p.rw_denote hd, (i.rw_denote hd).asInt]
  | .next p => by simp only [PTerm.rw, PTerm.denote, p.rw_denote hd]

theorem STerm.rw_denote (hd : StValue.Equiv (q.1.denote σ) (q.2.denote σ)) :
    (s : STerm C) → Struct.Equiv ((s.rw q).denote σ) (s.denote σ)
  | .storage | .pv _ => StValue.Equiv.refl _
  | .save s p v => by
    simp only [STerm.rw, STerm.denote, p.rw_denote hd]
    exact Struct.Equiv.copyTo (s.rw_denote hd) (v.rw_denote hd) _
  | .delAt s p => by
    simp only [STerm.rw, STerm.denote, p.rw_denote hd]
    exact Struct.Equiv.delAt (s.rw_denote hd) _
  | .push s p v => by
    simp only [STerm.rw, STerm.denote, p.rw_denote hd]
    exact Struct.Equiv.pushT (s.rw_denote hd) (StValue.Equiv.stripVal (v.rw_denote hd)) _
  | .pushSlot s p _ | .extend s p _ => by
    simp only [STerm.rw, STerm.denote, p.rw_denote hd]
    exact Struct.Equiv.pushSlotT _ _ (s.rw_denote hd) _
  | .pop s p => by
    simp only [STerm.rw, STerm.denote, p.rw_denote hd]
    exact Struct.Equiv.popT (s.rw_denote hd) _
  | .shrink s p => by
    simp only [STerm.rw, STerm.denote, p.rw_denote hd]
    exact Struct.Equiv.shrinkT (s.rw_denote hd) _

theorem SValT.rw_denote (hd : StValue.Equiv (q.1.denote σ) (q.2.denote σ)) :
    (v : SValT C) → StValue.Equiv ((v.rw q).denote σ) (v.denote σ)
  | .val e => e.rw_denote hd
  | .find s p => by
    simp only [SValT.rw, SValT.denote, p.rw_denote hd]
    exact StValue.Equiv.findSt (s.rw_denote hd) _
  | .copyMem _ _ => StValue.Equiv.refl _
  | .newArr _ n => by
    simp only [SValT.rw, SValT.denote, (n.rw_denote hd).asInt]
    exact StValue.Equiv.refl _

end

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
