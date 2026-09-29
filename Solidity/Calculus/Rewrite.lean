import Solidity.Calculus.Close
import Solidity.Calculus.UpdateRules

/-!
# Rewriting a term anywhere in a sequent

KeY closes the first-order goal a program leaves by rewriting its terms:
`{u}find(save(storage, p, 42), p) ⇝ 42` is a taclet, applied inside the
sequent, wherever the term is.  This module is that step for the calculus:
one rule, `Proves.rewrite`, that replaces a term `t` by `t'` and is sound for
every equation `t ≐ t'` given with it.  The equations are theorems
(`Hyp.EqUnder`), proved once each, as a KeY taclet is justified once; the
calculus does not change when one is added.

**Where the equation has to hold.**  A term here is a call of the
interpreter and can halt: `find(storage, alice.age)` is stuck in a state
without `alice`, so `find(save(storage, p, 42), p) ≐ 42` is no equation
between terms.  It does hold in every state a context *leads to*: behind
`{storage := save(storage, alice.age, 42)}` the read is `42`.  So an
equation is stated against a context `Γ₀` (`Hyp.Reaches Γ₀ σ τ`: running
the context from `σ` ends in `τ`, its preconditions holding on the way),
and `Proves.rewrite n` rewrites in the sequent `Γ₀ ++ Γ₁ ⟹ φ` whose first
`n` hypotheses are `Γ₀`.  What it rewrites is every occurrence evaluated in
the state `Γ₀` leaves (`Hyp.rwHere`): the right-hand sides of the next
update, the preconditions up to it, or the goal when no update is left —
never behind a further update, a modality or a quantifier, whose state is
another.

The updates themselves follow KeY too: `Proves.mergeStorage` is
`sequentialToParallel` over a storage write (`Proves.merge` takes only
updates of locals), and `Proves.rewriteUpd` rewrites the right-hand sides of
a box update under an equation that holds wherever the update runs
(`Hyp.EqRun`) — where it halts, the box holds anyway.  That is where a read
of the write is rewritten: KeY would apply the update to the formula and
drop it (`applyOnRigid`), but a dropped update that could halt takes with it
the fact that it did not, and the goal left is false where it would have.

The rules are proved through `close`, as `Proves.merge` is, so they apply to
a sequent with no modality left: the steps after symbolic execution.
-/

namespace Solidity

open Semantics SemanticsProperties

deriving instance DecidableEq for Term, PTerm, STerm, SValT, ITerm, MAddr, MTerm, MValT

variable {C : Contract}

/-! ## Replacing a term -/

/-- `q.2` where the term is `q.1`, and `d` elsewhere. -/
def Term.pick (q : Term C × Term C) (e d : Term C) : Term C := if e = q.1 then q.2 else d

mutual

/-- Every occurrence of `t` in a term, replaced by `t'`. -/
def Term.rw (q : Term C × Term C) : Term C → Term C
  | .lit v => Term.pick q (.lit v) (.lit v)
  | .pv x => Term.pick q (.pv x) (.pv x)
  | .binop op p a b => Term.pick q (.binop op p a b) (.binop op p (a.rw q) (b.rw q))
  | .unop op p a => Term.pick q (.unop op p a) (.unop op p (a.rw q))
  | .find s p => Term.pick q (.find s p) (.find (s.rw q) (p.rw q))
  | .len s p => Term.pick q (.len s p) (.len (s.rw q) (p.rw q))
  | .read m a => Term.pick q (.read m a) (.read (m.rw q) (a.rw q))
  | .ite c a b => Term.pick q (.ite c a b) (.ite (c.rw q) (a.rw q) (b.rw q))
  | .mlen m i => Term.pick q (.mlen m i) (.mlen (m.rw q) (i.rw q))
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

def SValT.rw (q : Term C × Term C) : SValT C → SValT C
  | .val e => .val (e.rw q)
  | .find s p => .find (s.rw q) (p.rw q)
  | .copyMem m i => .copyMem (m.rw q) (i.rw q)
  | .newArr R n => .newArr R (n.rw q)

def ITerm.rw (q : Term C × Term C) : ITerm C → ITerm C
  | .pv x => .pv x
  | .read m a => .read (m.rw q) (a.rw q)
  | .alloc m R => .alloc (m.rw q) R
  | .copy m v => .copy (m.rw q) (v.rw q)

def MAddr.rw (q : Term C × Term C) : MAddr C → MAddr C
  | .field i f => .field (i.rw q) f
  | .at i k => .at (i.rw q) (k.rw q)

def MTerm.rw (q : Term C × Term C) : MTerm C → MTerm C
  | .memory => .memory
  | .write m a v => .write (m.rw q) (a.rw q) (v.rw q)
  | .addM m R => .addM (m.rw q) R
  | .copySt m v => .copySt (m.rw q) (v.rw q)

def MValT.rw (q : Term C × Term C) : MValT C → MValT C
  | .val e => .val (e.rw q)
  | .ref i => .ref (i.rw q)

end

def UpdElem.rw (q : Term C × Term C) : UpdElem C → UpdElem C
  | .val x e => .val x (e.rw q)
  | .path x p => .path x (p.rw q)
  | .mref x i => .mref x (i.rw q)
  | .storage s => .storage (s.rw q)
  | .store x s => .store x (s.rw q)
  | .memory m => .memory (m.rw q)
  | .transfer r a => .transfer (r.rw q) (a.rw q)
  | .saveNet x => .saveNet x
  | .book a => .book (a.rw q)

def Upd.rw (q : Term C × Term C) (U : Upd C) : Upd C := U.map (·.rw q)

/-! ### Replacing an equal term changes no evaluation -/

section Eval

variable {q : Term C × Term C} {σ : State}

theorem Term.pick_eval (h : q.1.eval σ = q.2.eval σ) {e d : Term C} (hd : d.eval σ = e.eval σ) :
    (Term.pick q e d).eval σ = e.eval σ := by
  unfold Term.pick
  split
  · next he => rw [he, h]
  · exact hd

mutual

theorem Term.rw_eval (h : q.1.eval σ = q.2.eval σ) : (e : Term C) → (e.rw q).eval σ = e.eval σ
  | .lit _ => Term.pick_eval h rfl
  | .pv _ => Term.pick_eval h rfl
  | .binop _ _ a b => Term.pick_eval h (by simp only [Term.eval, a.rw_eval h, b.rw_eval h])
  | .unop _ _ a => Term.pick_eval h (by simp only [Term.eval, a.rw_eval h])
  | .find s p => Term.pick_eval h (by simp only [Term.eval, s.rw_eval h, p.rw_eval h])
  | .len s p => Term.pick_eval h (by simp only [Term.eval, s.rw_eval h, p.rw_eval h])
  | .read m a => Term.pick_eval h (by simp only [Term.eval, m.rw_eval h, a.rw_eval h])
  | .ite c a b => Term.pick_eval h (by simp only [Term.eval, c.rw_eval h, a.rw_eval h, b.rw_eval h])
  | .mlen m i => Term.pick_eval h (by simp only [Term.eval, m.rw_eval h, i.rw_eval h])
  | .env _ => Term.pick_eval h rfl
  | .net a => Term.pick_eval h (by simp only [Term.eval, a.rw_eval h])
  | .netOf _ a => Term.pick_eval h (by simp only [Term.eval, a.rw_eval h])

theorem PTerm.rw_eval (h : q.1.eval σ = q.2.eval σ) : (p : PTerm C) → (p.rw q).eval σ = p.eval σ
  | .root _ | .pv _ => rfl
  | .field p _ => by simp only [PTerm.rw, PTerm.eval, p.rw_eval h]
  | .at p i => by simp only [PTerm.rw, PTerm.eval, p.rw_eval h, i.rw_eval h]
  | .next p => by simp only [PTerm.rw, PTerm.eval, p.rw_eval h]

theorem STerm.rw_eval (h : q.1.eval σ = q.2.eval σ) : (s : STerm C) → (s.rw q).eval σ = s.eval σ
  | .storage | .pv _ => rfl
  | .save s p v => by simp only [STerm.rw, STerm.eval, s.rw_eval h, p.rw_eval h, v.rw_eval h]
  | .delAt s p => by simp only [STerm.rw, STerm.eval, s.rw_eval h, p.rw_eval h]
  | .push s p v => by simp only [STerm.rw, STerm.eval, s.rw_eval h, p.rw_eval h, v.rw_eval h]
  | .pushSlot s p _ => by simp only [STerm.rw, STerm.eval, s.rw_eval h, p.rw_eval h]
  | .pop s p => by simp only [STerm.rw, STerm.eval, s.rw_eval h, p.rw_eval h]
  | .shrink s p => by simp only [STerm.rw, STerm.eval, s.rw_eval h, p.rw_eval h]
  | .extend s p _ => by simp only [STerm.rw, STerm.eval, s.rw_eval h, p.rw_eval h]

theorem SValT.rw_eval (h : q.1.eval σ = q.2.eval σ) : (v : SValT C) → (v.rw q).eval σ = v.eval σ
  | .val e => by simp only [SValT.rw, SValT.eval, e.rw_eval h]
  | .find s p => by simp only [SValT.rw, SValT.eval, s.rw_eval h, p.rw_eval h]
  | .copyMem m i => by simp only [SValT.rw, SValT.eval, m.rw_eval h, i.rw_eval h]
  | .newArr _ n => by simp only [SValT.rw, SValT.eval, n.rw_eval h]

theorem ITerm.rw_eval (h : q.1.eval σ = q.2.eval σ) : (i : ITerm C) → (i.rw q).eval σ = i.eval σ
  | .pv _ => rfl
  | .read m a => by simp only [ITerm.rw, ITerm.eval, m.rw_eval h, a.rw_eval h]
  | .alloc m _ => by simp only [ITerm.rw, ITerm.eval, m.rw_eval h]
  | .copy m v => by simp only [ITerm.rw, ITerm.eval, m.rw_eval h, v.rw_eval h]

theorem MAddr.rw_eval (h : q.1.eval σ = q.2.eval σ) : (a : MAddr C) → (a.rw q).eval σ = a.eval σ
  | .field i _ => by simp only [MAddr.rw, MAddr.eval, i.rw_eval h]
  | .at i k => by simp only [MAddr.rw, MAddr.eval, i.rw_eval h, k.rw_eval h]

theorem MTerm.rw_eval (h : q.1.eval σ = q.2.eval σ) : (m : MTerm C) → (m.rw q).eval σ = m.eval σ
  | .memory => rfl
  | .write m a v => by simp only [MTerm.rw, MTerm.eval, m.rw_eval h, a.rw_eval h, v.rw_eval h]
  | .addM m _ => by simp only [MTerm.rw, MTerm.eval, m.rw_eval h]
  | .copySt m v => by simp only [MTerm.rw, MTerm.eval, m.rw_eval h, v.rw_eval h]

theorem MValT.rw_eval (h : q.1.eval σ = q.2.eval σ) : (v : MValT C) → (v.rw q).eval σ = v.eval σ
  | .val e => by simp only [MValT.rw, MValT.eval, e.rw_eval h]
  | .ref i => by simp only [MValT.rw, MValT.eval, i.rw_eval h]

end

theorem UpdElem.rw_write (h : q.1.eval σ = q.2.eval σ) (τ : State) :
    (e : UpdElem C) → (e.rw q).write σ τ = e.write σ τ
  | .val _ e => by simp only [UpdElem.rw, UpdElem.write, e.rw_eval h]
  | .path _ p => by simp only [UpdElem.rw, UpdElem.write, p.rw_eval h]
  | .mref _ i => by simp only [UpdElem.rw, UpdElem.write, i.rw_eval h]
  | .storage s => by simp only [UpdElem.rw, UpdElem.write, s.rw_eval h]
  | .store _ s => by simp only [UpdElem.rw, UpdElem.write, s.rw_eval h]
  | .memory m => by simp only [UpdElem.rw, UpdElem.write, m.rw_eval h]
  | .transfer r a => by simp only [UpdElem.rw, UpdElem.write, r.rw_eval h, a.rw_eval h]
  | .saveNet _ => rfl
  | .book a => by simp only [UpdElem.rw, UpdElem.write, a.rw_eval h]

theorem Upd.rw_foldl (h : q.1.eval σ = q.2.eval σ) : (U : Upd C) → ∀ τ,
    (U.rw q).foldlM (fun ρ e => e.write σ ρ) τ = U.foldlM (fun ρ e => e.write σ ρ) τ
  | [], _ => rfl
  | e :: U, τ => by
    simp only [Upd.rw, List.map_cons, List.foldlM_cons, UpdElem.rw_write h]
    congr 1
    funext ρ
    exact Upd.rw_foldl h U ρ

/-- An update whose right-hand sides read an equal term runs alike. -/
theorem Upd.rw_apply (h : q.1.eval σ = q.2.eval σ) (U : Upd C) : (U.rw q).apply σ = U.apply σ :=
  Upd.rw_foldl h U σ

end Eval

/-! ## Rewriting in the current state

A formula's terms are read in the state it is judged in, except behind an
update, a modality or a quantifier, which judge what follows in another
state.  `rwHere` rewrites the first kind and leaves the second alone; the
right-hand sides of an update are read before it, so they are rewritten. -/

def Fml.rwHere (q : Term C × Term C) : Fml C → Fml C
  | .eq a b => .eq (a.rw q) (b.rw q)
  | .not φ => .not (φ.rwHere q)
  | .and φ ψ => .and (φ.rwHere q) (ψ.rwHere q)
  | .imp φ ψ => .imp (φ.rwHere q) (ψ.rwHere q)
  | .upd m U φ => .upd m (U.rw q) φ
  | φ => φ

theorem Fml.rwHere_holds {q : Term C × Term C} {σ : State} (h : q.1.eval σ = q.2.eval σ) :
    (φ : Fml C) → (holds σ (φ.rwHere q) ↔ holds σ φ)
  | .tt => Iff.rfl
  | .eq a b => by simp only [Fml.rwHere, holds, a.rw_eval h, b.rw_eval h]
  | .not φ => by simp only [Fml.rwHere, holds, φ.rwHere_holds h]
  | .and φ ψ => by simp only [Fml.rwHere, holds, φ.rwHere_holds h, ψ.rwHere_holds h]
  | .imp φ ψ => by simp only [Fml.rwHere, holds, φ.rwHere_holds h, ψ.rwHere_holds h]
  | .upd m U φ => by simp only [Fml.rwHere, holds, Upd.rw_apply h]
  | .modal .. | .havoc _ | .all .. => Iff.rfl

/-- The sequent `Γ ⟹ φ` rewritten in the state it starts in: the
preconditions up to the first update, that update's right-hand sides, and
the goal if no update or `havoc` comes first. -/
def Hyp.rwHere (q : Term C × Term C) : List (Hyp C) → Fml C → List (Hyp C) × Fml C
  | [], φ => ([], φ.rwHere q)
  | .pre a :: Γ, φ => (.pre (a.rwHere q) :: (Hyp.rwHere q Γ φ).1, (Hyp.rwHere q Γ φ).2)
  | .upd m U :: Γ, φ => (.upd m (U.rw q) :: Γ, φ)
  | .havoc :: Γ, φ => (.havoc :: Γ, φ)

theorem Hyp.rwHere_holds {q : Term C × Term C} {σ : State} (h : q.1.eval σ = q.2.eval σ) :
    (Γ : List (Hyp C)) → (φ : Fml C) →
      (holds σ (Hyp.wrap (Hyp.rwHere q Γ φ).1 (Hyp.rwHere q Γ φ).2) ↔ holds σ (Hyp.wrap Γ φ))
  | [], φ => φ.rwHere_holds h
  | .pre a :: Γ, φ => by
    simp only [Hyp.rwHere, Hyp.wrap, holds, a.rwHere_holds h, Hyp.rwHere_holds h Γ φ]
  | .upd m U :: Γ, φ => by simp only [Hyp.rwHere, Hyp.wrap, holds, Upd.rw_apply h]
  | .havoc :: _, _ => Iff.rfl

/-! ## The states a context leads to -/

/-- `Reaches Γ σ τ`: running the context `Γ` from `σ` ends in `τ` — every
update returns, every precondition holds where it is met, and a `havoc`
leaves any storage, ledger and funds. -/
def Hyp.Reaches : List (Hyp C) → State → State → Prop
  | [], σ, τ => τ = σ
  | .pre a :: Γ, σ, τ => holds σ a ∧ Hyp.Reaches Γ σ τ
  | .upd _ U :: Γ, σ, τ => ∃ ρ, U.apply σ = .ok ρ ∧ Hyp.Reaches Γ ρ τ
  | .havoc :: Γ, σ, τ => ∃ st nt bal, Hyp.Reaches Γ (σ.havoc st nt bal) τ

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
  | .havoc :: Γ, σ, h => fun hA st nt bal =>
    Hyp.wrap_reach Γ _ (fun τ hr => h τ ⟨st, nt, bal, hr⟩) (hA st nt bal)

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
  | .havoc :: Γ, Δ, _, τ, ⟨st, nt, bal, h⟩ =>
    let ⟨ρ, h₁, h₂⟩ := Hyp.reaches_append Γ Δ _ τ h
    ⟨ρ, ⟨st, nt, bal, h₁⟩, h₂⟩

/-! ## Equations, and the rule -/

/-- `t ≐ t'` under `Γ`: the two terms read alike in every state `Γ` leads
to.  A rewrite rule is a theorem of this form. -/
def Hyp.EqUnder (Γ : List (Hyp C)) (t t' : Term C) : Prop :=
  ∀ σ τ, Hyp.Reaches Γ σ τ → t.eval τ = t'.eval τ

/-- A state a context leads to is one its last hypothesis leads to. -/
theorem Hyp.reaches_last {x : Hyp C} : (Γ : List (Hyp C)) → Γ.getLast? = some x →
    ∀ σ τ, Hyp.Reaches Γ σ τ → ∃ ρ, Hyp.Reaches [x] ρ τ
  | [], h, _, _, _ => by cases h
  | [y], h, σ, _, hr => by
    have hy : y = x := Option.some.inj h
    subst hy
    exact ⟨σ, hr⟩
  | y :: z :: Γ, h, σ, τ, hr =>
    let ⟨ρ, _, h₂⟩ := Hyp.reaches_append [y] (z :: Γ) σ τ hr
    Hyp.reaches_last (z :: Γ) h ρ τ h₂

/-- An equation behind the last hypothesis holds behind the whole context. -/
theorem Hyp.EqUnder.last {Γ : List (Hyp C)} {x : Hyp C} {t t' : Term C}
    (e : Hyp.EqUnder [x] t t') (hx : Γ.getLast? = some x) : Hyp.EqUnder Γ t t' := by
  intro σ τ hr
  obtain ⟨ρ, h⟩ := Hyp.reaches_last Γ hx σ τ hr
  exact e ρ τ h

/-- **Rewriting.**  In `Γ ⟹ φ`, the occurrences of `t` read in the state
the first `n` hypotheses lead to become `t'`, given `t ≐ t'` there. -/
theorem Proves.rewrite {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} {t t' : Term C} (n : Nat)
    (e : Hyp.EqUnder (Γ.take n) t t')
    (h : Proves R (Γ.take n ++ (Hyp.rwHere (t, t') (Γ.drop n) φ).1)
      (Hyp.rwHere (t, t') (Γ.drop n) φ).2)
    (hφ : (Hyp.wrap Γ φ).modalFree = true := by first | rfl | decide) :
    Proves R Γ φ :=
  .close (fun σ => by
    have hs := h.sound σ
    rw [Hyp.wrap_append] at hs
    rw [← List.take_append_drop n Γ, Hyp.wrap_append]
    exact Hyp.wrap_reach (Γ.take n) σ
      (fun τ hr hτ => (Hyp.rwHere_holds (q := (t, t')) (e σ τ hr) _ _).1 hτ) hs) hφ

/-! ## Rewrite rules

Each is a theorem `t ≐ t'` behind a context whose last hypothesis has a
given shape; the shape is checked by `rfl` against the sequent, so
`refine Proves.rewrite n (Hyp.EqUnder.findOnSave) ?_` finds its instance
the way a taclet's `\find` does. -/

/-- A path of state variables and members names the same slot in every state. -/
theorem PTerm.total_eval_eq (σ τ : State) : {p : PTerm C} → p.total = true → p.eval σ = p.eval τ
  | .root _, _ => rfl
  | .field p _, h => by simp only [PTerm.eval, PTerm.total_eval_eq σ τ (p := p) h]

/-- **`findOnSave`**: behind `{storage := save(storage, p, v)}`, `find(storage, p)` is `v`. -/
theorem Hyp.EqUnder.findOnSave {Γ : List (Hyp C)} {m : Modality} {p : PTerm C} {v : Value}
    (hx : Γ.getLast? = some (.upd m [.storage (.save .storage p (.val (.lit v)))]) := by rfl)
    (hp : p.total = true := by rfl) :
    Hyp.EqUnder Γ (.find .storage p) (.lit v) := by
  refine Hyp.EqUnder.last (fun σ τ hr => ?_) hx
  obtain ⟨ρ, hU, hτ⟩ := hr
  cases hτ
  obtain ⟨⟨r, segs⟩, hpe⟩ := PTerm.total_eval σ hp
  simp only [Upd.apply, List.foldlM_cons, List.foldlM_nil, Close.UpdElem.write_storage,
    Close.STerm.eval_save, Close.Term.eval_lit, Close.STerm.eval_storage, hpe, Close.ok_bind,
    Close.pure_eq_ok] at hU
  cases hs : σ.saveStorage r segs v.toSVal with
  | error _ => rw [hs] at hU; cases hU
  | ok τ' =>
    rw [hs] at hU
    cases hU
    rw [Close.Term.eval_find, Close.STerm.eval_storage, Close.ok_bind,
      PTerm.total_eval_eq _ σ hp, hpe, Close.ok_bind, Close.findStorage_mk,
      State.findStorage_saveStorage_same hs, Close.ok_bind, Close.asValue_toSVal,
      Close.Term.eval_lit]

/-- A run that returned ran its first step. -/
theorem Except.bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A list whose last element is `x` ends in `x`. -/
theorem List.eq_append_of_getLast? {α : Type} : {l : List α} → {x : α} → l.getLast? = some x →
    ∃ l', l = l' ++ [x]
  | [], _, h => by cases h
  | [a], x, h => by
    have ha : a = x := Option.some.inj h
    exact ⟨[], by rw [ha]; rfl⟩
  | a :: b :: l, _, h =>
    let ⟨l', e⟩ := List.eq_append_of_getLast? (l := b :: l) h
    ⟨a :: l', by rw [e]; rfl⟩

/-- **`applyOnPV`**: behind `{… ‖ x := v}`, `x` is `v` — the last element
of a parallel update is the write that stands. -/
theorem Hyp.EqUnder.applyOnPV {Γ : List (Hyp C)} {m : Modality} {U : Upd C} {x : Var} {v : Value}
    (hx : Γ.getLast? = some (.upd m U) := by rfl)
    (hU : U.getLast? = some (.val x (.lit v)) := by rfl) :
    Hyp.EqUnder Γ (.pv x) (.lit v) := by
  refine Hyp.EqUnder.last (fun σ τ hr => ?_) hx
  obtain ⟨ρ, hρ, hτ⟩ := hr
  cases hτ
  obtain ⟨U₀, rfl⟩ := List.eq_append_of_getLast? hU
  rw [Upd.apply, List.foldlM_append] at hρ
  obtain ⟨ρ₀, -, hρ⟩ := Except.bind_eq_ok hρ
  simp only [List.foldlM_cons, List.foldlM_nil, Close.UpdElem.write_val, Close.Term.eval_lit,
    Close.ok_bind] at hρ
  cases hρ
  rw [Close.Term.eval_pv, State.getEnv_setEnv_self, Close.ok_bind, Close.bindingVal_val,
    Close.Term.eval_lit]

/-! ## Closing -/

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
  | .havoc :: Γ, hb, σ, h => fun st nt bal =>
    Hyp.wrap_of_reaches Γ hb _ (fun τ hr => h τ ⟨st, nt, bal, hr⟩)

/-- **`eqClose`**: `v = v`, behind a context with no diamond. -/
theorem Proves.eqClose {R : RuleSet} {Γ : List (Hyp C)} {v : Value}
    (hb : Hyp.boxOnly Γ = true := by rfl)
    (hφ : (Hyp.wrap Γ (.eq (.lit v) (.lit v))).modalFree = true := by first | rfl | decide) :
    Proves R Γ (.eq (.lit v) (.lit v)) :=
  .close (fun σ => Hyp.wrap_of_reaches Γ hb σ (fun _ _ => rfl)) hφ

/-! ## Updates in parallel: `sequentialToParallel` over a storage write

`Proves.merge` joins `{U}{V}` only when `U` writes locals.  A storage write
`{storage := s}` joins too, KeY's `{storage := s ‖ {storage := s}V}`: `V`'s
right-hand sides read `storage` after the write, so `s` is substituted for
`storage` in them (`withSt`), and they are read before it.  The substitution
is exact only where every storage read is a `storage` term: a path through
an index (`a[i]`) or one past the end (`a[a.length]`) checks the array in
the state it is read in, which is not a term (`stExplicit`).

A storage term changes the storage and nothing else (`State.Keeps`), which
is what lets the substituted term read the post-state's locals, heap and
funds off the pre-state. -/

/-- `τ` is `σ` with another storage. -/
def Semantics.State.Keeps (σ τ : State) : Prop := { σ with storage := τ.storage } = τ

theorem Semantics.State.Keeps.refl (σ : State) : σ.Keeps σ := rfl

theorem Semantics.State.Keeps.trans {σ ρ τ : State} (h₁ : σ.Keeps ρ) (h₂ : ρ.Keeps τ) : σ.Keeps τ := by
  unfold Semantics.State.Keeps at *
  rw [← h₂, ← h₁]

theorem Semantics.State.saveStorage_keeps {σ τ : State} {r : Name} {segs : List Seg} {v : SVal}
    (h : σ.saveStorage r segs v = .ok τ) : σ.Keeps τ :=
  Close.saveStorage_restore h

theorem Semantics.State.writeStorage_keeps {σ τ : State} {r : Name} {segs : List Seg} {v : SVal}
    (h : σ.writeStorage r segs v = .ok τ) : σ.Keeps τ := by
  unfold State.writeStorage at h
  cases v with
  | prim _ => exact State.saveStorage_keeps h
  | struct _ | array _ _ _ | map _ _ =>
    cases hf : σ.findStorage r segs with
    | error _ => rw [hf] at h; cases h
    | ok _ => rw [hf] at h; exact State.saveStorage_keeps h

theorem pushAt_keeps {σ τ : State} {E : Ty} {r : Name} {segs : List Seg} {val : SVal → Res SVal}
    (h : pushAt σ E r segs val = .ok τ) : σ.Keeps τ := by
  unfold pushAt at h
  cases hf : σ.findStorage r segs with
  | error _ => rw [hf] at h; cases h
  | ok cur =>
    rw [hf] at h
    cases cur with
    | array elems shadow fx =>
      cases hv : val (pushSlot E shadow).1 with
      | error _ => simp only [hv, bind, Except.bind] at h; cases h
      | ok _ => simp only [hv, bind, Except.bind] at h; exact State.saveStorage_keeps h
    | prim _ | struct _ | map _ _ => cases h

theorem popAt_keeps {σ τ : State} {keep : Bool} {r : Name} {segs : List Seg}
    (h : popAt σ keep r segs = .ok τ) : σ.Keeps τ := by
  unfold popAt at h
  cases hf : σ.findStorage r segs with
  | error _ => rw [hf] at h; cases h
  | ok cur =>
    rw [hf] at h
    cases cur with
    | array elems shadow fx =>
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · exact State.saveStorage_keeps h
    | prim _ | struct _ | map _ _ => cases h

theorem pushPlaceAt_keeps {σ τ : State} {E : Ty} {r : Name} {segs : List Seg} {k : Int}
    (h : pushPlaceAt σ E r segs = .ok (τ, k)) : σ.Keeps τ := by
  unfold pushPlaceAt at h
  cases hf : σ.findStorage r segs with
  | error _ => rw [hf] at h; cases h
  | ok cur =>
    rw [hf] at h
    cases cur with
    | array elems shadow fx =>
      cases hs : σ.saveStorage r segs (.array (elems ++ [(pushSlot E shadow).1]) (pushSlot E shadow).2 fx) with
      | error _ => simp only [hs, bind, Except.bind] at h; cases h
      | ok σ' =>
        simp only [hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact State.saveStorage_keeps hs
    | prim _ | struct _ | map _ _ => cases h

/-- A storage term changes the storage only. -/
theorem STerm.eval_keeps {σ τ : State} : (s : STerm C) → s.eval σ = .ok τ → σ.Keeps τ
  | .storage, h => by cases h; exact State.Keeps.refl σ
  | .pv x, h => by
    simp only [STerm.eval] at h
    obtain ⟨b, -, h⟩ := Except.bind_eq_ok h
    cases b with
    | store st => cases h; rfl
    | val _ | spath _ _ | mref _ | ledger _ => cases h
  | .save s p v, h => by
    simp only [STerm.eval] at h
    obtain ⟨_, -, h⟩ := Except.bind_eq_ok h
    obtain ⟨τ₀, h₀, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨_, _⟩, -, h⟩ := Except.bind_eq_ok h
    exact (s.eval_keeps h₀).trans (State.writeStorage_keeps h)
  | .delAt s p, h => by
    simp only [STerm.eval] at h
    obtain ⟨τ₀, h₀, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨_, _⟩, -, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, -, h⟩ := Except.bind_eq_ok h
    exact (s.eval_keeps h₀).trans (State.saveStorage_keeps h)
  | .push s p v, h => by
    simp only [STerm.eval] at h
    obtain ⟨τ₀, h₀, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨_, _⟩, -, h⟩ := Except.bind_eq_ok h
    exact (s.eval_keeps h₀).trans (pushAt_keeps h)
  | .pushSlot s p E, h => by
    simp only [STerm.eval] at h
    obtain ⟨τ₀, h₀, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨_, _⟩, -, h⟩ := Except.bind_eq_ok h
    exact (s.eval_keeps h₀).trans (pushAt_keeps h)
  | .pop s p, h => by
    simp only [STerm.eval] at h
    obtain ⟨τ₀, h₀, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨_, _⟩, -, h⟩ := Except.bind_eq_ok h
    exact (s.eval_keeps h₀).trans (popAt_keeps h)
  | .shrink s p, h => by
    simp only [STerm.eval] at h
    obtain ⟨τ₀, h₀, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨_, _⟩, -, h⟩ := Except.bind_eq_ok h
    exact (s.eval_keeps h₀).trans (popAt_keeps h)
  | .extend s p E, h => by
    simp only [STerm.eval] at h
    obtain ⟨τ₀, h₀, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨_, _⟩, -, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨τ', _⟩, hp, h⟩ := Except.bind_eq_ok h
    cases h
    exact (s.eval_keeps h₀).trans (pushPlaceAt_keeps hp)

/-! ### Substituting a storage term for `storage` -/

/-- The storage term a write installs, substituted for `storage` by `withSt`.
(A structure rather than an `STerm` argument, so that the substitution is
structural recursion on the term alone.) -/
structure StWrite (C : Contract) where
  s : STerm C

mutual

/-- `{storage := s}e`: `s` for every `storage` in `e`. -/
def Term.withSt (w : StWrite C) : Term C → Term C
  | .binop op p a b => .binop op p (a.withSt w) (b.withSt w)
  | .unop op p a => .unop op p (a.withSt w)
  | .find s' p => .find (s'.withSt w) (p.withSt w)
  | .len s' p => .len (s'.withSt w) (p.withSt w)
  | .ite c a b => .ite (c.withSt w) (a.withSt w) (b.withSt w)
  | .lit v => .lit v
  | .pv x => .pv x
  | .env k => .env k
  | .read m a => .read m a
  | .mlen m i => .mlen m i
  | .net a => .net (a.withSt w)
  | .netOf x a => .netOf x (a.withSt w)

def PTerm.withSt (w : StWrite C) : PTerm C → PTerm C
  | .root r => .root r
  | .pv x => .pv x
  | .field p f => .field (p.withSt w) f
  | .at p i => .at (p.withSt w) (i.withSt w)
  | .next p => .next (p.withSt w)

def STerm.withSt (w : StWrite C) : STerm C → STerm C
  | .storage => w.s
  | .pv x => .pv x
  | .save s' p v => .save (s'.withSt w) (p.withSt w) (v.withSt w)
  | .delAt s' p => .delAt (s'.withSt w) (p.withSt w)
  | .push s' p v => .push (s'.withSt w) (p.withSt w) (v.withSt w)
  | .pushSlot s' p E => .pushSlot (s'.withSt w) (p.withSt w) E
  | .pop s' p => .pop (s'.withSt w) (p.withSt w)
  | .shrink s' p => .shrink (s'.withSt w) (p.withSt w)
  | .extend s' p E => .extend (s'.withSt w) (p.withSt w) E

def SValT.withSt (w : StWrite C) : SValT C → SValT C
  | .val t => .val (t.withSt w)
  | .find s' p => .find (s'.withSt w) (p.withSt w)
  | .copyMem m i => .copyMem m i
  | .newArr R n => .newArr R (n.withSt w)

end

mutual

/-- Every storage read of the term is a `storage` term: no index check, no
push slot, no memory. -/
def Term.stExplicit : Term C → Bool
  | .lit _ | .pv _ | .env _ => true
  | .binop _ _ a b => a.stExplicit && b.stExplicit
  | .unop _ _ a | .net a | .netOf _ a => a.stExplicit
  | .find s p | .len s p => s.stExplicit && p.stExplicit
  | .ite c a b => c.stExplicit && a.stExplicit && b.stExplicit
  | .read .. | .mlen .. => false

def PTerm.stExplicit : PTerm C → Bool
  | .root _ | .pv _ => true
  | .field p _ => p.stExplicit
  | .at .. | .next _ => false

def STerm.stExplicit : STerm C → Bool
  | .storage | .pv _ => true
  | .save s p v | .push s p v => s.stExplicit && p.stExplicit && v.stExplicit
  | .delAt s p | .pop s p | .shrink s p | .pushSlot s p _ | .extend s p _ =>
    s.stExplicit && p.stExplicit

def SValT.stExplicit : SValT C → Bool
  | .val t | .newArr _ t => t.stExplicit
  | .find s p => s.stExplicit && p.stExplicit
  | .copyMem .. => false

end

section WithSt

variable {w : StWrite C} {σ τ : State}

mutual

/-- Read before `{storage := s}`, the substituted term reads what the term
reads after it. -/
theorem Term.withSt_eval (hs : w.s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (e : Term C) → e.stExplicit = true → (e.withSt w).eval σ = e.eval τ
  | .lit _, _ => rfl
  | .pv _, _ => by rw [← hk]; rfl
  | .env _, _ => by rw [← hk]; rfl
  | .binop _ _ a b, he => by
    simp only [Term.stExplicit, Bool.and_eq_true] at he
    simp only [Term.withSt, Term.eval, Term.withSt_eval hs hk a he.1, Term.withSt_eval hs hk b he.2]
  | .unop _ _ a, he => by
    simp only [Term.stExplicit] at he
    simp only [Term.withSt, Term.eval, Term.withSt_eval hs hk a he]
  | .find s' p, he => by
    simp only [Term.stExplicit, Bool.and_eq_true] at he
    simp only [Term.withSt, Term.eval, STerm.withSt_eval hs hk s' he.1, PTerm.withSt_eval hs hk p he.2]
  | .len s' p, he => by
    simp only [Term.stExplicit, Bool.and_eq_true] at he
    simp only [Term.withSt, Term.eval, STerm.withSt_eval hs hk s' he.1, PTerm.withSt_eval hs hk p he.2]
  | .ite c a b, he => by
    simp only [Term.stExplicit, Bool.and_eq_true] at he
    simp only [Term.withSt, Term.eval, Term.withSt_eval hs hk c he.1.1, Term.withSt_eval hs hk a he.1.2,
      Term.withSt_eval hs hk b he.2]
  | .read .., he | .mlen .., he => by simp [Term.stExplicit] at he
  | .net a, he | .netOf _ a, he => by
    simp only [Term.stExplicit] at he
    simp only [Term.withSt, Term.eval, Term.withSt_eval hs hk a he]
    rw [← hk]; rfl

theorem PTerm.withSt_eval (hs : w.s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (p : PTerm C) → p.stExplicit = true → (p.withSt w).eval σ = p.eval τ
  | .root _, _ => rfl
  | .pv _, _ => by rw [← hk]; rfl
  | .field p _, he => by
    simp only [PTerm.stExplicit] at he
    simp only [PTerm.withSt, PTerm.eval, PTerm.withSt_eval hs hk p he]
  | .at .., he | .next _, he => by simp [PTerm.stExplicit] at he

theorem STerm.withSt_eval (hs : w.s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (s' : STerm C) → s'.stExplicit = true → (s'.withSt w).eval σ = s'.eval τ
  | .storage, _ => hs
  | .pv _, _ => by rw [← hk]; rfl
  | .save s' p v, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.eval, STerm.withSt_eval hs hk s' he.1.1, PTerm.withSt_eval hs hk p he.1.2,
      SValT.withSt_eval hs hk v he.2]
  | .push s' p v, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.eval, STerm.withSt_eval hs hk s' he.1.1, PTerm.withSt_eval hs hk p he.1.2,
      SValT.withSt_eval hs hk v he.2]
  | .delAt s' p, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.eval, STerm.withSt_eval hs hk s' he.1, PTerm.withSt_eval hs hk p he.2]
  | .pop s' p, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.eval, STerm.withSt_eval hs hk s' he.1, PTerm.withSt_eval hs hk p he.2]
  | .shrink s' p, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.eval, STerm.withSt_eval hs hk s' he.1, PTerm.withSt_eval hs hk p he.2]
  | .pushSlot s' p _, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.eval, STerm.withSt_eval hs hk s' he.1, PTerm.withSt_eval hs hk p he.2]
  | .extend s' p _, he => by
    simp only [STerm.stExplicit, Bool.and_eq_true] at he
    simp only [STerm.withSt, STerm.eval, STerm.withSt_eval hs hk s' he.1, PTerm.withSt_eval hs hk p he.2]

theorem SValT.withSt_eval (hs : w.s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (v : SValT C) → v.stExplicit = true → (v.withSt w).eval σ = v.eval τ
  | .val t, he => by
    simp only [SValT.stExplicit] at he
    simp only [SValT.withSt, SValT.eval, Term.withSt_eval hs hk t he]
  | .newArr _ n, he => by
    simp only [SValT.stExplicit] at he
    simp only [SValT.withSt, SValT.eval, Term.withSt_eval hs hk n he]
  | .find s' p, he => by
    simp only [SValT.stExplicit, Bool.and_eq_true] at he
    simp only [SValT.withSt, SValT.eval, STerm.withSt_eval hs hk s' he.1, PTerm.withSt_eval hs hk p he.2]
  | .copyMem .., he => by simp [SValT.stExplicit] at he

end

end WithSt

/-! ### The merge -/

def UpdElem.withSt (s : STerm C) : UpdElem C → UpdElem C
  | .val x t => .val x (t.withSt ⟨s⟩)
  | .path x p => .path x (p.withSt ⟨s⟩)
  | .storage s' => .storage (s'.withSt ⟨s⟩)
  | .store x s' => .store x (s'.withSt ⟨s⟩)
  | .transfer r a => .transfer (r.withSt ⟨s⟩) (a.withSt ⟨s⟩)
  | .mref x i => .mref x i
  | .memory m => .memory m
  | .saveNet x => .saveNet x
  | .book a => .book (a.withSt ⟨s⟩)

def UpdElem.stExplicit : UpdElem C → Bool
  | .val _ t => t.stExplicit
  | .path _ p => p.stExplicit
  | .storage s | .store _ s => s.stExplicit
  | .transfer r a => r.stExplicit && a.stExplicit
  | .saveNet _ => true
  | .book a => a.stExplicit
  | .mref .. | .memory _ => false

/-- `{storage := s}V`: `s` substituted for `storage` in `V`'s right-hand sides. -/
def Upd.withSt (s : STerm C) (V : Upd C) : Upd C := V.map (·.withSt s)

theorem UpdElem.withSt_write {s : STerm C} {σ τ : State} (hs : s.eval σ = .ok τ)
    (hk : σ.Keeps τ) (ρ : State) :
    (e : UpdElem C) → e.stExplicit = true → (e.withSt s).write σ ρ = e.write τ ρ
  | .val _ t, he => by
    simp only [UpdElem.withSt, UpdElem.write, Term.withSt_eval (w := ⟨s⟩) hs hk t he]
  | .path _ p, he => by
    simp only [UpdElem.withSt, UpdElem.write, PTerm.withSt_eval (w := ⟨s⟩) hs hk p he]
  | .storage s', he => by
    simp only [UpdElem.withSt, UpdElem.write, STerm.withSt_eval (w := ⟨s⟩) hs hk s' he]
  | .store _ s', he => by
    simp only [UpdElem.withSt, UpdElem.write, STerm.withSt_eval (w := ⟨s⟩) hs hk s' he]
  | .transfer r a, he => by
    simp only [UpdElem.stExplicit, Bool.and_eq_true] at he
    simp only [UpdElem.withSt, UpdElem.write, Term.withSt_eval (w := ⟨s⟩) hs hk r he.1,
      Term.withSt_eval (w := ⟨s⟩) hs hk a he.2]
  | .saveNet _, _ => by simp only [UpdElem.withSt, UpdElem.write]; rw [← hk]
  | .book a, he => by
    simp only [UpdElem.stExplicit] at he
    simp only [UpdElem.withSt, UpdElem.write, Term.withSt_eval (w := ⟨s⟩) hs hk a he]
    rw [← hk]; rfl
  | .mref .., he | .memory _, he => by simp [UpdElem.stExplicit] at he

theorem Upd.withSt_foldl {s : STerm C} {σ τ : State} (hs : s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (V : Upd C) → V.all (·.stExplicit) = true → ∀ ρ,
      (V.withSt s).foldlM (fun ρ e => e.write σ ρ) ρ = V.foldlM (fun ρ e => e.write τ ρ) ρ
  | [], _, _ => rfl
  | e :: V, hV, ρ => by
    simp only [List.all_cons, Bool.and_eq_true] at hV
    simp only [Upd.withSt, List.map_cons, List.foldlM_cons, UpdElem.withSt_write hs hk ρ e hV.1]
    congr 1
    funext ρ'
    exact Upd.withSt_foldl hs hk V hV.2 ρ'

/-- **`sequentialToParallel`** over a storage write:
`{storage := s}{V} ψ ⟺ {storage := s ‖ {storage := s}V} ψ`. -/
theorem Upd.mergeStorage_holds (m : Modality) (s : STerm C) (V : Upd C)
    (hV : V.all (·.stExplicit) = true) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (.storage s :: V.withSt s) ψ) ↔ holds σ (.upd m [.storage s] (.upd m V ψ)) := by
  simp only [holds, Upd.apply, List.foldlM_cons, List.foldlM_nil, Close.UpdElem.write_storage]
  cases hs : s.eval σ with
  | error _ => exact Iff.rfl
  | ok τ =>
    have hk : σ.Keeps τ := STerm.eval_keeps s hs
    simp only [Close.ok_bind]
    rw [hk, Upd.withSt_foldl hs hk V hV τ]
    exact Iff.rfl

/-- `sequentialToParallel` in a derivation, for a storage write followed by
an update whose storage reads are all `storage` terms. -/
theorem Proves.mergeStorage {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {s : STerm C}
    {V : Upd C} {φ : Fml C} (h : Proves R (Γ ++ [.upd m (.storage s :: V.withSt s)]) φ)
    (hV : V.all (·.stExplicit) = true := by rfl)
    (hφ : (Hyp.wrap (Γ ++ [.upd m [.storage s]] ++ [.upd m V]) φ).modalFree = true := by
      first | rfl | decide) :
    Proves R (Γ ++ [.upd m [.storage s]] ++ [.upd m V]) φ :=
  .close (fun σ => by
    have := h.sound σ
    simp only [List.append_assoc, List.cons_append, List.nil_append, Hyp.wrap_append,
      Hyp.wrap] at this ⊢
    exact Hyp.wrap_mono (fun τ hτ => (Upd.mergeStorage_holds m s V hV φ τ).1 hτ) Γ σ this) hφ

/-! ## Rewriting inside an update

In `{storage := s ‖ x := find(s, p)}` the right-hand side of `x` is read
before the write, where `find(s, p)` need not be `v`: it is, in every state
where the update runs.  Under the box that is enough — where the update
halts, what follows it holds — so an equation that holds wherever the update
runs (`Hyp.EqRun`) rewrites its right-hand sides. -/

/-- `t ≐ t'` wherever `Γ` leads and `U` then runs. -/
def Hyp.EqRun (Γ : List (Hyp C)) (U : Upd C) (t t' : Term C) : Prop :=
  ∀ σ τ ρ, Hyp.Reaches Γ σ τ → U.apply τ = .ok ρ → t.eval τ = t'.eval τ

/-- The update at hypothesis `n`, or the empty one. -/
def Hyp.updAt (Γ : List (Hyp C)) (n : Nat) : Upd C :=
  match Γ.drop n with
  | .upd _ U :: _ => U
  | _ => []

/-- **Rewriting in a box update.**  In `Γ ⟹ φ` whose hypothesis `n` is
`{U}` under the box, `t` becomes `t'` in `U`'s right-hand sides, given
`t ≐ t'` wherever `U` runs. -/
theorem Proves.rewriteUpd {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} {t t' : Term C}
    (n : Nat) (e : Hyp.EqRun (Γ.take n) (Hyp.updAt Γ n) t t')
    (h : Proves R (Γ.take n ++ .upd .box ((Hyp.updAt Γ n).rw (t, t')) :: Γ.drop (n + 1)) φ)
    (hn : Γ.drop n = .upd .box (Hyp.updAt Γ n) :: Γ.drop (n + 1) := by rfl)
    (hφ : (Hyp.wrap Γ φ).modalFree = true := by first | rfl | decide) :
    Proves R Γ φ :=
  .close (fun σ => by
    have hs := h.sound σ
    rw [Hyp.wrap_append] at hs
    rw [← List.take_append_drop n Γ, hn, Hyp.wrap_append]
    refine Hyp.wrap_reach (Γ.take n) σ (fun τ hr hτ => ?_) hs
    simp only [Hyp.wrap, holds] at hτ ⊢
    cases hU : (Hyp.updAt Γ n).apply τ with
    | error _ => trivial
    | ok ρ =>
      rw [Upd.rw_apply (q := (t, t')) (e σ τ ρ hr hU), hU] at hτ
      exact hτ) hφ

/-- **`findOnSave`**, in a parallel update: where
`{storage := save(storage, p, v) ‖ …}` runs, `find(save(storage, p, v), p)`
is `v`. -/
theorem Hyp.EqRun.findOnSave {Γ : List (Hyp C)} {U : Upd C} {p : PTerm C} {v : Value}
    (hU : U.head? = some (.storage (.save .storage p (.val (.lit v)))) := by rfl) :
    Hyp.EqRun Γ U (.find (.save .storage p (.val (.lit v))) p) (.lit v) := by
  intro σ τ ρ _ hρ
  cases U with
  | nil => cases hU
  | cons e U =>
    cases hU
    simp only [Upd.apply, List.foldlM_cons, Close.UpdElem.write_storage] at hρ
    obtain ⟨τ₁, hρ, -⟩ := Except.bind_eq_ok hρ
    obtain ⟨τ₂, hsave, -⟩ := Except.bind_eq_ok hρ
    rw [Close.STerm.eval_save, Close.Term.eval_lit, Close.ok_bind, Close.STerm.eval_storage,
      Close.ok_bind] at hsave
    obtain ⟨⟨r, segs⟩, hp, hsave⟩ := Except.bind_eq_ok hsave
    rw [Close.Term.eval_find, Close.STerm.eval_save, Close.Term.eval_lit, Close.ok_bind,
      Close.STerm.eval_storage, Close.ok_bind, hp, Close.ok_bind, hsave, Close.ok_bind,
      Close.ok_bind, State.findStorage_saveStorage_same hsave, Close.ok_bind,
      Close.asValue_toSVal]

/-! ## The relation is a setoid

For a fixed context, `Hyp.EqUnder Γ₀` is an equivalence on terms (and a
congruence for the term constructors: `Hyp.EqUnder.rw`), so it is a
`Setoid`.  It is not a congruence for every formula context, which is why
`rw` with it rewrites only where the sequent reads in the state `Γ₀` leads
to (`Hyp.rwHere_holds`); `Proves.rewrite` is that setoid rewrite. -/

section Setoid

variable {Γ : List (Hyp C)} {U : Upd C} {t₁ t₂ t₃ : Term C}

theorem Hyp.EqUnder.refl (Γ : List (Hyp C)) (t : Term C) : Hyp.EqUnder Γ t t :=
  fun _ _ _ => rfl

theorem Hyp.EqUnder.symm (h : Hyp.EqUnder Γ t₁ t₂) : Hyp.EqUnder Γ t₂ t₁ :=
  fun σ τ hr => (h σ τ hr).symm

theorem Hyp.EqUnder.trans (h₁ : Hyp.EqUnder Γ t₁ t₂) (h₂ : Hyp.EqUnder Γ t₂ t₃) :
    Hyp.EqUnder Γ t₁ t₃ :=
  fun σ τ hr => (h₁ σ τ hr).trans (h₂ σ τ hr)

/-- A congruence for the term constructors: an equal subterm replaced. -/
theorem Hyp.EqUnder.rw (h : Hyp.EqUnder Γ t₁ t₂) (e : Term C) :
    Hyp.EqUnder Γ (e.rw (t₁, t₂)) e :=
  fun σ τ hr => Term.rw_eval (q := (t₁, t₂)) (h σ τ hr) e

theorem Hyp.EqUnder.equivalence (Γ : List (Hyp C)) : Equivalence (Hyp.EqUnder Γ) :=
  ⟨Hyp.EqUnder.refl Γ, Hyp.EqUnder.symm, Hyp.EqUnder.trans⟩

/-- The terms that read alike behind `Γ`. -/
def Hyp.EqUnder.setoid (Γ : List (Hyp C)) : Setoid (Term C) :=
  ⟨Hyp.EqUnder Γ, Hyp.EqUnder.equivalence Γ⟩

instance : Trans (Hyp.EqUnder (C := C) Γ) (Hyp.EqUnder Γ) (Hyp.EqUnder Γ) :=
  ⟨Hyp.EqUnder.trans⟩

theorem Hyp.EqRun.refl (Γ : List (Hyp C)) (U : Upd C) (t : Term C) : Hyp.EqRun Γ U t t :=
  fun _ _ _ _ _ => rfl

theorem Hyp.EqRun.symm (h : Hyp.EqRun Γ U t₁ t₂) : Hyp.EqRun Γ U t₂ t₁ :=
  fun σ τ ρ hr hU => (h σ τ ρ hr hU).symm

theorem Hyp.EqRun.trans (h₁ : Hyp.EqRun Γ U t₁ t₂) (h₂ : Hyp.EqRun Γ U t₂ t₃) :
    Hyp.EqRun Γ U t₁ t₃ :=
  fun σ τ ρ hr hU => (h₁ σ τ ρ hr hU).trans (h₂ σ τ ρ hr hU)

theorem Hyp.EqRun.equivalence (Γ : List (Hyp C)) (U : Upd C) : Equivalence (Hyp.EqRun Γ U) :=
  ⟨Hyp.EqRun.refl Γ U, Hyp.EqRun.symm, Hyp.EqRun.trans⟩

/-- The terms that read alike behind `Γ`, wherever `U` then runs. -/
def Hyp.EqRun.setoid (Γ : List (Hyp C)) (U : Upd C) : Setoid (Term C) :=
  ⟨Hyp.EqRun Γ U, Hyp.EqRun.equivalence Γ U⟩

instance : Trans (Hyp.EqRun (C := C) Γ U) (Hyp.EqRun Γ U) (Hyp.EqRun Γ U) :=
  ⟨Hyp.EqRun.trans⟩

/-- What holds behind the whole context holds wherever its last update runs. -/
theorem Hyp.EqUnder.toRun (h : Hyp.EqUnder Γ t₁ t₂) : Hyp.EqRun Γ U t₁ t₂ :=
  fun σ τ _ hr _ => h σ τ hr

end Setoid

/-! ## `rw` on a sequent

`rw [r]`, with `r` an equation under a context (`Hyp.EqUnder`, `Hyp.EqRun`)
rather than an `=`, rewrites the sequent at the hypothesis where `r` holds:
it tries `Proves.rewriteUpd n r` and `Proves.rewrite n r` for each `n` and
keeps the first that fits the rule's shape and changes the goal.  Scoped to
`Proves`, where the derivations are written; elsewhere `rw` is Lean's. -/

open Lean Elab Tactic Meta in
/-- Rewrite a sequent with an equation under its context, at the first
hypothesis where it applies. -/
elab "sol_rw " r:term : tactic => do
  let goal ← getMainGoal
  let before ← instantiateMVars (← goal.getType)
  for n in List.range 17 do
    for rule in [``Proves.rewriteUpd, ``Proves.rewrite] do
      let saved ← saveState
      try
        let k := Syntax.mkNumLit (toString n)
        evalTactic (← `(tactic| refine $(mkIdent rule) $k $r ?_))
        let after ← instantiateMVars (← (← getMainGoal).getType)
        if ← isDefEq after before then throwError "no change"
        return
      catch _ => saved.restore
  throwError "sol_rw: no hypothesis of the sequent where {r} rewrites"

namespace Proves

scoped macro_rules
  | `(tactic| rw [$r:term]) => `(tactic| sol_rw $r)

end Proves

end Solidity
