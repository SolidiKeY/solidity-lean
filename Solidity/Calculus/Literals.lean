import Solidity.Calculus.ChainBranches

/-!
# The literal laws

KeY folds an operation on two literals by its `*_literals` taclets
(`integerSimplificationRules.key`): `250 + 10 ⇝ 260`, `260 <= 255 ⇝ false`.
Here each is a constructor of `LitLaw`, stated as the interpreter computes
it: a sum, a difference or a quotient folds where it stays in `uint` range
(`checkArith`; out of range, or divided by zero, the operation reverts, and
the term is its own normal form), a comparison always.

A literal law is **exact** (`LitLaw.exact`): its left side returns the
literal on the right in every state.  So it rewrites anywhere, under any
modality — in an update's right-hand side, a memory term included, since
the law is about what a term returns, not what it denotes (`LineRw.lit`,
`Upd.rwEv`, with no premise about what the update holds, unlike
`LineRw.lawUpdAny`), and in the
equations and `defined(…)`s of the propositional skeleton of a line
(`LineRw.litEq`, through `¬`, `∧`, `→`; never inside a modality, an update
or a quantifier, whose formulas are read elsewhere).  Both are
equivalences.

A comparison folded in an update, `{ se1 := 260 <= 255 }`, writes a Boolean
literal, `{ se1 := false }`; the branch it conditions folds by
`Fml.concrete` once the update is pushed through it (`LineRw.applyOnRigidIn`).
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-- KeY's `*_literals` taclets, as the interpreter computes them.  Hover a
constructor for the taclet. -/
inductive LitLaw : Term C → Term C → Prop
  /-- **`add_literals`**: `a + b ⇝ a + b` folded, in `uint` range. -/
  | add_literals {a b : Int} (h : 0 ≤ a + b ∧ a + b < uintBound := by decide) :
      LitLaw (.binop .add .uint (.lit (.int a)) (.lit (.int b))) (.lit (.int (a + b)))
  /-- **`sub_literals`**: `a - b ⇝ a - b` folded, in `uint` range. -/
  | sub_literals {a b : Int} (h : 0 ≤ a - b ∧ a - b < uintBound := by decide) :
      LitLaw (.binop .sub .uint (.lit (.int a)) (.lit (.int b))) (.lit (.int (a - b)))
  /-- **`leq_literals`**: `a <= b ⇝ true` or `false`. -/
  | leq_literals {a b : Int} :
      LitLaw (.binop .le .uint (.lit (.int a)) (.lit (.int b))) (.lit (.bool (decide (a ≤ b))))
  /-- **`less_literals`**: `a < b ⇝ true` or `false`. -/
  | less_literals {a b : Int} :
      LitLaw (.binop .lt .uint (.lit (.int a)) (.lit (.int b))) (.lit (.bool (decide (a < b))))
  /-- **`greater_literals`**: `a > b ⇝ true` or `false`. -/
  | greater_literals {a b : Int} :
      LitLaw (.binop .gt .uint (.lit (.int a)) (.lit (.int b))) (.lit (.bool (decide (b < a))))
  /-- **`geq_literals`**: `a >= b ⇝ true` or `false`. -/
  | geq_literals {a b : Int} :
      LitLaw (.binop .ge .uint (.lit (.int a)) (.lit (.int b))) (.lit (.bool (decide (b ≤ a))))
  /-- **`div_literals`**: `a / b ⇝ a / b` folded (truncated, as Solidity divides), the divisor not
  zero and the quotient in `uint` range. -/
  | div_literals {a b : Int} (h : b ≠ 0 ∧ 0 ≤ a.tdiv b ∧ a.tdiv b < uintBound := by decide) :
      LitLaw (.binop .div .uint (.lit (.int a)) (.lit (.int b))) (.lit (.int (a.tdiv b)))

/-- An operation on two integer literals is the interpreter's, applied and
range-checked (no `&&`/`||` short-circuit reads an integer). -/
theorem LitLaw.binop_lit_eval (op : BinOp) (a b : Int) (σ : State) :
    (Term.binop op .uint (.lit (.int a)) (.lit (.int b)) : Term C).eval σ =
      (do checkArith (op.retTy (.prim .uint)) (← applyBinOp op (.int a) (.int b))) := by
  cases op <;> rfl

/-- **A literal law is exact**: its right side is a literal, which its left
side returns in every state. -/
theorem LitLaw.exact {t t' : Term C} : LitLaw t t' → ∃ v, t' = .lit v ∧ ∀ σ, t.eval σ = .ok v
  | @LitLaw.add_literals _ a b h => ⟨_, rfl, fun σ => by
      rw [LitLaw.binop_lit_eval]
      show (if 0 ≤ a + b ∧ a + b < uintBound then (Except.ok (Value.int (a + b)) : Res Value)
        else .error .revert) = _
      rw [if_pos h]⟩
  | @LitLaw.sub_literals _ a b h => ⟨_, rfl, fun σ => by
      rw [LitLaw.binop_lit_eval]
      show (if 0 ≤ a - b ∧ a - b < uintBound then (Except.ok (Value.int (a - b)) : Res Value)
        else .error .revert) = _
      rw [if_pos h]⟩
  | .leq_literals => ⟨_, rfl, fun σ => by rw [LitLaw.binop_lit_eval]; rfl⟩
  | .less_literals => ⟨_, rfl, fun σ => by rw [LitLaw.binop_lit_eval]; rfl⟩
  | .greater_literals => ⟨_, rfl, fun σ => by rw [LitLaw.binop_lit_eval]; rfl⟩
  | .geq_literals => ⟨_, rfl, fun σ => by rw [LitLaw.binop_lit_eval]; rfl⟩
  | @LitLaw.div_literals _ a b h => ⟨_, rfl, fun σ => by
      rw [LitLaw.binop_lit_eval]
      show (if b = 0 then (Except.error .revert : Res Value) else .ok (Value.int (a.tdiv b))) >>=
        checkArith (.prim .uint) = _
      rw [if_neg h.1]
      show (if 0 ≤ a.tdiv b ∧ a.tdiv b < uintBound then (Except.ok (Value.int (a.tdiv b)) : Res Value)
        else .error .revert) = _
      rw [if_pos h.2]⟩

/-- Where the left side returns, the right returns the same. -/
theorem LitLaw.refines {t t' : Term C} (r : LitLaw t t') : Term.EvalRefines t t' := by
  obtain ⟨v, rfl, hv⟩ := r.exact
  intro σ x hx
  rw [hv σ] at hx
  exact hx

/-- Where the right side returns, the left returns the same: a literal law
halts nowhere. -/
theorem LitLaw.refines_rev {t t' : Term C} (r : LitLaw t t') (σ : State) :
    Res.Le (t'.eval σ) (t.eval σ) := by
  obtain ⟨v, rfl, hv⟩ := r.exact
  intro x hx
  rw [hv σ]
  exact hx

/-- The two sides denote alike in the Theory. -/
theorem LitLaw.theq {t t' : Term C} (r : LitLaw t t') : Term.Theq t t' := by
  obtain ⟨v, rfl, hv⟩ := r.exact
  intro σ
  rw [Term.denote_eval (hv σ)]
  exact Theory.StValue.Equiv.refl _

/-! ## In an update's right-hand sides -/

/-- The literal law on the right-hand sides of `{U}_m φ`, if it rewrites
one: under any modality, and with no premise on `U`, since the law is exact. -/
def Fml.rwLitTop (q : Term C × Term C) (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  if (U.rwEv q != U) = true then some (.upd m (U.rwEv q) φ) else none

theorem Fml.rwLitTop_holds {q : Term C × Term C} (r : LitLaw q.1 q.2) {m : Modality} {U : Upd C}
    {φ ψ : Fml C} (h : Fml.rwLitTop q m U φ = some ψ) (σ : State) :
    holds σ ψ ↔ holds σ (.upd m U φ) := by
  unfold Fml.rwLitTop at h
  split at h
  · cases h; exact Upd.rwEv_holds (u := .val) r.refines.at (fun σ _ _ => r.refines_rev σ) m φ σ
  · nomatch h

/-- The literal law on the right-hand sides of the update at position `i`. -/
def Fml.rwLitAt (q : Term C × Term C) (i : Nat) : Fml C → Option (Fml C) :=
  Fml.atSpine (Fml.rwLitTop q) i

/-! ## In the equations of the skeleton -/

/-- The law in a literal leaf: in both sides of an equation and under
`defined(…)`, which it may enter since it halts nowhere. -/
def Fml.rwLit (q : Term C × Term C) : Fml C → Fml C
  | .eq a b => .eq (a.rw q) (b.rw q)
  | .defined t => .defined (t.rw q)
  | φ => φ

/-- Whether the law rewrites something in a literal leaf. -/
def Fml.litRewrites (q : Term C × Term C) : Fml C → Bool
  | .eq a b => a.rw q != a || b.rw q != b
  | .defined t => t.rw q != t
  | _ => false

theorem Fml.rwLit_holds {q : Term C × Term C} (r : LitLaw q.1 q.2) (φ : Fml C) (σ : State) :
    holds σ (φ.rwLit q) ↔ holds σ φ := by
  cases φ with
  | eq a b =>
    have ha : Theory.StValue.Equiv ((a.rw q).denote σ) (a.denote σ) := a.rw_denote (r.theq σ)
    have hb : Theory.StValue.Equiv ((b.rw q).denote σ) (b.denote σ) := b.rw_denote (r.theq σ)
    exact ⟨fun e => ha.symm.trans (e.trans hb), fun e => ha.trans (e.trans hb.symm)⟩
  | defined t =>
    exact ⟨fun ⟨x, hx⟩ => ⟨x, Term.rw_eval_rev (r.refines_rev σ) t x hx⟩,
      fun ⟨x, hx⟩ => ⟨x, Term.rw_eval r.refines t σ x hx⟩⟩
  | _ => exact Iff.rfl

/-- The law in every literal leaf along the skeleton `s`. -/
def Fml.rwSkelAlong (q : Term C × Term C) : Skel → Fml C → Fml C
  | .and _ _ l r, .and φ ψ => .and (φ.rwSkelAlong q l) (ψ.rwSkelAlong q r)
  | .imp _ _ l r, .imp φ ψ => .imp (φ.rwSkelAlong q l) (ψ.rwSkelAlong q r)
  | .not _ s, .not φ => .not (φ.rwSkelAlong q s)
  | .lit, φ => φ.rwLit q
  | _, φ => φ

/-- Whether the law rewrites some literal leaf along `s`. -/
def Fml.skelRewrites (q : Term C × Term C) : Skel → Fml C → Bool
  | .and _ _ l r, .and φ ψ | .imp _ _ l r, .imp φ ψ => φ.skelRewrites q l || ψ.skelRewrites q r
  | .not _ s, .not φ => φ.skelRewrites q s
  | .lit, φ => φ.litRewrites q
  | _, _ => false

theorem Fml.rwSkelAlong_holds {q : Term C × Term C} (hr : LitLaw q.1 q.2) (σ : State) :
    (s : Skel) → (φ : Fml C) → (holds σ (φ.rwSkelAlong q s) ↔ holds σ φ)
  | .opaque, _ | .upd _, _ => Iff.rfl
  | .lit, φ => Fml.rwLit_holds hr φ σ
  | .and _ _ l r, φ => by
    cases φ with
    | and a b =>
      show holds σ (a.rwSkelAlong q l) ∧ holds σ (b.rwSkelAlong q r) ↔ holds σ a ∧ holds σ b
      rw [Fml.rwSkelAlong_holds hr σ l a, Fml.rwSkelAlong_holds hr σ r b]
    | _ => exact Iff.rfl
  | .imp _ _ l r, φ => by
    cases φ with
    | imp a b =>
      show (holds σ (a.rwSkelAlong q l) → holds σ (b.rwSkelAlong q r)) ↔ (holds σ a → holds σ b)
      rw [Fml.rwSkelAlong_holds hr σ l a, Fml.rwSkelAlong_holds hr σ r b]
    | _ => exact Iff.rfl
  | .not _ s, φ => by
    cases φ with
    | not a =>
      show ¬ holds σ (a.rwSkelAlong q s) ↔ ¬ holds σ a
      rw [Fml.rwSkelAlong_holds hr σ s a]
    | _ => exact Iff.rfl

/-- The law in every literal leaf of the whole skeleton of `φ`. -/
def Fml.rwSkel (q : Term C × Term C) (φ : Fml C) : Fml C := φ.rwSkelAlong q φ.skel

theorem Fml.rwSkel_holds {q : Term C × Term C} (r : LitLaw q.1 q.2) (φ : Fml C) (σ : State) :
    holds σ (φ.rwSkel q) ↔ holds σ φ :=
  Fml.rwSkelAlong_holds r σ φ.skel φ

/-- The law along `s`, if it rewrites a leaf. -/
def Fml.rwSkelOn (q : Term C × Term C) (s : Skel) (φ : Fml C) : Option (Fml C) :=
  if φ.skelRewrites q s then some (φ.rwSkelAlong q s) else none

theorem Fml.rwSkelOn_holds {q : Term C × Term C} (r : LitLaw q.1 q.2) {s : Skel} {φ ψ : Fml C}
    (h : φ.rwSkelOn q s = some ψ) (σ : State) : holds σ ψ ↔ holds σ φ := by
  unfold Fml.rwSkelOn at h
  split at h
  · cases h; exact Fml.rwSkelAlong_holds r σ s φ
  · nomatch h

/-- The law along `s` below `n` updates, if it rewrites a leaf. -/
def Fml.rwLitBelow (q : Term C × Term C) (n : Nat) (s : Skel) : Fml C → Option (Fml C) :=
  Fml.belowSpine (Fml.rwSkelOn q s) n

/-- The law on the whole skeleton below `n` updates, if it rewrites a leaf. -/
def Fml.rwLitSkelAt (q : Term C × Term C) (n : Nat) : Fml C → Option (Fml C) :=
  Fml.belowSpine (fun φ => φ.rwSkelOn q φ.skel) n

/-! ## The rewrites, bundled -/

namespace LineRw

/-- The literal law `r` on the right-hand sides of the update at position
`i`, under any modality. -/
def lit {t t' : Term C} (r : LitLaw t t') (i : Nat) : LineRw C :=
  ⟨Fml.rwLitAt (t, t') i, Fml.atSpine_sound (fun h σ => (Fml.rwLitTop_holds r h σ).1) i _⟩

/-- The literal law `r` in the equations and `defined(…)`s of the skeleton
`s` of the formula below `n` updates. -/
def litEq {t t' : Term C} (r : LitLaw t t') (n : Nat) (s : Skel) : LineRw C :=
  ⟨Fml.rwLitBelow (t, t') n s,
    fun h σ => (Fml.belowSpine_holds (fun h σ => Fml.rwSkelOn_holds r h σ) n _ h σ).1⟩

end LineRw

end Solidity
