import Solidity.Calculus.ChainRewrites

/-!
# Rewrites under a branch

A split leaves its goals behind one update, as a conjunction of
implications: `{ x := 260 ‖ se1 := 260 <= 255 } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨ revert(); ⟩ φ))`.
The printed trace goes on inside each goal, and so does KeY: the update is
pushed through the connectives (`applyOnRigid` through `∧`, `→`, `¬`), the
literal conditions fold (`concrete_*`, `eqClose`), and the updates a goal
accumulates merge where they stand.  This module says *where* on the
propositional skeleton of a line each rewrite acts, as
`Calculus/ChainRewrites.lean` says where on the update spine.

**The skeleton is read off the line by the elaborator** (`Skel`), not by the
rewrite: a chain's postcondition `φ : Post C` is a variable the kernel cannot
case on, and a function that matched on it would compute nowhere.  So each
rewrite takes the skeleton of the formula it acts on, the elaborator writes
it (`Chains.lean`, `skelOf`) with the postconditions marked opaque, and the
rewrite looks only where the skeleton says there is something to see.  The
rewrite is sound for every skeleton (a leaf it is told not to look at is
kept whole), and the versions without one (`Fml.push`, `Fml.concrete`,
`Fml.inSkeleton`) take the whole skeleton of a concrete formula (`Fml.skel`).

| `LineRw` | computes | line before ⇝ line after | sound by |
|---|---|---|---|
| `applyOnRigidIn i s` | `Fml.pushTop` | `{U}(A ∧ B) ⇝ A[U] ∧ B[U]` at spine position `i`, `U` total | `Fml.pushAlong_holds` (iff) |
| `applyOnRigidBoxIn i s` | `Fml.pushBoxTop` | `[U](A ∧ B) ⇐ [U]A ∧ [U]B`, a rigid leaf substituted | `Fml.pushBoxAlong_sound` |
| `concrete n s` | `Fml.concreteBelow` | `true ∧ A ⇝ A`, `v ≐ v ⇝ true`, … below `n` updates | `Fml.concreteAlong_holds` (iff) |
| `mergeIn n s` | `Fml.inSkeletonAlong` | `sequentialToParallel` on the first spine found under a branch | `Fml.mergeSpine_holds` (iff) |

**Why the diamond is the box's here.**  `⟨U⟩(A → B)` asks `U` to return;
`⟨U⟩A → ⟨U⟩B` holds where `U` halts (its antecedent is false), and so does
`¬⟨U⟩A`.  So `[U](A → B) ⇐ ([U]A → [U]B)` and `[U]¬A ⇐ ¬[U]A` are the box's
alone, and `Fml.pushBox` keeps an antecedent and a negated part whole under
`[U]`: no direction holds of them with `U` substituted.  Where `U` cannot
halt (`Upd.total`), `Fml.push` substitutes everywhere, under either
modality, an equivalence.
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## The skeleton of a line -/

/-- The propositional skeleton of a formula, as the elaborator reads it off
a line: a connective, a literal leaf (`true`, `a ≐ b`, `defined(t)`), an
update with the skeleton under it, or a part not looked at — a
postcondition variable, a program, a quantifier, a `havoc`.  A connective
carries whether each of its parts, once rewritten, may be a formula not to
look at (`lo`, `ro`, `o`), which the folds of `Fml.concrete` read before
testing a part for `true` or `false`. -/
inductive Skel where
  | opaque
  | lit
  | and (lo ro : Bool) (l r : Skel)
  | imp (lo ro : Bool) (l r : Skel)
  | not (o : Bool) (s : Skel)
  | upd (s : Skel)
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- A connective. -/
def Skel.isConn : Skel → Bool
  | .and .. | .imp .. | .not .. => true
  | _ => false

/-- A connective somewhere, through the updates: a rewrite under a branch
has somewhere to act. -/
def Skel.hasConn : Skel → Bool
  | .and .. | .imp .. | .not .. => true
  | .upd s => s.hasConn
  | _ => false

/-- A literal leaf or a connective somewhere: a fold or a literal law has
somewhere to act. -/
def Skel.hasLit : Skel → Bool
  | .lit | .and .. | .imp .. | .not .. => true
  | .upd s => s.hasLit
  | .opaque => false

/-- The whole skeleton of a formula, every part looked at: the skeleton of
a concrete formula. -/
def Fml.skel : Fml C → Skel
  | .tt | .eq .. | .defined _ => .lit
  | .not φ => .not false φ.skel
  | .and φ ψ => .and false false φ.skel ψ.skel
  | .imp φ ψ => .imp false false φ.skel ψ.skel
  | .upd _ _ φ => .upd φ.skel
  | _ => .opaque

/-- `f` on the formula below `n` updates of the spine: `f φ` rewrites
`{U₁}…{Uₙ} φ`, and for `n = 0` the line itself. -/
def Fml.belowSpine (f : Fml C → Option (Fml C)) : Nat → Fml C → Option (Fml C)
  | 0, φ => f φ
  | i + 1, .upd m U φ => (φ.belowSpine f i).map (.upd m U)
  | _ + 1, _ => none

theorem Fml.belowSpine_holds {f : Fml C → Option (Fml C)}
    (hf : ∀ {φ ψ : Fml C}, f φ = some ψ → ∀ σ, (holds σ ψ ↔ holds σ φ)) :
    (i : Nat) → (φ : Fml C) → ∀ {ψ : Fml C}, φ.belowSpine f i = some ψ → ∀ σ,
      (holds σ ψ ↔ holds σ φ)
  | 0, _, _, h, σ => hf h σ
  | i + 1, φ, _, h, σ => by
    cases φ with
    | upd m U φ =>
      simp only [Fml.belowSpine, Option.map_eq_some_iff] at h
      obtain ⟨φ', h', rfl⟩ := h
      exact m.after_congr (fun τ => Fml.belowSpine_holds hf i φ h' τ) _
    | _ => nomatch h

/-- An update that cannot halt returns from every state. -/
theorem Upd.apply_total {U : Upd C} (hU : U.total = true) (σ : State) :
    ∃ τ, U.apply σ = .ok τ :=
  Upd.foldl_total σ U hU σ

/-- `{U}_m φ` where `U` returns `τ`: `φ` at `τ`. -/
theorem holds_upd_ok {U : Upd C} {σ τ : State} (h : U.apply σ = .ok τ) (m : Modality)
    (φ : Fml C) : holds σ (.upd m U φ) ↔ holds τ φ := by
  simp only [holds, h, Modality.after]

/-! ## `applyOnRigid` through the connectives -/

/-- `{U}_m φ` pushed through the connectives along the skeleton `s`: a
literal leaf substituted (`Fml.subst`) where it is rigid and sorted for
`U`, any other part kept under `{U}_m`. -/
def Fml.pushAlong (m : Modality) (U : Upd C) : Skel → Fml C → Fml C
  | .and _ _ l r, .and φ ψ => .and (φ.pushAlong m U l) (ψ.pushAlong m U r)
  | .imp _ _ l r, .imp φ ψ => .imp (φ.pushAlong m U l) (ψ.pushAlong m U r)
  | .not _ s, .not φ => .not (φ.pushAlong m U s)
  | .lit, φ => if (φ.rigid && φ.sortedFor U) = true then φ.subst U else .upd m U φ
  | _, φ => .upd m U φ

/-- **`applyOnRigid` through the connectives is an equivalence** where `U`
cannot halt: `U` returns one state, and each part is read there. -/
theorem Fml.pushAlong_holds {U : Upd C} (hU : U.total = true) (m : Modality) (σ : State) :
    (s : Skel) → (φ : Fml C) → (holds σ (φ.pushAlong m U s) ↔ holds σ (.upd m U φ))
  | .opaque, _ | .upd _, _ => Iff.rfl
  | .lit, φ => by
    unfold Fml.pushAlong
    split
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      exact (UpdRule.applyOnRigid hU hc.1 hc.2).sound σ
    · exact Iff.rfl
  | .and _ _ l r, φ => by
    cases φ with
    | and a b =>
      obtain ⟨τ, hτ⟩ := Upd.apply_total hU σ
      rw [holds_upd_ok hτ]
      show holds σ (a.pushAlong m U l) ∧ holds σ (b.pushAlong m U r) ↔ holds τ a ∧ holds τ b
      rw [Fml.pushAlong_holds hU m σ l a, Fml.pushAlong_holds hU m σ r b, holds_upd_ok hτ,
        holds_upd_ok hτ]
    | _ => exact Iff.rfl
  | .imp _ _ l r, φ => by
    cases φ with
    | imp a b =>
      obtain ⟨τ, hτ⟩ := Upd.apply_total hU σ
      rw [holds_upd_ok hτ]
      show (holds σ (a.pushAlong m U l) → holds σ (b.pushAlong m U r)) ↔ (holds τ a → holds τ b)
      rw [Fml.pushAlong_holds hU m σ l a, Fml.pushAlong_holds hU m σ r b, holds_upd_ok hτ,
        holds_upd_ok hτ]
    | _ => exact Iff.rfl
  | .not _ s, φ => by
    cases φ with
    | not a =>
      obtain ⟨τ, hτ⟩ := Upd.apply_total hU σ
      rw [holds_upd_ok hτ]
      show ¬ holds σ (a.pushAlong m U s) ↔ ¬ holds τ a
      rw [Fml.pushAlong_holds hU m σ s a, holds_upd_ok hτ]
    | _ => exact Iff.rfl

/-- `{U}_m φ` pushed through every connective of `φ`: KeY's `applyOnRigid`
on a formula with connectives. -/
def Fml.push (m : Modality) (U : Upd C) (φ : Fml C) : Fml C := φ.pushAlong m U φ.skel

theorem Fml.push_holds {U : Upd C} (hU : U.total = true) (m : Modality) (φ : Fml C) (σ : State) :
    holds σ (φ.push m U) ↔ holds σ (.upd m U φ) :=
  Fml.pushAlong_holds hU m σ φ.skel φ

/-- `applyOnRigid` through the connectives at the top of `{U}_m φ`: where
`U` cannot halt and `φ` is a connective, so that the line changes. -/
def Fml.pushTop (s : Skel) (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  if (U.total && s.isConn) = true then some (φ.pushAlong m U s) else none

theorem Fml.pushTop_holds {s : Skel} {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.pushTop s m U φ = some ψ) (σ : State) : holds σ ψ ↔ holds σ (.upd m U φ) := by
  unfold Fml.pushTop at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    exact Fml.pushAlong_holds hc.1 m σ s φ
  · nomatch h

/-! ## `applyOnRigid` through the connectives, under the box -/

/-- The box holds of a conjunction where it holds of each part. -/
theorem holds_box_and {U : Upd C} {σ : State} {a b : Fml C} (ha : holds σ (.upd .box U a))
    (hb : holds σ (.upd .box U b)) : holds σ (.upd .box U (.and a b)) := by
  simp only [holds] at ha hb ⊢
  generalize U.apply σ = r at ha hb ⊢
  cases r with
  | ok τ => exact ⟨ha, hb⟩
  | error _ => trivial

/-- The box holds of an implication where it holds of the consequent
whenever it holds of the antecedent. -/
theorem holds_box_imp {U : Upd C} {σ : State} {a b : Fml C}
    (h : holds σ (.upd .box U a) → holds σ (.upd .box U b)) : holds σ (.upd .box U (.imp a b)) := by
  simp only [holds] at h ⊢
  generalize U.apply σ = r at h ⊢
  cases r with
  | ok τ => exact h
  | error _ => trivial

/-- The box holds of a negation where it does not hold of the part. -/
theorem holds_box_not {U : Upd C} {σ : State} {a : Fml C} (h : ¬ holds σ (.upd .box U a)) :
    holds σ (.upd .box U (.not a)) := by
  simp only [holds] at h ⊢
  generalize U.apply σ = r at h ⊢
  cases r with
  | ok τ => exact h
  | error _ => trivial

/-- `[U] φ` pushed through the connectives along `s`, for any `U`: a
conjunction part by part, the consequent of an implication; an antecedent
and a negated part stay whole under `[U]` (the module docstring says why);
a rigid leaf is substituted as `Fml.applyOnRigidBoxTop` substitutes it. -/
def Fml.pushBoxAlong (U : Upd C) : Skel → Fml C → Fml C
  | .and _ _ l r, .and φ ψ => .and (φ.pushBoxAlong U l) (ψ.pushBoxAlong U r)
  | .imp _ _ _ r, .imp φ ψ => .imp (.upd .box U φ) (ψ.pushBoxAlong U r)
  | .not _ _, .not φ => .not (.upd .box U φ)
  | .lit, φ => (Fml.applyOnRigidBoxTop .box U φ).getD (.upd .box U φ)
  | _, φ => .upd .box U φ

/-- **`applyOnRigid` through the connectives under the box**: wherever the
pushed line holds, the box line does. -/
theorem Fml.pushBoxAlong_sound {U : Upd C} (σ : State) :
    (s : Skel) → (φ : Fml C) → holds σ (φ.pushBoxAlong U s) → holds σ (.upd .box U φ)
  | .opaque, _, h | .upd _, _, h => h
  | .lit, φ, h => by
    unfold Fml.pushBoxAlong at h
    cases hb : Fml.applyOnRigidBoxTop .box U φ with
    | some ψ =>
      rw [hb] at h
      exact Fml.applyOnRigidBoxTop_sound hb σ h
    | none =>
      rw [hb] at h
      exact h
  | .and _ _ l r, φ, h => by
    cases φ with
    | and a b =>
      exact holds_box_and (Fml.pushBoxAlong_sound σ l a h.1) (Fml.pushBoxAlong_sound σ r b h.2)
    | _ => exact h
  | .imp _ _ _ r, φ, h => by
    cases φ with
    | imp a b => exact holds_box_imp fun ha => Fml.pushBoxAlong_sound σ r b (h ha)
    | _ => exact h
  | .not _ _, φ, h => by
    cases φ with
    | not a => exact holds_box_not h
    | _ => exact h

/-- `[U] φ` pushed through every connective of `φ`. -/
def Fml.pushBox (U : Upd C) (φ : Fml C) : Fml C := φ.pushBoxAlong U φ.skel

theorem Fml.pushBox_sound (U : Upd C) (φ : Fml C) (σ : State) (h : holds σ (φ.pushBox U)) :
    holds σ (.upd .box U φ) :=
  Fml.pushBoxAlong_sound σ φ.skel φ h

/-- `applyOnRigid` through the connectives at the top of `[U] φ`, `φ` a
connective: the box only. -/
def Fml.pushBoxTop (s : Skel) (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  if (decide (m = .box) && s.isConn) = true then some (φ.pushBoxAlong U s) else none

theorem Fml.pushBoxTop_sound {s : Skel} {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.pushBoxTop s m U φ = some ψ) (σ : State) (hψ : holds σ ψ) : holds σ (.upd m U φ) := by
  unfold Fml.pushBoxTop at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨rfl, -⟩ := hc
    exact Fml.pushBoxAlong_sound σ s φ hψ
  · nomatch h

/-! ## The concrete folds

KeY's `concrete` rules: `true ∧ φ ⇝ φ`, `false → φ ⇝ true`, `¬false ⇝ true`,
and the closing of a literal equation (`eqClose` on two literals, with
`defined(v) ⇝ true` for a literal `v`); `false` is `¬true` here, so
`concrete_not_1` rewrites nothing.  Each fold tests a part for `true` or
`false` only where the skeleton says the part is one to look at. -/

/-- `true`. -/
def Fml.isTT : Fml C → Bool
  | .tt => true
  | _ => false

/-- `false`, which is `¬true`. -/
def Fml.isFF : Fml C → Bool
  | .not .tt => true
  | _ => false

theorem Fml.eq_tt_of_isTT : {φ : Fml C} → φ.isTT = true → φ = .tt
  | .tt, _ => rfl

theorem Fml.eq_ff_of_isFF : {φ : Fml C} → φ.isFF = true → φ = .not .tt
  | .not .tt, _ => rfl

/-- `φ ∧ ψ` folded: `concrete_and_1-4`.  `lo`, `ro`: a part not to look at. -/
def Fml.andC (lo ro : Bool) (φ ψ : Fml C) : Fml C :=
  if (!lo && φ.isTT) = true then ψ
  else if (!lo && φ.isFF) = true then .ff
  else if (!ro && ψ.isTT) = true then φ
  else if (!ro && ψ.isFF) = true then .ff
  else .and φ ψ

/-- `φ → ψ` folded: `concrete_impl_1-4`. -/
def Fml.impC (lo ro : Bool) (φ ψ : Fml C) : Fml C :=
  if (!lo && φ.isTT) = true then ψ
  else if (!lo && φ.isFF) = true then .tt
  else if (!ro && ψ.isTT) = true then .tt
  else if (!ro && ψ.isFF) = true then .not φ
  else .imp φ ψ

/-- `¬φ` folded: `concrete_not_2`. -/
def Fml.notC (o : Bool) (φ : Fml C) : Fml C :=
  if (!o && φ.isFF) = true then .tt else .not φ

/-- A literal leaf folded: two literals compared (`eqClose`), a literal
defined. -/
def Fml.litC : Fml C → Fml C
  | .eq (.lit v) (.lit w) => if v = w then .tt else .ff
  | .defined (.lit _) => .tt
  | φ => φ

/-- Whether a fold fires on `φ ∧ ψ` or `φ → ψ`: a part looked at is `true` or `false`. -/
def Fml.connFires (lo ro : Bool) (φ ψ : Fml C) : Bool :=
  (!lo && (φ.isTT || φ.isFF)) || (!ro && (ψ.isTT || ψ.isFF))

/-- Whether a fold fires on `¬φ`. -/
def Fml.notFires (o : Bool) (φ : Fml C) : Bool := !o && φ.isFF

/-- Whether a fold fires on a literal leaf. -/
def Fml.litFires : Fml C → Bool
  | .eq (.lit _) (.lit _) | .defined (.lit _) => true
  | _ => false

theorem Fml.andC_holds (lo ro : Bool) (φ ψ : Fml C) (σ : State) :
    holds σ (φ.andC lo ro ψ) ↔ (holds σ φ ∧ holds σ ψ) := by
  unfold Fml.andC
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_tt_of_isTT h.2
    simp only [holds, true_and]
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_ff_of_isFF h.2
    simp only [holds, not_true_eq_false, false_and]
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_tt_of_isTT h.2
    simp only [holds, and_true]
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_ff_of_isFF h.2
    simp only [holds, not_true_eq_false, and_false]
  exact Iff.rfl

theorem Fml.impC_holds (lo ro : Bool) (φ ψ : Fml C) (σ : State) :
    holds σ (φ.impC lo ro ψ) ↔ (holds σ φ → holds σ ψ) := by
  unfold Fml.impC
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_tt_of_isTT h.2
    simp only [holds, true_implies]
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_ff_of_isFF h.2
    simp only [holds, not_true_eq_false, false_implies]
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_tt_of_isTT h.2
    simp only [holds, implies_true]
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_ff_of_isFF h.2
    simp only [holds, not_true_eq_false, imp_false]
  exact Iff.rfl

theorem Fml.notC_holds (o : Bool) (φ : Fml C) (σ : State) :
    holds σ (φ.notC o) ↔ ¬ holds σ φ := by
  unfold Fml.notC
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_ff_of_isFF h.2
    simp only [holds, not_true_eq_false, not_false_eq_true]
  exact Iff.rfl

theorem Fml.litC_holds (φ : Fml C) (σ : State) : holds σ φ.litC ↔ holds σ φ := by
  unfold Fml.litC
  split
  · rename_i v w
    split
    · rename_i hvw
      subst hvw
      simp only [holds, true_iff]
      exact Theory.StValue.Equiv.refl _
    · rename_i hvw
      simp only [holds, not_true_eq_false, false_iff]
      intro h
      exact hvw (Theory.StValue.prim.inj (Theory.StValue.Equiv.prim_iff.1 h))
  · rename_i v
    simp only [holds, true_iff]
    exact ⟨v, rfl⟩
  · exact Iff.rfl

/-- The folds, bottom-up along the skeleton `s`. -/
def Fml.concreteAlong : Skel → Fml C → Fml C
  | .and lo ro l r, .and φ ψ => Fml.andC lo ro (φ.concreteAlong l) (ψ.concreteAlong r)
  | .imp lo ro l r, .imp φ ψ => Fml.impC lo ro (φ.concreteAlong l) (ψ.concreteAlong r)
  | .not o s, .not φ => Fml.notC o (φ.concreteAlong s)
  | .lit, φ => φ.litC
  | _, φ => φ

/-- Whether some fold fires along `s`. -/
def Fml.concretesAlong : Skel → Fml C → Bool
  | .and lo ro l r, .and φ ψ =>
    φ.concretesAlong l || ψ.concretesAlong r ||
      Fml.connFires lo ro (φ.concreteAlong l) (ψ.concreteAlong r)
  | .imp lo ro l r, .imp φ ψ =>
    φ.concretesAlong l || ψ.concretesAlong r ||
      Fml.connFires lo ro (φ.concreteAlong l) (ψ.concreteAlong r)
  | .not o s, .not φ => φ.concretesAlong s || Fml.notFires o (φ.concreteAlong s)
  | .lit, φ => φ.litFires
  | _, _ => false

/-- **The folds are equivalences.** -/
theorem Fml.concreteAlong_holds (σ : State) :
    (s : Skel) → (φ : Fml C) → (holds σ (φ.concreteAlong s) ↔ holds σ φ)
  | .opaque, _ | .upd _, _ => Iff.rfl
  | .lit, φ => Fml.litC_holds φ σ
  | .and lo ro l r, φ => by
    cases φ with
    | and a b =>
      simp only [Fml.concreteAlong, Fml.andC_holds, Fml.concreteAlong_holds σ l a,
        Fml.concreteAlong_holds σ r b, holds]
    | _ => exact Iff.rfl
  | .imp lo ro l r, φ => by
    cases φ with
    | imp a b =>
      simp only [Fml.concreteAlong, Fml.impC_holds, Fml.concreteAlong_holds σ l a,
        Fml.concreteAlong_holds σ r b, holds]
    | _ => exact Iff.rfl
  | .not o s, φ => by
    cases φ with
    | not a => simp only [Fml.concreteAlong, Fml.notC_holds, Fml.concreteAlong_holds σ s a, holds]
    | _ => exact Iff.rfl

/-- KeY's `concrete` folds on the whole skeleton of `φ`. -/
def Fml.concrete (φ : Fml C) : Fml C := φ.concreteAlong φ.skel

theorem Fml.concrete_holds (φ : Fml C) (σ : State) : holds σ φ.concrete ↔ holds σ φ :=
  Fml.concreteAlong_holds σ φ.skel φ

/-- The folds along `s`, if one fires. -/
def Fml.concreteOn (s : Skel) (φ : Fml C) : Option (Fml C) :=
  if φ.concretesAlong s then some (φ.concreteAlong s) else none

theorem Fml.concreteOn_holds {s : Skel} {φ ψ : Fml C} (h : φ.concreteOn s = some ψ) (σ : State) :
    holds σ ψ ↔ holds σ φ := by
  unfold Fml.concreteOn at h
  split at h
  · cases h; exact Fml.concreteAlong_holds σ s φ
  · nomatch h

/-- The folds along `s` below `n` updates, if one fires. -/
def Fml.concreteBelow (n : Nat) (s : Skel) : Fml C → Option (Fml C) :=
  Fml.belowSpine (Fml.concreteOn s) n

/-- The folds on the whole skeleton below `n` updates, if one fires. -/
def Fml.concreteAt (n : Nat) : Fml C → Option (Fml C) :=
  Fml.belowSpine (fun φ => φ.concreteOn φ.skel) n

/-! ## A rewrite under a branch -/

/-- `f` at the first node of the skeleton where it gives a line: the node
itself, then under its update, its `¬`, the left part of its `∧` or `→`
then the right; never a part the skeleton does not look at. -/
def Fml.inSkeletonAlong (f : Fml C → Option (Fml C)) : Skel → Fml C → Option (Fml C)
  | .opaque, _ => none
  | .lit, φ => f φ
  | .upd s, φ => f φ <|> match φ with
    | .upd m U ψ => (ψ.inSkeletonAlong f s).map (.upd m U)
    | _ => none
  | .not _ s, φ => f φ <|> match φ with
    | .not ψ => (ψ.inSkeletonAlong f s).map .not
    | _ => none
  | .and _ _ l r, φ => f φ <|> match φ with
    | .and a b => (a.inSkeletonAlong f l).map (.and · b) <|> (b.inSkeletonAlong f r).map (.and a ·)
    | _ => none
  | .imp _ _ l r, φ => f φ <|> match φ with
    | .imp a b => (a.inSkeletonAlong f l).map (.imp · b) <|> (b.inSkeletonAlong f r).map (.imp a ·)
    | _ => none

theorem Option.or_eq_some_iff' {α : Type} {a b : Option α} {x : α} :
    a.or b = some x ↔ a = some x ∨ (a = none ∧ b = some x) := by
  cases a with
  | some y => simp only [Option.some_or, Option.some.injEq, reduceCtorEq, false_and, or_false]
  | none => simp only [Option.none_or, reduceCtorEq, true_and, false_or]

/-- **An equivalence at one node is one of the line.** -/
theorem Fml.inSkeletonAlong_holds {f : Fml C → Option (Fml C)}
    (hf : ∀ {φ ψ : Fml C}, f φ = some ψ → ∀ σ, (holds σ ψ ↔ holds σ φ)) :
    (s : Skel) → (φ : Fml C) → ∀ {ψ : Fml C}, φ.inSkeletonAlong f s = some ψ → ∀ σ,
      (holds σ ψ ↔ holds σ φ)
  | .opaque, _, _, h, _ => nomatch h
  | .lit, _, _, h, σ => hf h σ
  | .upd s, φ, ψ, h, σ => by
    simp only [Fml.inSkeletonAlong, Option.orElse_eq_orElse, Option.orElse_eq_or] at h
    rcases Option.or_eq_some_iff'.1 h with h | ⟨-, h⟩
    · exact hf h σ
    · cases φ with
      | upd m U χ =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨χ', h', rfl⟩ := h
        exact m.after_congr (fun τ => Fml.inSkeletonAlong_holds hf s χ h' τ) _
      | _ => nomatch h
  | .not _ s, φ, ψ, h, σ => by
    simp only [Fml.inSkeletonAlong, Option.orElse_eq_orElse, Option.orElse_eq_or] at h
    rcases Option.or_eq_some_iff'.1 h with h | ⟨-, h⟩
    · exact hf h σ
    · cases φ with
      | not χ =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨χ', h', rfl⟩ := h
        simp only [holds, Fml.inSkeletonAlong_holds hf s χ h' σ]
      | _ => nomatch h
  | .and _ _ l r, φ, ψ, h, σ => by
    simp only [Fml.inSkeletonAlong, Option.orElse_eq_orElse, Option.orElse_eq_or] at h
    rcases Option.or_eq_some_iff'.1 h with h | ⟨-, h⟩
    · exact hf h σ
    · cases φ with
      | and a b =>
        rcases Option.or_eq_some_iff'.1 h with h | ⟨-, h⟩
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨a', h', rfl⟩ := h
          simp only [holds, Fml.inSkeletonAlong_holds hf l a h' σ]
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨b', h', rfl⟩ := h
          simp only [holds, Fml.inSkeletonAlong_holds hf r b h' σ]
      | _ => nomatch h
  | .imp _ _ l r, φ, ψ, h, σ => by
    simp only [Fml.inSkeletonAlong, Option.orElse_eq_orElse, Option.orElse_eq_or] at h
    rcases Option.or_eq_some_iff'.1 h with h | ⟨-, h⟩
    · exact hf h σ
    · cases φ with
      | imp a b =>
        rcases Option.or_eq_some_iff'.1 h with h | ⟨-, h⟩
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨a', h', rfl⟩ := h
          simp only [holds, Fml.inSkeletonAlong_holds hf l a h' σ]
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨b', h', rfl⟩ := h
          simp only [holds, Fml.inSkeletonAlong_holds hf r b h' σ]
      | _ => nomatch h

/-- `f` at the first node of the whole skeleton of `φ` where it gives a line. -/
def Fml.inSkeleton (f : Fml C → Option (Fml C)) (φ : Fml C) : Option (Fml C) :=
  φ.inSkeletonAlong f φ.skel

theorem Fml.inSkeleton_holds {f : Fml C → Option (Fml C)}
    (hf : ∀ {φ ψ : Fml C}, f φ = some ψ → ∀ σ, (holds σ ψ ↔ holds σ φ)) {φ ψ : Fml C}
    (h : φ.inSkeleton f = some ψ) (σ : State) : holds σ ψ ↔ holds σ φ :=
  Fml.inSkeletonAlong_holds hf φ.skel φ h σ

/-! ## The rewrites, bundled -/

namespace LineRw

/-- `applyOnRigid` through the connectives of the formula under the update
at position `i`, whose skeleton is `s`, where the update cannot halt. -/
def applyOnRigidIn (i : Nat) (s : Skel) : LineRw C :=
  ⟨Fml.atSpine (Fml.pushTop s) i, Fml.atSpine_sound (fun h σ => (Fml.pushTop_holds h σ).1) i _⟩

/-- `applyOnRigid` through the connectives of the formula under the box
update at position `i`, whose skeleton is `s`: one direction, any update. -/
def applyOnRigidBoxIn (i : Nat) (s : Skel) : LineRw C :=
  ⟨Fml.atSpine (Fml.pushBoxTop s) i, Fml.atSpine_sound Fml.pushBoxTop_sound i _⟩

/-- KeY's `concrete` folds below `n` updates, along the skeleton `s`. -/
def concrete (n : Nat) (s : Skel) : LineRw C :=
  ⟨Fml.concreteBelow n s,
    fun h σ => (Fml.belowSpine_holds (fun h σ => Fml.concreteOn_holds h σ) n _ h σ).1⟩

/-- `sequentialToParallel` on the first `n + 1` updates of the first spine
the skeleton `s` finds, under a branch. -/
def mergeIn (n : Nat) (s : Skel) : LineRw C :=
  ⟨Fml.inSkeletonAlong (Fml.mergeSpine n) s,
    fun h σ => (Fml.inSkeletonAlong_holds (fun h σ => Fml.mergeSpine_holds n _ h σ) s _ h σ).1⟩

end LineRw

end Solidity
