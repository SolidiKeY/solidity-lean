import Solidity.Calculus.LeafInputs

/-!
# Positive quantifiers moved to the prefix

A specification's `\forall` in a postcondition leaves the eliminated leaf
as `pre → ∀ k. post`, which the universal prefix (`UniversalPrefix`) does
not reach.  `LFml.prenex` moves a universal quantifier out of the
consequent of an implication, `φ → ∀ k. ψ` to `∀ k. (φ → ψ)`, when `φ`
reads no `k`, and keeps the formula otherwise: exact in every valuation
(`LFml.prenex_holds`).  A quantifier in an antecedent, or under a
negation, is an `∃` of the leaf and stays where it is.  On a leaf with no
quantifier in a consequent `LFml.prenex` is the identity.

`LFml`'s family has no index, so its recursion is `match`-based (Gate G0).
-/

namespace Solidity.Decide

variable {C : Contract}

/-- `φ → ψ`, the leading quantifiers of `ψ` that `φ` does not read moved
in front. -/
def LFml.pullImp (φ : LFml C) : LFml C → LFml C
  | .all k p ψ =>
    if (⟨p, k⟩ : Parameter) ∈ φ.parameters then .imp φ (.all k p ψ) else .all k p (φ.pullImp ψ)
  | ψ => .imp φ ψ

/-- **The leaf with its consequents' quantifiers in front.** -/
def LFml.prenex : LFml C → LFml C
  | .imp φ ψ => φ.pullImp ψ.prenex
  | .all k p ψ => .all k p ψ.prenex
  | φ => φ

theorem Parameters.Agree.set {ps : List Parameter} {ν μ : AEnv} (h : Parameters.Agree ps ν μ)
    (p : PrimTy) (k : Nat) (v : p.Denote) : Parameters.Agree ps (ν.set p k v) (μ.set p k v) := by
  intro q hq
  by_cases he : q = ⟨p, k⟩
  · subst he
    exact (Parameter.read_set ⟨p, k⟩ ν v).trans (Parameter.read_set ⟨p, k⟩ μ v).symm
  · exact (Parameter.read_set_ne q ⟨p, k⟩ he ν v).trans
      ((h q hq).trans (Parameter.read_set_ne q ⟨p, k⟩ he μ v).symm)

/-- A formula reads only its atoms. -/
theorem LFml.holds_agree (g : State C []) :
    ∀ (φ : LFml C) {ν μ : AEnv}, Parameters.Agree φ.parameters ν μ → (φ.holds g ν ↔ φ.holds g μ)
  | .tt, _, _, _ => Iff.rfl
  | @LFml.eq _ p a b, ν, μ, h => by
    have ha : (a.eval g ν : Option p.Denote) = a.eval g μ := a.eval_agree_parameters g h.left
    have hb : (b.eval g ν : Option p.Denote) = b.eval g μ := b.eval_agree_parameters g h.right
    simp only [LFml.holds, ha, hb]
  | .not φ, _, _, h => not_congr (LFml.holds_agree g φ h)
  | .and φ ψ, _, _, h => and_congr (LFml.holds_agree g φ h.left) (LFml.holds_agree g ψ h.right)
  | .imp φ ψ, _, _, h => imp_congr (LFml.holds_agree g φ h.left) (LFml.holds_agree g ψ h.right)
  | .all k p φ, _, _, h => forall_congr' fun v => LFml.holds_agree g φ (h.set p k v)

/-- A formula that reads no `k` holds alike whatever `k` holds. -/
theorem LFml.holds_set_of_not_mem (g : State C []) (φ : LFml C) (ν : AEnv) (p : PrimTy) (k : Nat)
    (v : p.Denote) (h : (⟨p, k⟩ : Parameter) ∉ φ.parameters) :
    φ.holds g (ν.set p k v) ↔ φ.holds g ν :=
  LFml.holds_agree g φ fun q hq =>
    Parameter.read_set_ne q ⟨p, k⟩ (fun he => h (he ▸ hq)) ν v

theorem LFml.pullImp_holds (g : State C []) (φ : LFml C) :
    ∀ (ψ : LFml C) (ν : AEnv), (φ.pullImp ψ).holds g ν ↔ (LFml.imp φ ψ).holds g ν
  | .all k p ψ, ν => by
    unfold LFml.pullImp
    split
    · exact Iff.rfl
    · rename_i hm
      show (∀ v, (φ.pullImp ψ).holds g (ν.set p k v)) ↔ (φ.holds g ν → ∀ v, ψ.holds g (ν.set p k v))
      simp only [LFml.pullImp_holds g φ ψ, LFml.holds, LFml.holds_set_of_not_mem g φ ν p k _ hm]
      exact ⟨fun h hφ v => h v hφ, fun h v hφ => h hφ v⟩
  | .tt, _ | .eq _ _, _ | .not _, _ | .and _ _, _ | .imp _ _, _ => Iff.rfl

/-- **Prenexing is exact.** -/
theorem LFml.prenex_holds (g : State C []) : ∀ (φ : LFml C) (ν : AEnv), φ.prenex.holds g ν ↔ φ.holds g ν
  | .imp φ ψ, ν => by
    show (φ.pullImp ψ.prenex).holds g ν ↔ _
    rw [LFml.pullImp_holds]
    exact imp_congr Iff.rfl (LFml.prenex_holds g ψ ν)
  | .all k p ψ, ν => forall_congr' fun v => LFml.prenex_holds g ψ (ν.set p k v)
  | .tt, _ | .eq _ _, _ | .not _, _ | .and _ _, _ => Iff.rfl

end Solidity.Decide
