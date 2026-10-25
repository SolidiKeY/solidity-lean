import Solidity.Calculus.Blocks

/-!
# A weakening's scope ends, and a loop body's frame: the syntax

What the runs' weakening and frame lemmas read of the syntax alone, kept
apart from the runs so that the typed ones
(`Semantics/RunWk.lean`, `Semantics/RunFrame.lean`)
need neither M3 run.  `Thin.Over e h e' h'` says that `e'` pops on `Δ` what
`e` pops on `Γ`, the thinning kept over it, which a weakened statement does
(`Stmt.wk_over`, `Prog.wk_over`); `Prog.frame_some` reads a loop body's
frame (`Prog.frame`, `Calculus/Blocks.lean`) as its mutability, its modifies
set and the locals it may write.
-/

namespace Solidity

open Solidity (Mutability)

variable {C : Contract}

/-! ## A scope's end on both sides -/

/-- `e'` pops on `Δ` what `e` pops on `Γ`, the thinning kept over it. -/
inductive Thin.Over : {Γ Γ' Δ Δ' : Ctx} → Ext Γ Γ' → Thin Γ Δ → Ext Δ Δ' → Thin Γ' Δ' → Prop
  | refl {Γ Δ : Ctx} (h : Thin Γ Δ) : Thin.Over .refl h .refl h
  | push {Γ Γ' Δ Δ' : Ctx} {t : LTy} {e : Ext Γ Γ'} {h : Thin Γ Δ} {e' : Ext Δ Δ'}
      {h' : Thin Γ' Δ'} : Thin.Over e h e' h' → Thin.Over (.push (t := t) e) h (.push e') (.keep h')

namespace Thin.Over

theorem trans {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ : Ctx} {e₁ : Ext Γ Γ₁} {h : Thin Γ Δ} {e₁' : Ext Δ Δ₁}
    {h₁ : Thin Γ₁ Δ₁} {e₂ : Ext Γ₁ Γ₂} {e₂' : Ext Δ₁ Δ₂} {h₂ : Thin Γ₂ Δ₂}
    (ho₁ : Thin.Over e₁ h e₁' h₁) (ho₂ : Thin.Over e₂ h₁ e₂' h₂) :
    Thin.Over (e₁.trans e₂) h (e₁'.trans e₂') h₂ := by
  induction ho₂ with
  | refl => exact ho₁
  | push _ ih => exact .push (ih ho₁)

theorem append {Γ Δ : Ctx} (h : Thin Γ Δ) :
    (ρ : Ctx) → Thin.Over (Ext.append Γ ρ) h (Ext.append Δ ρ) (Thin.keepAll ρ h)
  | [] => .refl h
  | _ :: ρ => .push (append h ρ)

end Thin.Over

/-! ## A weakened statement pops what it popped -/

theorem CallRet.wk_over {Γ Δ : Ctx} (h : Thin Γ Δ) {rs Γ' : Ctx} (ret : CallRet Γ rs Γ') :
    Thin.Over ret.ext h (ret.wk h).2.2.ext (ret.wk h).2.1 := by
  cases ret with
  | none => exact .refl h
  | val => exact .refl h
  | rets bs => exact Thin.Over.append h _
  | mem => exact .push (.refl h)
  | storage => exact .push (.refl h)

theorem Stmt.wk_over {Γ Γ' Δ : Ctx} (h : Thin Γ Δ) (s : Stmt C Γ Γ') :
    Thin.Over s.ext h (s.wk h).2.2.ext (s.wk h).2.1 := by
  cases s <;> first | exact .refl h | exact .push (.refl h) | exact CallRet.wk_over h _

theorem Prog.wk_over : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → ∀ {Δ : Ctx} (h : Thin Γ Δ),
    Thin.Over P.ext h (P.wk h).2.2.ext (P.wk h).2.1
  | _, _, .nil, _, h => .refl h
  | _, _, .cons s P, _, h => (Stmt.wk_over h s).trans (Prog.wk_over P (s.wk h).2.1)

/-! ## A loop body's frame -/

section Frame

variable {Γ : Ctx}

/-- **A body with a frame** is within no mutability, its frame writing no
storage, or within `nonpayable`, its frame its modifies set
(`Prog.storeAt`); and its frame lists every local of the loop's context it
may write. -/
theorem Prog.frame_some {Γ₁ : Ctx} {P : Prog C Γ Γ₁} {xs : List ((t : LTy) × Idx Γ t)}
    {hv : Option (List Name)} (h : P.frame = some (xs, hv)) :
    (Prog.within .view P = true ∧ hv = some [] ∨
        Prog.within .nonpayable P = true ∧ hv = Prog.storeAt P) ∧
      ∀ t (i : Idx Γ t), (t, i.toNat) ∈ Prog.writesAt 0 P → (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs := by
  unfold Prog.frame at h
  have hxs : ∀ ys : List ((t : LTy) × Idx Γ t),
      ys = (Prog.writesAt 0 P).filterMap (fun (tn : LTy × Nat) => (Γ.idx? tn.2 tn.1).map (⟨tn.1, ·⟩)) →
      ∀ t (i : Idx Γ t), (t, i.toNat) ∈ Prog.writesAt 0 P → (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ ys := by
    intro ys hys t i hm
    rw [hys, List.mem_filterMap]
    exact ⟨(t, i.toNat), hm, by simp only [Ctx.idx?_toNat, Option.map_some]⟩
  split at h
  · cases h
    exact ⟨.inl ⟨by assumption, rfl⟩, hxs _ rfl⟩
  · split at h
    · cases h
      exact ⟨.inr ⟨by assumption, rfl⟩, hxs _ rfl⟩
    · cases h

/-- A body with a frame is within a mutability. -/
theorem Prog.frame_within {Γ₁ : Ctx} {P : Prog C Γ Γ₁} {xs : List ((t : LTy) × Idx Γ t)}
    {hv : Option (List Name)} (h : P.frame = some (xs, hv)) : ∃ μ, Prog.within μ P = true := by
  rcases (Prog.frame_some h).1 with ⟨hw, -⟩ | ⟨hw, -⟩
  · exact ⟨_, hw⟩
  · exact ⟨_, hw⟩

end Frame

end Solidity
