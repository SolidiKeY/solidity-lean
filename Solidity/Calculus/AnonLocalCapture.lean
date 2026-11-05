import Solidity.Calculus.CallResultCapture

/-! # Anonymous primitive values through fresh intrinsic locals

Each primitive position is universally bound at a fresh head, copied into
its original position, and popped before the next position. No RHS or
postcondition is substituted into another term. Repeated positions and
order remain explicit. This module supplies a sound leaf transformation;
it does not claim call-family compression.
-/
namespace Solidity.AnonLocalCapture
variable {C : Contract} {Γ : Ctx}

/-- Primitive positions in one original intrinsic context. -/
abbrev Positions (Γ : Ctx) := List ((p : PrimTy) × Idx Γ (.val p))

/-- The exact original anonymous positions, including repetitions. -/
def keys (xs : Positions Γ) : List ((t : LTy) × Idx Γ t) :=
  xs.map (fun x => ⟨.val x.1, x.2⟩)

/-- Fresh positional binding, copy and pop; every continuation stays in Γ. -/
def plan (m : Modality) (names : Nat → Var) (k : Nat)
    (xs : Positions Γ) (φ : Fml C Γ) : Fml C Γ :=
  match xs with
  | [] => φ
  | ⟨p, j⟩ :: rest => .bind m (names k) (.val p)
      (.upd m (CallResultCapture.restore j) (plan m names (k+1) rest φ))

/-- Validity of the fresh-local plan establishes the actual anonymous leaf,
for both modalities, every original state and every postcondition. -/
theorem sound (m : Modality) (names : Nat → Var) (k : Nat)
    (xs : Positions Γ) (φ : Fml C Γ) (σ : State C Γ)
    (hh : holds σ (plan m names k xs φ)) : holds σ (.anon (keys xs) φ) := by
  induction xs generalizing k σ with
  | nil => intro b; exact hh
  | cons x xs ih =>
    rcases x with ⟨p, j⟩
    change ∀ b, holds (σ.anon (⟨.val p, j⟩ :: keys xs) b) φ
    intro b
    let v : p.Denote := b ⟨.val p, j⟩
    have hc : Upd.afterT m (σ.push (t := .val p) v) (CallResultCapture.restore j)
        (fun τ => holds τ (plan m names (k+1) xs φ)) :=
      Modality.forallB_all hh v
    rw [Upd.afterT_applyV, CallResultCapture.restore_applyV] at hc
    have he : (σ.setLocal j v).locV = σ.locV.set j v := State.locV_setLocal σ j v
    have hp : holds (σ.setLocal j v) (plan m names (k+1) xs φ) :=
      hc (σ.setLocal j v) rfl (fun {u} i => congrFun (congrFun he u) i)
    have hr : holds (σ.setLocal j v) (.anon (keys xs) φ) := ih (k+1) (σ.setLocal j v) hp
    exact hr b

/-- Count the complete emitted bind/copy/pop syntax and the unchanged post once. -/
theorem plan_size (m : Modality) (names : Nat → Var) (k : Nat)
    (xs : Positions Γ) (φ : Fml C Γ) :
    (plan m names k xs φ).tmSize = φ.tmSize + 4 * xs.length := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨p, j⟩
    change 1 + (1 + 2 + (plan m names (k+1) xs φ).tmSize) = _
    rw [ih]
    simp only [List.length_cons]
    omega

end Solidity.AnonLocalCapture
