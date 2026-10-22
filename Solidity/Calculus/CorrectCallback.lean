import Solidity.Calculus.Correct
import Solidity.Calculus.CallbackHolds

/-!
# Correctness statements with callbacks

`Spec.satC` reads the same statements as `Spec.sat`, but modalities quantify
all `ExecP` outcomes, including broken invariants. Equations still require
successful evaluation of both operands. `Spec.satC_iff_holdsC` relates this
direct reading to the translated formula; no frames or updates occur in the
definition of correctness. The invariant and transfer-callback policy are
explicit, as they are for the callback calculus.
-/

namespace Solidity

variable {C : Contract}

namespace Spec

/-- A statement read over every callback execution. For example, a value
call may change the storage and balance before its postcondition is read. -/
def satC (I : Invariant C) (pay : Bool) : {Γ : Ctx} → State C Γ → Spec C Γ → Prop
  | _, _, .tt => True
  | _, σ, .eq a b => ∃ v, a.eval σ = some v ∧ b.eval σ = some v
  | _, σ, .wellFormed s => ∃ st, s.eval σ = some st ∧ st.wtB = true
  | _, σ, .not φ => ¬ satC I pay σ φ
  | _, σ, .and φ ψ => satC I pay σ φ ∧ satC I pay σ ψ
  | _, σ, .imp φ ψ => satC I pay σ φ → satC I pay σ ψ
  | _, σ, .all _ t φ => ∀ v : t.TDenote C σ.H, satC I pay (σ.push v) φ
  | _, σ, .box P φ =>
    ∀ o, ExecP (I.fml.stateInv pay) σ P o → o.after .box (satC I pay · φ)
  | _, σ, .diamond P φ =>
    ∀ o, ExecP (I.fml.stateInv pay) σ P o → o.after .diamond (satC I pay · φ)

/-- Correct in every state under the stated callback invariant and policy. -/
def ValidC (I : Invariant C) (φ : Spec C []) (pay : Bool := true) : Prop :=
  ∀ σ : State C [], satC I pay σ φ

private theorem after_iff {H : HTy} {Γ : Ctx} (m : Modality)
    {p q : State C Γ → Prop} (hpq : ∀ τ, p τ ↔ q τ) (o : COut C H Γ) :
    o.after m p ↔ o.after m q := by
  cases o with
  | ok o => exact hpq o.st
  | halt e => rfl
  | violated => rfl

private theorem after_nil {H : HTy} {Γ : Ctx} (J : StateInv C) (m : Modality)
    (p : State C Γ → Prop) (o : COut C H Γ) :
    o.after m p ↔ o.thenF J .nil m p := by
  cases o with
  | ok o =>
    exact ⟨fun hp _ he => by cases he; exact hp, fun h => h _ .nil⟩
  | halt e => rfl
  | violated => rfl

/-- The direct statement semantics agree with their formula translation,
including arbitrary storage and balance left by callbacks. -/
theorem satC_iff_holdsC {Γ : Ctx} (I : Invariant C) (pay : Bool)
    (φ : Spec C Γ) (σ : State C Γ) :
    satC I pay σ φ ↔ holdsC I.fml pay σ φ.toFml := by
  induction φ with
  | box P φ ih =>
    simp only [satC, toFml, holdsC]
    exact forall_congr' fun o =>
      ⟨fun h he => (after_nil _ _ _ o).mp ((after_iff .box ih o).mp (h he)),
        fun h he => (after_iff .box ih o).mpr ((after_nil _ _ _ o).mpr (h he))⟩
  | diamond P φ ih =>
    simp only [satC, toFml, holdsC]
    exact forall_congr' fun o =>
      ⟨fun h he => (after_nil _ _ _ o).mp ((after_iff .diamond ih o).mp (h he)),
        fun h he => (after_iff .diamond ih o).mpr ((after_nil _ _ _ o).mpr (h he))⟩
  | tt => rfl
  | eq a b =>
    exact (Fml.holds_evalEq σ a b).symm.trans
      (holdsC_iff_holds (Fml.evalEq a b) rfl σ).symm
  | wellFormed s => rfl
  | not φ ih => exact not_congr (ih σ)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ σ) (ihψ σ)
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ σ) (ihψ σ)
  | all x t φ ih => exact forall_congr' fun v => ih (σ.push v)

/-- Callback validity is exactly validity of the translated formula. -/
theorem validC_iff (I : Invariant C) (φ : Spec C []) (pay : Bool) :
    ValidC I φ pay ↔ Solidity.ValidC I φ.toFml pay :=
  ⟨fun h σ => (satC_iff_holdsC I pay φ σ).mp (h σ),
    fun h σ => (satC_iff_holdsC I pay φ σ).mpr (h σ)⟩

/-- With no callback sites, both direct readings agree. -/
theorem satC_iff_sat {Γ : Ctx} (I : Invariant C) (pay : Bool) (φ : Spec C Γ)
    (hn : φ.toFml.callsBack pay = false) (σ : State C Γ) :
    satC I pay σ φ ↔ sat σ φ :=
  (satC_iff_holdsC I pay φ σ).trans
    ((holdsC_iff_holds φ.toFml hn σ).trans (sat_iff_holds φ σ).symm)

end Spec

notation:25 "⊨[" I "] " φ:26 => Spec.ValidC I φ true
notation:25 "⊨ₙ[" I "] " φ:26 => Spec.ValidC I φ false

/-- info: 'Solidity.Spec.satC_iff_holdsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.satC_iff_holdsC

end Solidity
