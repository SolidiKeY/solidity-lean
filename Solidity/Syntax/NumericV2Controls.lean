import Solidity.Syntax.NumericV2Correct

/-! Regression controls: magnitude overflow must reach the exact panic statement,
not v1's bare revert. Successful unchanged state is component-local only. -/
namespace Solidity.Val.NumericV2.Controls

abbrev signed {C : Contract} {Γ : Ctx} (n : Int)
    (valid : PrimTy.int.inRange n = true) : Val C Γ .int := .simple (.lit n valid)
abbrev unsigned {C : Contract} {Γ : Ctx} (n : Int)
    (valid : PrimTy.uint.inRange n = true) : Val C Γ .uint := .simple (.lit n valid)

theorem magnitude_overflow_guard {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    (powerFits (signed ((2^128 : Nat) : Int) (by decide))
      (unsigned 2 (by decide))).evalT σ = .ok false := by rfl

theorem exact_magnitude_overflow {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    (checkedSignedPower (signed ((2^128 : Nat) : Int) (by decide))
      (unsigned 2 (by decide))).1.run σ =
        .error (THalt.ofData (Semantics.encodePanic 0x11)) := by
  exact guard_run σ _ false (magnitude_overflow_guard σ)

theorem v1_bare_revert {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    (Val.checkedSignedPower (signed ((2^128 : Nat) : Int) (by decide))
      (unsigned 2 (by decide))).evalT σ = .error .revert := by rfl

theorem exact_not_bare {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    (checkedSignedPower (signed ((2^128 : Nat) : Int) (by decide))
      (unsigned 2 (by decide))).1.run σ ≠ .error .revert := by
  rw [exact_magnitude_overflow]
  intro impossible
  cases impossible

theorem signed_edges {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    (powerFits (signed (-2) (by decide)) (unsigned 255 (by decide))).evalT σ = .ok true ∧
    (powerFits (signed 2 (by decide)) (unsigned 255 (by decide))).evalT σ = .ok false ∧
    (powerFits (signed (-2) (by decide)) (unsigned 256 (by decide))).evalT σ = .ok false := by
  refine ⟨?_,?_,?_⟩
  · rw [powerFits_eval_model σ _ _ ⟨-2,by decide⟩ ⟨255,by decide⟩ rfl rfl]
    congr 1
  · rw [powerFits_eval_model σ _ _ ⟨2,by decide⟩ ⟨255,by decide⟩ rfl rfl]
    congr 1
  · rw [powerFits_eval_model σ _ _ ⟨-2,by decide⟩ ⟨256,by decide⟩ rfl rfl]
    congr 1

theorem unit_and_zero {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    (powerFits (signed 0 (by decide)) (unsigned 0 (by decide))).evalT σ = .ok true ∧
    (powerFits (signed (-1) (by decide))
      (unsigned ((2^256-1 : Nat) : Int) (by decide))).evalT σ = .ok true ∧
    (powerFits (signed 1 (by decide))
      (unsigned ((2^256-1 : Nat) : Int) (by decide))).evalT σ = .ok true := by
  exact ⟨rfl,rfl,rfl⟩

theorem successful_pair {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    ((checkedSignedPower (signed (-2) (by decide)) (unsigned 3 (by decide))).1.run σ >>=
      fun out => (checkedSignedPower (signed (-2) (by decide))
        (unsigned 3 (by decide))).2.evalT out.st >>= fun value => pure (out,value)) =
      .ok ((⟨σ,List.prefix_refl _⟩ : Out C σ.H Γ),
        (⟨-8,by decide⟩ : PrimTy.int.Denote)) := by rfl

/-- info: 'Solidity.Val.NumericV2.Controls.magnitude_overflow_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.Controls.magnitude_overflow_guard
/-- info: 'Solidity.Val.NumericV2.Controls.exact_magnitude_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.Controls.exact_magnitude_overflow
/-- info: 'Solidity.Val.NumericV2.Controls.v1_bare_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.Controls.v1_bare_revert
/-- info: 'Solidity.Val.NumericV2.Controls.exact_not_bare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.Controls.exact_not_bare
/-- info: 'Solidity.Val.NumericV2.Controls.signed_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.Controls.signed_edges
/-- info: 'Solidity.Val.NumericV2.Controls.unit_and_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.Controls.unit_and_zero
/-- info: 'Solidity.Val.NumericV2.Controls.successful_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.Controls.successful_pair

end Solidity.Val.NumericV2.Controls
