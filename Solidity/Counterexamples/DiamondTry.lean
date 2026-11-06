import Solidity.Calculus.CallbackHolds

/-!
# External try witnesses do not establish a callback diamond

The callback reading universally checks executions even under the diamond.
`ExecS.tryRevert` supplies a caller revert independently of the callee's
success/catch witnesses. This obstruction applies under both payment flags,
to all clauses, continuations, frames and postconditions.
-/

namespace Solidity.Counterexamples.DiamondTry

variable {C : Contract} {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf Δ Ω : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁)
    (err : Prog C Γ Γ₂) (code : CodeBinder κ) (pnc : Prog C (κ ++ Γ) Γ₃)
    (other : Prog C Γ Γ₄) (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf)

/-- Every try admits a caller revert in the existing callback semantics. -/
theorem caller_revert (J : StateInv C) (σ : State C Γ) (self : Bool)
    (rest : Prog C Γ Δ) :
    ExecP J σ (.cons (.tryCall call rets ok err code pnc other sargs sbody self) rest)
      (.halt .revert) :=
  .halt .tryRevert

/-- An existential successful or caught execution cannot discharge this
universally read diamond, including with `pay = false`. -/
theorem callback_diamond_false (I : Fml C []) (pay : Bool) (σ : State C Γ)
    (self : Bool) (rest : Prog C Γ Δ) (frames : Frames C Δ Ω) (post : Fml C Ω) :
    ¬ holdsC I pay σ (.modal .diamond
      (.cons (.tryCall call rets ok err code pnc other sargs sbody self) rest) frames post) := by
  intro h
  have bad : THalt.revert = .exhausted := (h _ (caller_revert call rets ok err code pnc other sargs sbody
    (I.stateInv pay) σ self rest)).1
  cases bad

/-- info: 'Solidity.Counterexamples.DiamondTry.callback_diamond_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms callback_diamond_false

end Solidity.Counterexamples.DiamondTry
