import Solidity.Calculus.CallbackHolds


namespace Solidity.Counterexamples.DiamondTry

variable {C : Contract} {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf Δ Ω : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁)
    (err : Prog C Γ Γ₂) (code : CodeBinder κ) (pnc : Prog C (κ ++ Γ) Γ₃)
    (other : Prog C Γ Γ₄) (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf)

theorem caller_revert (J : StateInv C) (σ : State C Γ) (self : Bool)
    (rest : Prog C Γ Δ) :
    ExecP J σ (.cons (.tryCall call rets ok err code pnc other sargs sbody self) rest)
      (.halt .revert) :=
  .halt .tryRevert

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
