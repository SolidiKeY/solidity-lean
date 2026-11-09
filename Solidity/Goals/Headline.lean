import Solidity.Tools.Goal
import Solidity.Backend.Payments.Headlines

/-! Finish-line component 1: the honest headline `Solidity.Main.compiler_correct`
(owner: va2-honest-theorems). -/

namespace Solidity.Goals

open Semantics Solidity.Goal

open Main Evm Evm in
@[goal Solidity.Main.compiler_correct_v2]
def compilerCorrectNoPaymentRevert : Prop :=
  ∀ {C Γ Γ'} {P : Prog C Γ Γ'} {F : Frag Γ} {F' : Frag Γ'} {σ : State C Γ} {mc : Machine} {L b : Nat},
    F ⊩ P ⊣ F' → σ ≈[C, L, b, F] mc → L + Prog.pushes P ≤ Lmax →
    (∃ o mc', (P, σ) ⇓ o ∧ (⟦P⟧b, mc) ⇓ₘ mc' ∧ o.st ≈[C, L + Prog.pushes P, b, F'] mc') ∨
      ((Prog.run σ P = .error .revert ∨
          (Prog.asserts P = true ∧ Prog.run σ P = .error .panic)) ∧ (⟦P⟧b, mc) ↯ₘ) ∨
      (Prog.run σ P = .error .diverge ∧ run (⟦P⟧b) mc = .fault)

@[goal Solidity.Main.compiler_correct "va2-honest-theorems" ← compilerCorrectNoPaymentRevert]
def headlineIsNoPaymentRevert : Prop := compilerCorrectNoPaymentRevert

end Solidity.Goals
