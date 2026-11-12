import Solidity.Theorems
import Solidity.Backend.Payments.Versioned

/-!
# G43 V2 of the `Theorems` compiler headlines

The versioned pair (H57, H98) for `Main.compiler_correct` and
`Main.compiler_checked` (`Solidity/Theorems.lean`), in their notation and
under their premises, with the payment-revert outcome gone:
`compiler_correct_v2`, `compiler_checked_v2`, and the migration lemmas
`compiler_correct_of_v2`, `compiler_checked_of_v2` giving the frozen
statements back. `compiler_correct` now carries V2; `compiler_checked` remains
frozen. This is the only payments headline module
that imports `Solidity.Theorems`; consumers outside `Main` should use
`Backend/Payments/Versioned.lean` instead.
-/

namespace Solidity
namespace Main

open Semantics

variable {C : Contract} {Γ Γ' : Ctx}

open Evm Evm in
/-- **The compiler is correct, V2**: from a machine that represents the typed
state, both end in states the machine still represents, or both revert (a
panic only in code with an `assert`), or the typed run diverges and the
machine faults. A payment the world refuses reverts both (`Sim.oracle`). -/
theorem compiler_correct_v2 {P : Prog C Γ Γ'} {F : Frag Γ} {F' : Frag Γ'} {σ : State C Γ}
    {mc : Machine} {L b : Nat}
    (hP : F ⊩ P ⊣ F') (hm : σ ≈[C, L, b, F] mc) (hL : L + Prog.pushes P ≤ Lmax) :
    (∃ o mc', (P, σ) ⇓ o ∧ (⟦P⟧b, mc) ⇓ₘ mc' ∧ o.st ≈[C, L + Prog.pushes P, b, F'] mc') ∨
      ((Prog.run σ P = .error .revert ∨
          (Prog.asserts P = true ∧ Prog.run σ P = .error .panic)) ∧ (⟦P⟧b, mc) ↯ₘ) ∨
      (Prog.run σ P = .error .diverge ∧ run (⟦P⟧b) mc = .fault) :=
  compiler_correct hP hm hL

open Evm Evm in
/-- Migration: the former four-outcome `compiler_correct` statement, from V2. -/
theorem compiler_correct_of_v2 {P : Prog C Γ Γ'} {F : Frag Γ} {F' : Frag Γ'} {σ : State C Γ}
    {mc : Machine} {L b : Nat}
    (hP : F ⊩ P ⊣ F') (hm : σ ≈[C, L, b, F] mc) (hL : L + Prog.pushes P ≤ Lmax) :
    (∃ o mc', (P, σ) ⇓ o ∧ (⟦P⟧b, mc) ⇓ₘ mc' ∧ o.st ≈[C, L + Prog.pushes P, b, F'] mc') ∨
      ((Prog.run σ P = .error .revert ∨
          (Prog.asserts P = true ∧ Prog.run σ P = .error .panic)) ∧ (⟦P⟧b, mc) ↯ₘ) ∨
      (Prog.pays P = true ∧ (⟦P⟧b, mc) ↯ₘ ∧ ∃ o, (P, σ) ⇓ o) ∨
      (Prog.run σ P = .error .diverge ∧
        (run (⟦P⟧b) mc = .fault ∨ (Prog.pays P = true ∧ (⟦P⟧b, mc) ↯ₘ))) := by
  rcases compiler_correct_v2 hP hm hL with h | h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr ⟨h1, .inl h2⟩))

/-- **The checked entry, V2**: every compilation result agrees exactly under
its input (`Compiler.Compilation.correct_v2`). -/
theorem compiler_checked_v2 {P : Prog C Γ Γ'} {F : Evm.Frag Γ} {b L frame : Nat}
    (compiled : Evm.Compiler.Compilation b F P) {base : Nat → Fin Evm.W}
    {σ : State C Γ} {mc : Evm.Machine}
    (h : compiled.Input L frame base σ mc) :
    compiled.AgreesV2 L frame base σ mc :=
  compiled.correct_v2 h

/-- Migration: the frozen `compiler_checked` statement, from V2. -/
theorem compiler_checked_of_v2 {P : Prog C Γ Γ'} {F : Evm.Frag Γ} {b L frame : Nat}
    (compiled : Evm.Compiler.Compilation b F P) {base : Nat → Fin Evm.W}
    {σ : State C Γ} {mc : Evm.Machine}
    (h : compiled.Input L frame base σ mc) : compiled.Agrees L frame base σ mc :=
  Evm.Compiler.Compilation.agrees_of_v2 (compiler_checked_v2 compiled h)

/-! ## Axioms: Lean's three -/

/-- info: 'Solidity.Main.compiler_correct_v2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compiler_correct_v2

/-- info: 'Solidity.Main.compiler_checked_v2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compiler_checked_v2

end Main
end Solidity
