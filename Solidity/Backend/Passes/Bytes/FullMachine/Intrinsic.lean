import Solidity.Backend.Payments.CompilerExact

/-!
# Intrinsic outcome projections for full-machine agreement

These are consequences of the existing checked compiler contract, before any
byte representation. They neither authorize `Compilation.Input` as a bytes
entry premise nor prove byte execution, payload, rollback or resource agreement.
-/
namespace Solidity.Backend.Passes.Bytes.FullMachine.Intrinsic

open Evm Evm.Compiler

/-- Under the existing intrinsic input, machine fault is exactly source divergence. -/
theorem fault_iff_diverges {C : Contract} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Solidity.Prog C Γ Δ} {b L frame : Nat}
    (r : Compilation b F P) {base : Nat → Fin W}
    {σ : Solidity.State C Γ} {m0 : Machine}
    (input : r.Input L frame base σ m0) :
    Evm.run r.code m0 = .fault ↔ P.run σ = .error .diverge := by
  rcases r.correct_exact input with
    ⟨o, m, hs, ht, _⟩ | ⟨hs | ⟨_, hs⟩, ht⟩ | ⟨hs, ht⟩ <;>
    simp only [hs, ht, Except.error.injEq, reduceCtorEq]

/-- Successful checked intrinsic execution has no pending instruction skip. -/
theorem skip_zero {C : Contract} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Solidity.Prog C Γ Δ} {b L frame : Nat}
    (r : Compilation b F P) {base : Nat → Fin W}
    {σ : Solidity.State C Γ} {m0 m : Machine}
    (input : r.Input L frame base σ m0) (k : Nat)
    (run : Evm.run r.code m0 = .ok m k) : k = 0 := by
  rcases r.correct_exact input with ⟨_, _, _, ht, _⟩ | ⟨_, ht⟩ | ⟨_, ht⟩
  · rw [ht] at run
    cases run
    rfl
  · rw [ht] at run
    cases run
  · rw [ht] at run
    cases run

end Solidity.Backend.Passes.Bytes.FullMachine.Intrinsic
