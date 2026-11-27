import Solidity.Backend.Passes.Bytes.FullMachine.Intrinsic

/-!
# Negative controls for intrinsic compiler outcomes

These use the public projections at the existing intrinsic boundary. A divergent
source cannot produce intrinsic success, and intrinsic success cannot retain a
positive pending skip. Neither control asserts any byte execution result.
-/
namespace Solidity.Examples.Backend.BytesFullMachine.Intrinsic

open Evm Evm.Compiler
open Backend.Passes.Bytes.FullMachine.Intrinsic

/-- A source loop that diverges cannot compile to intrinsic success under Input. -/
example {C : Contract} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Solidity.Prog C Γ Δ} {b L frame : Nat}
    (r : Compilation b F P) {base : Nat → Fin W}
    {σ : Solidity.State C Γ} {m0 m : Machine}
    (input : r.Input L frame base σ m0)
    (diverges : P.run σ = .error .diverge) (k : Nat)
    (success : Evm.run r.code m0 = .ok m k) : False := by
  have fault := (fault_iff_diverges r input).2 diverges
  rw [success] at fault
  cases fault

/-- Closed successful intrinsic code cannot leave a positive jump skip. -/
example {C : Contract} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Solidity.Prog C Γ Δ} {b L frame : Nat}
    (r : Compilation b F P) {base : Nat → Fin W}
    {σ : Solidity.State C Γ} {m0 m : Machine}
    (input : r.Input L frame base σ m0) (k : Nat)
    (skipped : Evm.run r.code m0 = .ok m (k + 1)) : False := by
  have zero := skip_zero r input (k + 1) skipped
  omega

end Solidity.Examples.Backend.BytesFullMachine.Intrinsic
