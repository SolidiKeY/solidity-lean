import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close

/-!
# Quantified premises at later indices

These proofs use the public strategy and closer. The earlier scoped
`allLeftHide` pre-pass cannot name the later local in the premise's context;
the fallback applies the quantified proof after opening the typed leaf.
-/
namespace Solidity.Examples.Tactics.AllLeftLater
local instance : InContract := ⟨StandardExample⟩
open scoped Solidity.Scoped
/-- The later universally bound index is outside the quantified premise's scope. -/
theorem laterIndex : ⊨ᶠ dl!{ (∀ uint k; k < values.length → values[k] <= 255) →
    ∀ uint i; i < values.length → values[i] <= 255 } := by
  sol_prove
  all_goals sol_leaf
  all_goals sol_close

/-- A program local is introduced after the premise and initialized from a parameter. -/
theorem laterLocal : ⊨ᶠ dl!{ (∀ uint k; balances[k] <= 255) →
    ∀ uint bound; [ uint i = bound; ] balances[i] <= 255 } := by
  sol_prove
  all_goals sol_leaf
  all_goals sol_close

/-- The invariant rule anonymises the counter: the instance uses its typed projection. -/
theorem loopCounter : ⊨ᶠ dl!{ (∀ uint k; balances[k] <= 255) →
    [ uint i = 0;
      /// @custom:key invariant i <= 3
      while (i < 3) { assert(balances[i] <= 255); i++; };
    ] i == 3 } := by
  sol_prove
  all_goals sol_leaf
  all_goals sol_close


/-- Guard proofs are required before a bounded universal can yield its conclusion. -/
example (P : Int → Prop) (h : ∀ n, 0 ≤ n → n ≤ 10 → P n)
    (i : Int) (hi : 0 ≤ i) (hi' : i ≤ 10) : P i := by
  sol_close_all
  assumption

/-- An unavailable guard is retained as an implication, rather than assumed. -/
example (P : Int → Prop) (h : ∀ n, 0 ≤ n → n ≤ 10 → P n)
    (i : Int) (hi : 0 ≤ i) : i ≤ 10 → P i := by
  sol_close_all
  assumption

/-- A function returning propositions is data, rather than a universal proof. -/
example (_P : Int → Prop) (_i : Int) : True := by
  fail_if_success sol_close_all
  trivial

@[reducible] private def deepResult : Nat → Prop → Prop
  | 0, P => P
  | n + 1, P => deepResult n P

/-- Candidate result normalization can exceed its budget before guard solving.
The failed attempt restores the original context and allows a fallback. -/
example (P : Nat → Prop) (_h : ∀ n, deepResult n (P n))
    (fallback : Unit → P 1000000) : P 1000000 := by
  let i : Nat := 1000000
  fail_if_success sol_close_all
  exact fallback ()

/-- An unsupported existential is retained while its supported sibling advances. -/
example (w : PrimTy.int.Denote) (P : Nat → Prop) (h : P 7) :
    (∃ n : Nat, P n) ∧ ∃ a : PrimTy.int.Denote, w.val = a.val ∧ True := by
  sol_close_captures
  case left => exact ⟨7, h⟩
  case right =>
    change True
    trivial

@[reducible] private def captureTail : Nat → Prop
  | 0 => True
  | n + 1 => True → captureTail n

/-- The constructor budget retains the unfinished tail instead of dropping it. -/
example : captureTail 129 := by
  sol_close_captures
  fail_if_success done
  change True → True
  exact fun h => h

end Solidity.Examples.Tactics.AllLeftLater
