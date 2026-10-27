import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.CallbackDerive
import Solidity.Tools.Inspect
import Solidity.Examples.LexRuleSyntax

/-!
# Public ordinary-diamond tuple variants

Source tuples select the named lexicographic invariant rule. Every component
must evaluate and the tuple must decrease after each successful body. These
ordinary modal proofs retain the exhaustion policy; they are not strict
SourceCertificates. Callback diamonds and unsupported annotations stay pending.
-/
namespace Solidity.Examples.Tactics.LexDiamond

open scoped Scoped

def Counter : Contract := contract!{ uint n; uint m; }
local instance : InContract := ⟨Counter⟩

theorem pairCountdown : ⊨ᶠ dl!{ ⟨
    /// @custom:key invariant true
    /// @custom:key decreases (n, 0)
    while (n > 0) { n−−; };
  ⟩ n == 0 } := by
  sol_symex
  sol_close

theorem tripleCountdown : ⊨ᶠ dl!{ ⟨
    /// @custom:key invariant true
    /// @custom:key decreases (n, 0, 0)
    while (n > 0) { n−−; };
  ⟩ n == 0 } := by
  sol_symex
  sol_close

/-- Resetting `m` increases the second component while the first decreases. -/
theorem pairReset : ⊨ᶠ dl!{ ⟨
    /// @custom:key invariant true
    /// @custom:key decreases (n, m)
    while (n > 0 || m > 0) {
      if (m > 0) { m−−; } else { n−−; m = 2; }
    };
  ⟩ n == 0 && m == 0 } := by
  sol_symex
  sol_close

theorem tripleReset : ⊨ᶠ dl!{ ⟨
    /// @custom:key invariant true
    /// @custom:key decreases (n, m, 0)
    while (n > 0 || m > 0) {
      if (m > 0) { m−−; } else { n−−; m = 2; }
    };
  ⟩ n == 0 && m == 0 } := by
  sol_symex
  sol_close

example : True := by
  fail_if_success
    have : ⊨ᶠ dl!{ ⟨
      /// @custom:key invariant true
      /// @custom:key decreases (0, 0)
      while (n > 0) { n−−; };
    ⟩ n == 0 } := by sol_symex; sol_close
  trivial

example : True := by
  fail_if_success
    have : ⊨ᶠ dl!{ ⟨ uint i = 0;
      /// @custom:key invariant i <= 2
      /// @custom:key decreases (i, 0)
      while (i < 2) { i++; };
    ⟩ i == 2 } := by sol_symex; sol_close
  trivial

example : True := by
  fail_if_success
    have : ⊨ᶠ dl!{ ⟨
      /// @custom:key invariant true
      /// @custom:key decreases (0, 1 / 0)
      while (false) { };
    ⟩ true } := by sol_symex; sol_close
  trivial

example : True := by
  fail_if_success
    have : ⊨ᶠ dl!{ ⟨
      /// @custom:key invariant true
      /// @custom:key decreases (n, 0)
      while (n > 0) { revert(); };
    ⟩ true } := by sol_symex; sol_close
  trivial

example : True := by
  fail_if_success
    have : ⊨ᶠ dl!{ ⟨
      /// @custom:key invariant true
      /// @custom:key decreases (n + 1, 0)
      while (false) { };
    ⟩ true } := by sol_symex; sol_close
  trivial

/-- Break annotations keep the conservative pending path. -/
example : True := by
  fail_if_success
    have : ⊨ᶠ dl!{ ⟨
      /// @custom:key invariant true
      /// @custom:key decreases (n, 0)
      while (n > 0) { break; };
    ⟩ true } := by sol_symex; sol_close
  trivial

/-- Quantified clauses retain the explicit pending diamond path. -/
example : True := by
  fail_if_success
    have : ⊨ᶠ dl!{ ⟨
      /// @custom:key invariant true
      /// @custom:key invariant \forall uint q; q < n -> q < n
      /// @custom:key decreases (n, 0)
      while (n > 0) { n−−; };
    ⟩ n == 0 } := by sol_symex; sol_close
  trivial

/-- Memory allocation has no admitted invariant frame. -/
example : True := by
  fail_if_success
    have : ⊨ᶠ dl!{ ⟨
      /// @custom:key invariant true
      /// @custom:key decreases (n, 0)
      while (n > 0) { uint[] memory temporary = new uint[](1); n−−; };
    ⟩ n == 0 } := by sol_symex; sol_close
  trivial

/-- Existing scalar variant behavior remains available. -/
theorem scalarCountdown : ⊨ᶠ dl!{ ⟨
    /// @custom:key invariant true
    /// @custom:key decreases n
    while (n > 0) { n−−; };
  ⟩ n == 0 } := by
  sol_symex
  sol_close

/-- Callback diamonds have no lexicographic invariant bridge. -/
example : True := by
  fail_if_success
    have : ValidC (.tt : Fml Counter []) dl!{ ⟨
      /// @custom:key invariant true
      /// @custom:key decreases (n, 0)
      while (n > 0) { n−−; };
    ⟩ n == 0 } := by sol_prove
  trivial

end Solidity.Examples.Tactics.LexDiamond
