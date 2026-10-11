import Solidity.Calculus.NFmlClose
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Tests of `sol_close`

Goals `sol_close` is expected to close (`NFmlClose.lean`), each a leaf the
scoped strategy leaves (`open scoped Solidity.Scoped`), erased to
today's formulas.
-/

namespace Solidity.CloseTests


local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## Boolean connectives on literals -/

example : ⊨ dl!{ ⟨ bool r = true && false; bool t = false; ⟩ r == t } := by
  sol_symex
  sol_close

example : ⊨ dl!{ ⟨ bool r = false || true; bool t = true; ⟩ r == t } := by
  sol_symex
  sol_close

example : ⊨ dl!{ [ bool p = flags[k]; bool r = p || true; ] r == true } := by
  sol_symex
  sol_close

example : ⊨ dl!{ [ bool p = flags[k]; bool q = flags[j]; bool r = p && !q;
    bool s = !(q || !p); ] r == s } := by
  sol_symex
  sol_close

/-! ## Unary operators -/

example : ⊨ dl!{ ⟨ bool r = !false; bool t = true; ⟩ r == t } := by
  sol_symex
  sol_close

example : ⊨ dl!{ ⟨ int x = 5; int r = -x; int t = x - 10; ⟩ r == t } := by
  sol_symex
  sol_close

/-! ## A branch condition as a fact (mini-solkey's `whichWriteWins`) -/

example : ⊨ dl!{ [ balances[a] = 1; balances[b] = 2; uint x = 0;
    if (a == b) { x = 2; } else { x = 1; }; ] balances[a] == x } := by
  sol_symex
  sol_close

/-- The same with `!=`: the condition is `!decide (a = b)`. -/
example : ⊨ dl!{ [ balances[a] = 1; balances[b] = 2; uint x = 0;
    if (a != b) { x = 1; } else { x = 2; }; ] balances[a] == x } := by
  sol_symex
  sol_close

/-! ## A diamond whose other branch the precondition rules out -/

example : ⊨ dl!{ a == 1 ∧ b == 2 → ⟨ if (a == b) { revert(); } else { x = 1; }; ⟩ x == 1 } := by
  sol_symex
  sol_close

example : ⊨ dl!{ a == 1 ∧ b == 2 → ⟨ if (a != b) { x = 1; } else { revert(); }; ⟩ x == 1 } := by
  sol_symex
  sol_close

/-! ## A root write of a local -/

example : ⊨ dl!{ [ age = amount; ] age == amount } := by
  sol_symex
  sol_close

/-! ## After `refine close ?_` -/

example : ⊢ dl!{ a == 1 → a == 1 } := by
  apply intro
  refine close ?_
  sol_symex
  sol_close

example : ⊢ dl!{ [ x = 1; ] x == 1 } := by
  apply update .localValueAssign
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- Each goal of a split (the scoped split has KeY's two). -/
example : ⊢ dl!{ a == b → ⟨ if (a == b) { x = 2; } else { x = 1; }; ⟩ x == 2 } := by
  apply intro
  apply unfold .ifElseUnfold
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply split .ifElseSplit
  case thn =>
    apply update .localValueAssign
    apply empty
    refine close ?_
    sol_symex
    sol_close
  case els =>
    apply update .localValueAssign
    apply empty
    refine close ?_
    sol_symex
    sol_close

/-! ## Parameters read at their types (M6c)

A scoped leaf keeps its parameters as quantifiers (`sol_close_unwrap`,
`Calculus/Derive.lean`), so `sol_close` reads `a` as a `uint` in range (a
parameter is a `uint`, `Calculus/Notation.lean`).  The erased leaf with
`a` stripped to a free name, bound to anything (unset, a negative
integer, a boolean), left these open. -/

/-- A `uint` parameter is at least `0`. -/
example : ⊨ dl!{ [ uint x = a; ] x >= 0 } := by
  sol_symex
  sol_close

/-- … and is set: the diamond's read of it returns. -/
example : ⊨ dl!{ ⟨ uint x = a; ⟩ x == a } := by
  sol_symex
  sol_close

/-- … and the diamond's checked `+` returns below the bound. -/
example : ⊨ dl!{ a < 100 → ⟨ uint y = a + 1; ⟩ y <= 100 } := by
  sol_symex
  sol_close

/-- With no goal left, `sol_close` does nothing. -/
example : ⊨ dl!{ [ revert(); ] true } := by
  sol_symex
  sol_close
  sol_close

end Solidity.CloseTests
