import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Tests of `sol_close`

Goals `sol_close` is expected to close, each a leaf the scoped strategy
leaves (`open scoped Solidity.Scoped`), read scoped
(`Calculus/CloseScoped.lean`), on `⊨ᶠ` and on a sequent's leaf after
`sol_leaf`.
-/

namespace Solidity.CloseTests


local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## Boolean connectives on literals -/

example : ⊨ᶠ dl!{ ⟨ bool r = true && false; bool t = false; ⟩ r == t } := by
  sol_symex
  sol_close

example : ⊨ᶠ dl!{ ⟨ bool r = false || true; bool t = true; ⟩ r == t } := by
  sol_symex
  sol_close

example : ⊨ᶠ dl!{ [ bool p = flags[k]; bool r = p || true; ] r == true } := by
  sol_symex
  sol_close

example : ⊨ᶠ dl!{ [ bool p = flags[k]; bool q = flags[j]; bool r = p && !q;
    bool s = !(q || !p); ] r == s } := by
  sol_symex
  sol_close

/-! ## Unary operators -/

example : ⊨ᶠ dl!{ ⟨ bool r = !false; bool t = true; ⟩ r == t } := by
  sol_symex
  sol_close

example : ⊨ᶠ dl!{ ⟨ int x = 5; int r = -x; int t = x - 10; ⟩ r == t } := by
  sol_symex
  sol_close

/-! ## A branch condition as a fact (mini-solkey's `whichWriteWins`) -/

example : ⊨ᶠ dl!{ [ balances[a] = 1; balances[b] = 2; uint x = 0;
    if (a == b) { x = 2; } else { x = 1; }; ] balances[a] == x } := by
  sol_symex
  sol_close

/-- The same with `!=`: the condition is `!decide (a = b)`. -/
example : ⊨ᶠ dl!{ [ balances[a] = 1; balances[b] = 2; uint x = 0;
    if (a != b) { x = 1; } else { x = 2; }; ] balances[a] == x } := by
  sol_symex
  sol_close

/-! ## A diamond whose other branch the precondition rules out -/

example : ⊨ᶠ dl!{ a == 1 ∧ b == 2 → ⟨ if (a == b) { revert(); } else { x = 1; }; ⟩ x == 1 } := by
  sol_symex
  sol_close

example : ⊨ᶠ dl!{ a == 1 ∧ b == 2 → ⟨ if (a != b) { x = 1; } else { revert(); }; ⟩ x == 1 } := by
  sol_symex
  sol_close

/-! ## A root write of a local -/

example : ⊨ᶠ dl!{ [ age = amount; ] age == amount } := by
  sol_symex
  sol_close

/-! ## A sequent's leaf, after `sol_leaf` -/

example : ⊢ dl!{ a == 1 → a == 1 } := by
  apply intro
  sol_leaf
  sol_close

example : ⊢ dl!{ [ x = 1; ] x == 1 } := by
  apply update .localValueAssign
  apply empty
  sol_leaf
  sol_close

/-- A joined `if`'s one goal (`ifElseJoin`), its value split back into the
two cases at the leaf (`sol_close_ite_split`). -/
example : ⊢ dl!{ a == b → ⟨ if (a == b) { x = 2; } else { x = 1; }; ⟩ x == 2 } := by
  apply intro
  apply unfold .ifElseUnfold
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply update .ifElseJoin
  apply empty
  sol_leaf
  sol_close

/--
trace: case h₁
⊢ ⊨ᶠ dl{ ∀ uint x; ∀ uint b; ∀ uint a; { se1 := a == b } (se1 = true → { x := 2 } ¬x = 0) }

case h₂
⊢ ⊨ᶠ dl{ ∀ uint x; ∀ uint b; ∀ uint a; { se1 := a == b } (se1 = false → { x := 1 } ¬x = 0) }
-/
#guard_msgs in
/-- The split itself (`sol_close_ite_split`, KeY's `ifthenelse_split`): the
joined `{x := se1 ? 2 : 1}` back into the two cases `ifElseSplit` would have
left, each closed as such a leaf. -/
example : ⊨ᶠ dl!{ [ if (a == b) { x = 2; } else { x = 1; }; ] x != 0 } := by
  sol_symex
  sol_close_ite_split
  trace_state
  all_goals sol_close

/-- Each goal of a split (the scoped split has KeY's two): a branch that
writes the storage is not joined. -/
example : ⊢ dl!{ a == b → ⟨ if (a == b) { x = 2; } else { age = 1; x = 1; }; ⟩ x == 2 } := by
  apply intro
  apply unfold .ifElseUnfold
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply split .ifElseSplit
  case thn =>
    apply update .localValueAssign
    apply empty
    sol_leaf
    sol_close
  case els =>
    apply update .storageRootWriteStore
    apply update .localValueAssign
    apply empty
    sol_leaf
    sol_close

/-! ## Parameters read at their types (M6c)

A scoped leaf keeps its parameters as quantifiers at their types
(`holds`, `Calculus/CloseScoped.lean`), so `sol_close` reads `a`
as a `uint` in range (a parameter is a `uint`, `Calculus/Notation.lean`).
The erased leaf with `a` stripped to a free name, bound to anything (unset,
a negative integer, a boolean), left these open. -/

/-- A `uint` parameter is at least `0`. -/
example : ⊨ᶠ dl!{ [ uint x = a; ] x >= 0 } := by
  sol_symex
  sol_close

/-- … and is set: the diamond's read of it returns. -/
example : ⊨ᶠ dl!{ ⟨ uint x = a; ⟩ x == a } := by
  sol_symex
  sol_close

/-- … and the diamond's checked `+` returns below the bound. -/
example : ⊨ᶠ dl!{ a < 100 → ⟨ uint y = a + 1; ⟩ y <= 100 } := by
  sol_symex
  sol_close

/-! ## The scoped leaf, read on the typed state (W9.7.2) -/

/-- `sol_close_unwrap` takes a scoped leaf to `holds` in every typed state,
and `close_rw_s` reads it. -/
example : ⊨ᶠ dl!{ [ x = 1; ] x == 1 } := by
  sol_symex
  sol_close_unwrap
  intro σ
  show holds σ _
  sol_close_eval

/-- With no goal left, `sol_close` does nothing. -/
example : ⊨ᶠ dl!{ [ revert(); ] true } := by
  sol_symex
  sol_close
  sol_close

/- A leaf whose term is a variable: the closer's pass cannot evaluate its
Booleans, so the leaf is read as it stands (`t = t`, KeY's `=` reflexive). -/
#guard_msgs in
example (t : Tm StandardExample [] (.val .uint)) : Fml.Valid (.eq t t) := by
  sol_close

end Solidity.CloseTests
