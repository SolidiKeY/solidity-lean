import Solidity.Calculus.Rewrite
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.RewriteSyntax

/-!
# Update simplification: one update instead of a stack

Symbolic execution leaves one update per terminal rule in front of the
postcondition; KeY merges them as it goes (`Calculus/NFmlUpdateRules.lean`,
mini-solkey's update examples).  Here the same derivation is shown
rule by rule with `sol_upd`, all at once with `sol_merge` on `⊨`, and with
`refine merge rfl ?_`/`refine simplify ?_` on `⊢`.  The goals are under the box: a
leaf is closed on its erasure over untyped states (`Calculus/CloseErase.lean`,
until M6c), where a write under the diamond may fail.

The formulas read scoped (`open scoped Solidity.Scoped`): the rules
rewrite a leaf's erasure (`sol_upd`, `sol_merge`,
`Calculus/Closers.lean`), today's update.  The sequent rules `merge`
and `simplify` are the scoped sequent's (`Calculus/RewriteSyntax.lean`
reads today's lines).
-/

namespace Solidity.Examples.Tactics.UpdateRules

open NFml.Proves

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## Rule by rule

`sequentialToParallel` merges the two outermost updates, substituting the
first into the second: `sp1.balance` becomes `alice.account.balance`, `se1`
becomes `10`.  After two merges `se1` and `sp1` are written and never read,
and neither can halt, so `simplifyUpdate` drops them. -/

/--
trace: ⊢ ⊨
    dl{
      { se1 := 10 }
        { sp1 := alice.account }
          { storage := save(storage, sp1.balance, se1) } find(storage, alice.account.balance) = 10 }
---
trace: ⊢ ⊨
    dl{
      { se1 := 10 ‖ sp1 := alice.account }
        { storage := save(storage, sp1.balance, se1) } find(storage, alice.account.balance) = 10 }
---
trace: ⊢ ⊨
    dl{
      { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) }
        find(storage, alice.account.balance) = 10 }
---
trace: ⊢ ⊨ dl{ { storage := save(storage, alice.account.balance, 10) } find(storage, alice.account.balance) = 10 }
-/
#guard_msgs in
/-- `alice.account.balance = 10;`, its three updates merged into one. -/
theorem deepFieldWrite_upd :
    ⊨ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } := by
  sol_symex
  trace_state
  sol_upd .sequentialToParallel
  trace_state
  sol_upd .sequentialToParallel
  trace_state
  sol_upd .simplifyUpdate
  trace_state
  sol_close

/-- A rule that does not fit is refused: `se1` is read by the update after it,
and no update is empty. -/
example : ⊨ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } := by
  sol_symex
  fail_if_success sol_upd .simplifyUpdate
  fail_if_success sol_upd .applySkip
  sol_close

/-! ## The other rules

`applyOnRigid` substitutes an update that cannot halt into the first-order
formula under it, and `applySkip` removes an update with nothing left in it.
The empty update is KeY's `skip`; the notation has no syntax for it, so it
prints as the escaped term `‹[]›`. -/

/-- trace: ⊢ ⊨ dl{ 3 = 3 } -/
#guard_msgs in
example : ⊨ dl!{ { y := 3 } y = 3 } := by
  sol_upd .applyOnRigid
  trace_state
  sol_close

/--
trace: ⊢ ⊨ dl{ ‹[]› true }
---
trace: ⊢ ⊨ dl{ true }
-/
#guard_msgs in
example : ⊨ dl!{ { y := 3 } true } := by
  sol_upd .simplifyUpdate
  trace_state
  sol_upd .applySkip
  trace_state
  sol_close

/-- `x = x;` leaves `x := x`, which halts where `x` holds no value: dropping
it is sound under the box only (`UpdElem.elimSelf_box`), so it is a lemma
applied by hand, not a rule of `sol_upd`. -/
theorem selfAssign : ⊨ dl!{ [ x = x; y = 3; ] y == 3 } := by
  sol_symex
  sol_merge
  refine fun σ => Surface.UpdElem.elimSelf_box rfl ?_
  revert σ
  show NFml.Valid _
  sol_close

/-! ## All at once: `sol_merge` -/

/--
trace: ⊢ ⊨ dl{ { storage := save(storage, alice.account.balance, 10) } find(storage, alice.account.balance) = 10 }
-/
#guard_msgs in
/-- The headline, merged in one call. -/
theorem deepFieldWrite_merge :
    ⊨ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } := by
  sol_symex
  sol_merge
  trace_state
  sol_close

/--
trace: ⊢ ⊨ dl{ ∀ uint y; ∀ uint x; { x := 1 } { y := x } y = 1 }
---
trace: ⊢ ⊨ dl{ { y := 1 } y = 1 }
-/
#guard_msgs in
/-- `x = 1; y = x;`: merged, then `x := 1` dropped as unused. -/
theorem copyLocal_merge : ⊨ dl!{ [ x = 1; y = x; ] y == 1 } := by
  sol_symex
  trace_state
  sol_merge
  trace_state
  sol_close

/-! Two storage writes stay two updates: an update that writes the storage
is not substituted into one that reads it (`Upd.envOnly`), and a
`storage :=` element is never effectless. -/

/--
trace: ⊢ ⊨ dl{ { storage := save(storage, balances[a], 1) } { storage := save(storage, balances[b], 2) } true }
-/
#guard_msgs in
/-- `balances[a] = 1; balances[b] = 2;`: nothing to merge. -/
theorem twoWrites_merge : ⊨ dl!{ [ balances[a] = 1; balances[b] = 2; ] true } := by
  sol_symex
  sol_merge
  trace_state
  sol_close

/-! ## In a derivation: `merge`, `simplify`

Under `⊢` the updates are in the context, the latest last.  `merge` joins
the last two (`sequentialToParallel`, `rfl` checks the merge);
`simplify` cleans the last one.  The sequent is the scoped one: `merge` is
a rule of the calculus (`Calculus/Proves.lean`), so it need not wait for
the modalities to be gone, and `simplify` drops what the update pops after
it (`Calculus/UpdateRules.lean`); the context also holds the hidden
binders of `se1` and `sp1` and their scope's end, which print as nothing. -/

/--
trace: case h
⊢ dl{ { se1 := 10 }, { sp1 := alice.account }, { storage := save(storage, sp1.balance, se1) } ⟹
    find(storage, alice.account.balance) = 10 }
---
trace: case h
⊢ dl{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } ⟹
    find(storage, alice.account.balance) = 10 }
---
trace: case h
⊢ dl{ { storage := save(storage, alice.account.balance, 10) } ⟹ find(storage, alice.account.balance) = 10 }
-/
#guard_msgs in
/-- `alice.account.balance = 10;`, walked, its context merged. -/
theorem deepFieldWriteMerged :
    ⊢ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } := by
  apply unfold .storageFieldWrite_unfold_leftFst
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldWriteSave
  apply empty
  trace_state
  refine merge rfl ?_
  refine merge rfl ?_
  trace_state
  refine simplify ?_
  trace_state
  refine close ?_
  sol_symex
  sol_close

end Solidity.Examples.Tactics.UpdateRules
