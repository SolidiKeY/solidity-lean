import Solidity.Calculus.RewriteSyntax
import Solidity.Calculus.RewriteSyntax
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Term taclets on a sequent

`rw [findOnSave]` on a sequent applies the term taclet
`TermTaclet.findOnSave` (`Calculus/TermLib.lean`) by `Proves.rewrite`:
its paths are found in the sequent and its side conditions closed on them.
`sol_rw [find_delAt_same, …]` builds a rule from the Theory's own lemmas
instead (`Calculus/RewriteSyntax.lean`).

The sequents are scoped (`open scoped Solidity.Scoped`, `⊢ φ`), over
`StandardExample`: they hold terms only, with no local, no update and no
program, as a leaf the walk leaves.  `rw [r]` (`Calculus/RewriteSyntax.lean`)
runs the scoped twins on a scoped goal's closed terms, a program still open
or not (`Examples/Tactics/SelectOnSaveConsr.lean`).
-/

namespace Solidity.Examples.Tactics.TermTaclets

open Solidity Semantics Theory Theory.StValue

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-- `alice.age = 42; alice.account.balance = 7;` read back at `alice.age`:
the frame steps over the second write, `findOnSave` reads the first, and the
goal `42 ≐ 42` closes.  The taclets are named bare: their paths come from
the sequent, and `diverges` and `hasSeg` close on them. -/
example : ⊢ dl!{ find(save(save(storage, alice.age, 42), alice.account.balance, 7), alice.age)
    ≐ 42 } := by
  rw [findOnSaveFrame, findOnSave]
  exact Proves.eqRefl

/-- `alice.age = 42; delete alice.age;` reads `0` at `alice.age`. -/
example : ⊢ dl!{ find(delAt(save(storage, alice.age, 42), alice.age), alice.age) ≐ 0 } := by
  sol_rw [findOnDelAtSave]
  exact Proves.eqRefl

/-- The same, with the Theory's own lemmas named instead of `findOnDelAtSave`:
the read of the delete (`find_delAt_same`), of the write under it
(`find_copyTo_same`, `copyVal`) and the reset of the word (`delValueDefault`,
`primDefault`), one step, since `delValue (findSt …)` alone is no term. -/
example : ⊢ dl!{ find(delAt(save(storage, alice.age, 42), alice.age), alice.age) ≐ 0 } := by
  sol_rw [find_delAt_same, find_copyTo_same, copyVal, delValueDefault, primDefault]
  exact Proves.eqRefl

/-- A Theory frame lemma: a read off the deleted path, `alice` against
`bob.age`, whose `diverges` closes on the two literal paths. -/
example : ⊢ dl!{ find(delAt(storage, alice), bob.age) ≐ find(storage, bob.age) } := by
  rw [find_delAt_frame]
  exact Proves.eqRefl

/- A frame law whose side condition fails: `alice.account` and
`alice.account.balance` do not diverge, so the scoped `rw` does not apply
it (and Lean's `rw`, tried after, knows no such name). -/
#guard_msgs (drop error) in
example : ⊢ dl!{ find(save(storage, alice.account, 1), alice.account.balance) ≐ 0 } := by
  rw [findOnSaveFrame]

/-- A path named, as an argument: its side condition's default (`by rfl`)
runs once the other path is found. -/
example : ⊢ dl!{ find(save(storage, alice.account.balance, 7), alice.age)
    ≐ find(storage, alice.age) } := by
  rw [findOnSaveFrame (p := Tms.PTerm.field (Tms.PTerm.field (Tms.PTerm.root "alice") "account")
    "balance")]
  exact Proves.eqRefl

/-- Not a sequent: `rw` is Lean's, and so is its error. -/
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  a
in the target expression
  b = b

a b : Nat
h : a = b
⊢ b = b
-/
#guard_msgs in
example (a b : Nat) (h : a = b) : b = b := by
  rw [h]

end Solidity.Examples.Tactics.TermTaclets
