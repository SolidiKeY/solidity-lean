import Solidity.Tactics.Derivation
import Solidity.Semantics.DecEq

/-!
# A storage derivation read one step at a time

`Solidity/Paper/Storage.lean` writes the calculus's chains as `sol_derivation`:
every intermediate frontier is *written*, and the command folds the lines into
one theorem.  That is what the paper prints.  This file is the same fact in the
other presentation — the two endpoints in the statement, the rules in the
proof — for the times when what you want is to step through a derivation rather
than read one off the page.

The chain is `Paper.deepFieldWrite`, `alice.account.balance = 10;`.  Two proofs
of it, both of which Lean checks against the same two lines:

* `deepFieldWrite`, one `seq_step` per rule.  The goal between any two lines is
  the frontier the paper draws there, so the derivation can be walked with the
  cursor.
* `deepFieldWriteListed`, the same rules as one `seq_steps [...]`.  The cursor
  on an element shows that element's frontier, as it does inside `rw [a, b, c]`.

`seq_steps?` is how the rule list was obtained, and how the next one should be.

The frontier the goal shows between two steps is printed by
`Update/SequentPP.lean`, so it reads as the line the paper draws rather than as
the constructor applications it is.  Where the two differ it is because the
term does not carry the annotation: `se@uint` is a `Rules.writeBack` whose
left-hand side is gone by the time the update exists, so it comes back as `se`.

Two things the `sol_derivation` command does for a chain that a hand-written
`seq!` line does not.  The bare `(φ)` goal of the last line carries no
modality, so it is read as the **combined** one (`Update/SequentSyntax.lean`) —
which is what `<[ … ]>` on the first line is, so the endpoints still agree.
And the paper draws the merge as its own `=` line; here it is the last thing
`seq_done` does, since a `⇝ᵘ*` may absorb a trailing merge.
-/

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax Semantics

set_option maxHeartbeats 8000000

section
variable (φ : WrappedExpr)

/-- `alice.account.balance = 10;` — the paper's headline chain, proved one rule
per line.  Put the cursor on any `seq_step` to see the frontier the rule before
it left. -/
theorem deepFieldWrite :
    [ seq!{ => <[ alice.account.balance = 10 ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { se@uint := 10 ‖ sp@Account := path(alice.account)
                       ‖ storage := save(alice.account.balance, 10) } (φ) } ] := by
  seq_step .storageFieldWriteUnfoldLeftFst
  seq_step .localValueDeclInitDrop
  seq_step .valueDeclSkip
  seq_step .localValueAssign
  seq_step .storagePlaceAlias
  seq_step .storageFieldWriteSave
  seq_done

/-- The same chain as one line.  `seq_steps` gives each rule its own info node,
so the frontiers are still there to look at — they are just not on the page. -/
theorem deepFieldWriteListed :
    [ seq!{ => <[ alice.account.balance = 10 ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { se@uint := 10 ‖ sp@Account := path(alice.account)
                       ‖ storage := save(alice.account.balance, 10) } (φ) } ] := by
  seq_steps [.storageFieldWriteUnfoldLeftFst, .localValueDeclInitDrop,
             .valueDeclSkip, .localValueAssign, .storagePlaceAlias,
             .storageFieldWriteSave]

end

end Solidity.Examples
