import Solidity.Tactics.Derivation
import Solidity.Semantics.DecEq

/-!
# The calculus's worked examples — payment and control flow

Sections 9–10 of `SolidityPaper.lean`: `transfer`, and the
guarded statements `require`/`assert` and `if`/`else`.  The conventions are
that file's docstring; the example-by-example map is `docs/paper-parity.md`.
-/

namespace Solidity.Examples.Paper

open Rules StandardExample SoliditySyntax Solidity.Examples Semantics

set_option maxHeartbeats 8000000

section
variable (φ : WrappedExpr)

/-- The calculus's `⊤` as a postcondition: the unfunded transfer is drawn with
it, so that the booking goal is trivial and the funds obligation is all that
is left.  A bare identifier in the postcondition position is a Lean term, so
this is how `⊤` is written there. -/
def truePost : WrappedExpr := Typed.WrappedExpr.bool true

/-! ## 9 · Payment

The calculus states the transfer rule twice, and the modalities part company
at it: the box books the debit unconditionally — an unfunded transfer reverts
on chain, and a reverting run is vacuously correct under partial correctness —
while the diamond owes a *sufficient funds* obligation beside the booking, as
a goal with no program left in it.  Neither draws a revert branch.  The
calculus writes the booking as the pair
`{selfBalance := selfBalance − se ‖ net := store(net, at(to), … − se)}`; here
it is the one element `transfer(to, se)`, which is that pair named. -/

sol_derivation transferBox :
    => [ to.transfer(5) ](φ)
  ~> => { transfer(to, 5) } [ ](φ)

sol_derivation transferDiamond :
    => < to.transfer(5) >(φ)
  ~> [ => funded(5),
       => { transfer(to, 5) } < >(φ) ]

/-! ### `owner.transfer(5);` — a storage receiver
The calculus cites `transfer_unfold_leftFstReceiver` because a storage root is
not a stack word.  In Lean `owner` is an atom (`WrappedExpr.simple`), so the
receiver needs no capture and the transfer rule fires directly — a genuine
difference in where the "simple operand" line is drawn, and one step where
the calculus draws three. -/

sol_derivation transferStorageReceiverBox :
    => [ owner.transfer(5) ](φ)
  ~> => { transfer(owner, 5) } [ ](φ)

sol_derivation transferStorageReceiverDiamond :
    => < owner.transfer(5) >(φ)
  ~> [ => funded(5),
       => { transfer(owner, 5) } < >(φ) ]

/-! ### `to.transfer(x + 2);` — a nonsimple amount
The amount is captured into `se` first, exactly as the calculus's
`transferUnfoldRightSndArgument` does, and the box trace then ends in the
booking under that capture.  The diamond trace splits instead, and the funds
obligation is read *under* the capture — which is what the `{…}` prefix says;
the calculus abbreviates the same thing by substituting, and writes
`0 ≤ x + 2 ≤ selfBalance`.

The last line of each is what KeY's guarded pair costs on an operator that
does not need a guard: `binopAssignment` is stated as `\if(se2 != 0)` for
every operator and specialises the condition, so `+` still produces a `\else`
branch — with the antecedent `¬⊤`, which is what makes it vacuous. -/

sol_derivation transferCapturedAmount :
    => [ to.transfer(x + 2) ](φ)
  ~*> [ => { se@uint := defVal(uint) } { se@uint := (x + 2) }
          { transfer(to, se@uint) } [ ](φ),
        { se@uint := defVal(uint) } ¬⊤ => { se@uint := defVal(uint) } ⊤ ]

sol_derivation transferCapturedAmountDiamond :
    => < to.transfer(x + 2) >(φ)
  ~*> [ => { se@uint := defVal(uint) } { se@uint := (x + 2) } funded(se@uint),
        => { se@uint := defVal(uint) } { se@uint := (x + 2) }
          { transfer(to, se@uint) } < >(φ),
        { se@uint := defVal(uint) } ¬⊤ => { se@uint := defVal(uint) } ⊥ ]

/-! ### an unfunded `to.transfer(5);`
The calculus's last payment example, and the point of the split: nothing is
known about the contract's balance.  The box is `transferBox` again — it never
has to establish funding.  The diamond, with `⊤` as the postcondition, leaves
the funds obligation as the only content of the proof: the second goal closes
and the first is one no rule of the calculus can close. -/

sol_derivation transferUnfundedDiamond :
    => < to.transfer(5) >(truePost)
  ~> [ => funded(5),
       => { transfer(to, 5) } < >(truePost) ]

/-! ## 10 · Require, assert and control flow

`require` is the calculus's own guarded pair, and the only rule whose guard is
a program expression rather than a property of the store. -/

sol_derivation requireSimple :
    => [ require(flag) ](φ)
  ~*> [ flag => [ ](φ),
        ¬flag => ⊤ ]

/-! ### `assert(ok);` — the same statement, a different second line
`require` fails by reverting, so its second line is the revert closed with `⊤`.
`assert` fails by *violating*, so its second line is an obligation: no
antecedent, and the condition itself as the goal.  That is KeY's own shape,
and it is why `Rules.assertGoals` leaves a line a `sol_calculus` still has to
discharge (`docs/calculus-parity.md`). -/

sol_derivation assertSimple :
    => [ assert(flag) ](φ)
  ~> [ flag => [ ](φ),
       => flag ]

/-! ### `if (ok) s0 else s1` — no chain
The calculus's `ifElseSplit` is a *sequent* rule: one sequent in, two out, on
a condition it cannot evaluate.  That is not a `BlockStep`, so it has no
`RuleName` and no chain can name it; it is `JudgmentSplit.ite_split`.  The
four condition-directed rewrites that are rules — `ifElseUnfold`,
`ifElseTrue`, `ifElseFalse`, `ifElseNegated` — have their chains in
`Examples/Derivations/ControlFlow.lean`, together with `revert()` in both
modalities.  `docs/paper-parity.md` carries the row. -/

end

end Solidity.Examples.Paper
