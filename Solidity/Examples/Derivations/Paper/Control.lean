import Solidity.Examples.Common
import Solidity.Semantics.DecEq

/-!
# The calculus's worked examples — payment and control flow

Sections 9–10 of `Examples/Derivations/Paper.lean`: `transfer`, and the
guarded statements `require`/`assert` and `if`/`else`.  The conventions are
that file's docstring; the example-by-example map is `docs/paper-parity.md`.
-/

namespace Solidity.Examples.Paper

open Rules StandardExample SoliditySyntax Solidity.Examples Semantics

set_option maxHeartbeats 8000000

section
variable (φ : WrappedExpr)

/-! ## 9 · Payment

Upstream states the transfer rule as a box taclet with a single update and a
diamond taclet that splits off a funds *obligation*.  Lean merges the two into
one guarded pair, so the diamond line branches into the booking and a revert
rather than into a booking and an obligation — the difference is recorded in
`docs/lean-key-rule-map.md`, and it is the interpreter's reading: an unfunded
`transfer` reverts.  The calculus writes the booking as the pair
`{selfBalance := selfBalance − se ‖ net := store(net, at(to), … − se)}`; here
it is the one element `transfer(to, se)`, which is that pair named. -/

sol_derivation transferBox :
    => [ to.transfer(5) ](φ)
  ~*> [ funded(5) => { transfer(to, 5) } [ ](φ),
        ¬funded(5) => ⊤ ]

sol_derivation transferDiamond :
    => < to.transfer(5) >(φ)
  ~*> [ funded(5) => { transfer(to, 5) } < >(φ),
        ¬funded(5) => ⊥ ]

/-! ### `owner.transfer(5);` — a storage receiver
The calculus cites `transfer_unfold_leftFstReceiver` because a storage root is
not a stack word.  In Lean `owner` is an atom (`WrappedExpr.simple`), so the
receiver needs no capture and the transfer rule fires directly — a genuine
difference in where the "simple operand" line is drawn. -/

sol_derivation transferStorageReceiverBox :
    => [ owner.transfer(5) ](φ)
  ~*> [ funded(5) => { transfer(owner, 5) } [ ](φ),
        ¬funded(5) => ⊤ ]

sol_derivation transferStorageReceiverDiamond :
    => < owner.transfer(5) >(φ)
  ~*> [ funded(5) => { transfer(owner, 5) } < >(φ),
        ¬funded(5) => ⊥ ]

/-! ### `to.transfer(x + 2);` — a nonsimple amount
The amount is captured into `pv` first, exactly as upstream's
`transferUnfoldRightSndArgument` does, and the funds guard is then read *under*
that capture — which is what the `{…}` prefix on the antecedent says.  The
calculus abbreviates the same thing by substituting: it writes
`0 ≤ x + 2 ≤ selfBalance`.

The third line is what KeY's guarded pair costs on an operator that does not
need a guard: `binopAssignment` is stated as `\if(se2 != 0)` for every operator
and specialises the condition, so `+` still produces a `\else` branch — with
the antecedent `¬⊤`, which is what makes it vacuous. -/

sol_derivation transferCapturedAmount :
    => [ to.transfer(x + 2) ](φ)
  ~*> [ { pv@uint := default(uint) } { pv@uint := (x + 2) } funded(pv@uint) =>
          { pv@uint := default(uint) } { pv@uint := (x + 2) }
          { transfer(to, pv@uint) } [ ](φ),
        { pv@uint := default(uint) } { pv@uint := (x + 2) } ¬funded(pv@uint) =>
          { pv@uint := default(uint) } { pv@uint := (x + 2) } ⊤,
        { pv@uint := default(uint) } ¬⊤ => { pv@uint := default(uint) } ⊤ ]

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
