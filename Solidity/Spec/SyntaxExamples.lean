import Solidity.Spec.Syntax
import Solidity.Spec.Tactic

/-!
# Worked `solspec!` specifications

The in-Lean notation of `Spec/Syntax.lean`, exercised over stores
built the same way the `.sol` front-end builds them: one Lean variable
per storage slot, so an obligation quantifies over every store of that
shape rather than running from one fixed one.

The file is in two halves on purpose. The `#check` block elaborates the
*syntax* of every clause form without proving anything, so a grammar
problem is visible on its own; the theorems below then exercise the
`sol_spec` tactic on those same shapes. If the `#check`s pass and a
theorem does not, the parser is fine and the automation is what needs
work.

Names come from the program's vocabulary (`SoliditySyntax.rootExpr`), so
the stores here use the calculus's roots — `age`, `total`, `balance`,
`values` as globals, `amount` as a stack local. A contract with other
names writes them `myRoot@@uint`, the program language's own escape
hatch.
-/

namespace Solidity
namespace Spec
namespace SyntaxExamples

set_option maxHeartbeats 8000000

open Semantics

/-! ## Stores -/

/-- Three primitive globals and one parameter, all symbolic. -/
def store (age total balance amount : Int) : State :=
  { storage :=
      [("age", SVal.int age), ("total", SVal.int total),
       ("balance", SVal.int balance)],
    env := [("amount", Binding.val (Value.int amount))] }

/-- A store with an array root, for `push` and the quantifiers. -/
def arrStore (xs : List SVal) (total : Int) : State :=
  { storage := [("values", SVal.array xs), ("total", SVal.int total)] }

/-! ## Grammar smoke tests

Elaboration only: every clause form and every specification-expression
form, with no proof attached. -/

section Grammar

#check solspec!{ requires (amount <= age)
                 ensures (age == old(age) - amount)
                 < age -= amount > }

#check solspec!{ ensures (age == old(age) + old(total))
                 modifies age
                 < age = age + total > }

#check solspec!{ invariant (age + total <= 100)
                 modifies age, total
                 < age = 0; total = 0 > }

-- Partial correctness is the square bracket, as in `sol!`.
#check solspec!{ ensures (age == old(age) - amount)
                 reverts_when (age < amount)
                 [ require((amount <= age)); age -= amount ] }

-- `==>` and `<==>`, the two connectives Solidity does not have.
#check solspec!{ requires (0 < amount ==> amount <= age)
                 ensures ((age < 10) <==> (total < 10))
                 < total = age > }

-- Bounded quantifiers; the binder is a Lean `Int` usable as an index.
#check solspec!{ requires (forall i in 0 .. values.length :: values[i] <= total)
                 ensures (exists i in 0 .. values.length :: values[i] <= total)
                 < total = total > }

-- Ghost steps between statements.
#check solspec!{ ensures (total == 1)
                 < age = 1;
                   ghost assert (age == 1);
                   ghost assume (total >= 0);
                   total = age > }

-- A root outside `rootExpr`'s table, via the program language's `@@` form.
#check solspec!{ ensures (balSender@@uint == old(balSender@@uint) - amount)
                 < balSender@@uint -= amount > }

end Grammar

/-! ## Proved specifications -/

/-- The transfer, in the surface syntax: precondition, two
postconditions with `old`, and a frame that leaves `balance` alone.
The range hypotheses are what the front-end emits for `uint256`
inputs; under checked arithmetic (solc ≥ 0.8) total correctness needs
them — without `hsum` the `total += amount` overflow is exactly the
report this obligation would produce. -/
theorem move_spec (age total balance amount : Int)
    (hrange_age : Spec.inRange 0 115792089237316195423570985008687907853269984665640564039457584007913129639935 age)
    (hrange_total : Spec.inRange 0 115792089237316195423570985008687907853269984665640564039457584007913129639935 total)
    (hrange_amount : Spec.inRange 0 115792089237316195423570985008687907853269984665640564039457584007913129639935 amount)
    (hsum : total + amount ≤ 115792089237316195423570985008687907853269984665640564039457584007913129639935) :
    solspec!{ requires (amount <= age)
              ensures (age == old(age) - amount)
              ensures (total == old(total) + amount)
              ensures (age + total == old(age) + old(total))
              modifies age, total
              < age -= amount; total += amount > }
      (store age total balance amount) := by
  sol_spec [store]

/-- The frame is the interesting half: `balance` is not in `modifies`,
so it has to come out of the final state unchanged. -/
theorem move_frame (age total balance amount : Int)
    (hrange_age : Spec.inRange 0 115792089237316195423570985008687907853269984665640564039457584007913129639935 age)
    (hrange_total : Spec.inRange 0 115792089237316195423570985008687907853269984665640564039457584007913129639935 total)
    (hrange_amount : Spec.inRange 0 115792089237316195423570985008687907853269984665640564039457584007913129639935 amount)
    (hsum : total + amount ≤ 115792089237316195423570985008687907853269984665640564039457584007913129639935) :
    solspec!{ requires (amount <= age)
              modifies age, total
              < age -= amount; total += amount > }
      (store age total balance amount) := by
  sol_spec [store]

/-- A contract invariant: assumed on entry, proved on exit. The added
hypotheses are the checked-arithmetic ranges plus the guard a caller
would establish (`amount ≤ age`): the invariant alone does not rule
out the `age -= amount` underflow revert. -/
theorem invariant_preserved (age total balance amount : Int)
    (hrange_age : Spec.inRange 0 115792089237316195423570985008687907853269984665640564039457584007913129639935 age)
    (hrange_total : Spec.inRange 0 115792089237316195423570985008687907853269984665640564039457584007913129639935 total)
    (hrange_amount : Spec.inRange 0 115792089237316195423570985008687907853269984665640564039457584007913129639935 amount)
    (hamt : amount ≤ age) :
    solspec!{ invariant (age + total <= 100)
              modifies age, total
              < age -= amount; total += amount > }
      (store age total balance amount) := by
  sol_spec [store]

/-- Partial correctness plus `reverts_when`: the guard's two branches,
one discharged vacuously by the box reading, the other forced. -/
theorem guarded (age total balance amount : Int) :
    solspec!{ ensures (age == old(age) - amount)
              reverts_when (age < amount)
              modifies age
              [ require((amount <= age)); age -= amount ] }
      (store age total balance amount) := by
  sol_spec [store]

/-- A ghost assertion between two writes: proved where it stands, and an
assumption for what follows. -/
theorem ghost_step (age total balance amount : Int) :
    solspec!{ ensures (total == 1)
              modifies age, total
              < age = 1;
                ghost assert (age == 1);
                total = age > }
      (store age total balance amount) := by
  sol_spec [store]

/-- `push` grows the array by one, stated with `old(values.length)`. -/
theorem push_grows (xs : List SVal) (total : Int) :
    solspec!{ ensures (values.length == old(values.length) + 1)
              modifies values
              < values.push() = total > }
      (arrStore xs total) := by
  sol_spec [arrStore]

end SyntaxExamples
end Spec
end Solidity
