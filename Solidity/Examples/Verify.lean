import Solidity.Tools.Verify

/-!
# `#verify` and `#counterexample`, pinned

Each verdict of `Tools/Verify.lean` once: a specification proved (with the
theorem as a `Try this:` suggestion), one refuted with a certified
counterexample (the kernel checked `¬ ⊨ spec[C]{f}`), one refuted by its
`assignable` frame, one refuted by a tested counterexample only (the layout
premise of a mapping is a `\forall` over a `uint`, which the certificate
cannot evaluate), and one stuck: true, but outside what `sol_spec_try`
closes.  Then `#counterexample` on a formula.
-/

namespace Solidity.Examples.Verify

open Solidity.Tools

def Counter : Contract := contract!{
  uint count;
  uint total;
  ensures count == \old(count) + 1;
  function inc() public {
    count += 1;
  }
  ensures count == \old(count) + 2;
  function incTwice() public {
    count += 1;
  }
  ensures count == \old(count) + 1;
  assignable count;
  function incBoth() public {
    count += 1;
    total += 1;
  }
  requires count < 1000;
  ensures count >= \old(count);
  function square() public {
    count = count * count;
  }
}

/--
info: ✓ inc
---
info: Try this:
  theorem inc_spec : ⊨ spec[Counter]{inc} := by sol_spec
-/
#guard_msgs in #verify Counter.inc

/--
info: ✗ incTwice (certified):
  msg.sender = 1, msg.value = 0
  before: count = 0; total = 0
  after: count = 1; total = 0
  fails: ensures count == \old(count) + 2
-/
#guard_msgs in #verify Counter.incTwice

/--
info: ✗ incBoth (certified):
  msg.sender = 1, msg.value = 0
  before: count = 0; total = 0
  after: count = 1; total = 1
  fails: assignable count: dl{ select(old, total) = select(old, total) → select(storage, total) = select(old, total) }
-/
#guard_msgs in #verify Counter.incBoth

/-- `square()` is true (`x ≤ x * x` for `0 ≤ x`), but not linear: one goal
is left, and no counterexample is found. -/
def squareGoals : Lean.Elab.Term.TermElabM Nat := do
  match ← verifyFunction ``Counter "square" with
  | .stuck gs _ => pure gs.length
  | _ => pure 0

/-- info: 1 -/
#guard_msgs in #eval squareGoals

def Bank : Contract := contract!{
  mapping(address => uint) balances;
  ensures balances[a] == \old(balances[a]) + 1;
  function credit(address a) public {
    balances[a] = 1;
  }
}

/--
info: ✗ credit (tested):
  a = 2, msg.sender = 1, msg.value = 0
  before: balances = {2: 1, _: 0}
  after: balances = {2: 1, _: 0}
  fails: ensures balances[a] == \old(balances[a]) + 1
-/
#guard_msgs in #verify Bank

section
local instance : InContract := ⟨Counter⟩

-- `a` is a free local: the search binds it, and `a = 1` passes the premise.
/--
info: counterexample (certified):
  a = 1, msg.sender = 1, msg.value = 0
  before: count = 0; total = 0
  after: count = 1; total = 0
-/
#guard_msgs in #counterexample dl!{ a == 1 → [ count = a; ] count == 2 }

/-- info: no counterexample found in 2000 candidates -/
#guard_msgs in #counterexample dl!{ [ count = a; ] count == a }
end

end Solidity.Examples.Verify
