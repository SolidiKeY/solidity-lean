import Solidity.Tools.Verify

/-!
# `#verify` and `#counterexample`, pinned

Each verdict of `Tools/Verify.lean` once: a specification proved (with the
theorem as a `Try this:` suggestion), one refuted with a certified
counterexample (the kernel checked `¬ ⊨ spec[C]{f}`), one refuted by its
`assignable` frame, one refuted by a tested counterexample only (the layout
premise of a mapping is a `\forall` over a `uint`, which the certificate
cannot evaluate), one refuted by a failed `assert`, and one given up on: true,
but outside what `sol_spec_try` closes.  Then `#counterexample` on a formula.

Both read the scoped calculus (`open scoped Solidity.Core.Surface`,
`docs/intrinsic.md`): `#verify` states `⊨ spec[C]{f}` of the scoped
obligation (`Core.Valid`), and a certificate is the kernel's `¬ ⊨` of that
statement; `#counterexample` evaluates scoped formulas over the typed state
and the typed run with fuel (`Core.Fml.eval3`, `Tools/Counterexample.lean`).
-/

namespace Solidity.Examples.Verify

open Solidity.Tools
open scoped Core.Scoped

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

/-- The suggestion, pasted: the scoped obligation (`Core.Valid`). -/
theorem inc_spec : ⊨ spec[Counter]{inc} := by sol_spec

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
  fails: assignable count: dl{ find(old, total) = find(old, total) → find(storage, total) = find(old, total) }
-/
#guard_msgs in #verify Counter.incBoth

/-- `square()` is true (`x ≤ x * x` for `0 ≤ x`), but not linear: one goal
is left, and no counterexample is found. -/
def squareGoals : Lean.Elab.Term.TermElabM Nat := do
  match ← verifyFunction ``Counter "square" with
  | .gaveUp gs _ => pure gs.length
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

/-- A failed `assert` refutes the box with no clause to blame: the witness
says the run panicked. -/
def Guarded : Contract := contract!{
  uint count;
  function check(uint x) public {
    assert(x != 0);
    count = x;
  }
}

/--
info: ✗ check (certified):
  x = 0, msg.sender = 1, msg.value = 0
  before: count = 0
  after: panic (an `assert` failed)
-/
#guard_msgs in #verify Guarded.check

section
local instance : InContract := ⟨Counter⟩

-- `a` is a parameter, bound by `∀`: the search binds it, and `a = 1` passes the premise.
/--
info: counterexample (certified):
  a = 1, msg.sender = 1, msg.value = 0
  before: count = 0; total = 0
  after: count = 1; total = 0
-/
#guard_msgs in #counterexample dl!{ a == 1 → [ count = a; ] count == 2 }

/-- info: no counterexample found in 2000 candidates -/
#guard_msgs in #counterexample dl!{ [ count = a; ] count == a }

/-! A loop runs at most `loopFuel` iterations in the search (`Prog.trunF`,
the typed run with fuel): bounded by `a`, which the pools draw at
`2^256 - 1`, its run is `unknown` past them, not endless.  A loop that ends within them is
run, and its counterexample certified; `i` is the program's local, not a
parameter, so the witness binds nothing. -/

/-- info: no counterexample found in 2000 candidates -/
#guard_msgs in #counterexample dl!{ [ uint i = 0; while (i < a) { i++; }; ] i == a }

/--
info: counterexample (certified):
  msg.sender = 1, msg.value = 0
  before: count = 0; total = 0
  after: count = 0; total = 0
-/
#guard_msgs in #counterexample dl!{ [ uint i = 0; while (i < 3) { i++; }; ] i == 2 }
end

end Solidity.Examples.Verify
