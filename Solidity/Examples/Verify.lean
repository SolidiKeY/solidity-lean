import Solidity.Tools.Verify

/-!
# `#verify` and `#counterexample`, pinned

Each verdict of `Tools/Verify.lean` once: a specification proved (with the
theorem as a `Try this:` suggestion), one refuted with a certified
counterexample (the kernel checked `¬ ⊨ spec[C]{f}`), one refuted by its
`assignable` frame, one whose mapping-layout premise is proved structurally
rather than by finite evaluation, one refuted by a failed `assert`, and one given up on: true,
but outside what `sol_spec_try` closes.  Then `#counterexample` on a formula,
and on a contract with a struct, both arrays and a mapping.

Both read the scoped calculus (`open scoped Solidity.Scoped`,
`docs/intrinsic.md`): `#verify` states `⊨ spec[C]{f}` of the scoped
obligation (`Valid`), and a certificate is the kernel's `¬ ⊨` of that
statement; `#counterexample` evaluates scoped formulas over the typed state
and the typed run with fuel (`Fml.eval3`, `Tools/Counterexample.lean`).
-/

namespace Solidity.Examples.Verify

open Solidity.Tools
open scoped Scoped

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

/-- The suggestion, pasted: the scoped obligation (`Valid`). -/
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
info: ✗ credit (certified):
  a = 0, msg.sender = 0, msg.value = 0
  before: balances = {0: 1, _: 0}
  after: balances = {0: 1, _: 0}
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
  x = 0, msg.sender = 0, msg.value = 0
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

/-! A loop runs at most `loopFuel` iterations in the search (`Prog.runF`,
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

/-- A struct, a fixed array, a dynamic array and a mapping: the certificate
quotes each (`quoteFold`, `Cand.quote`). -/
def Shapes : Contract := contract!{
  Person alice;
  uint[2] pair;
  uint[] xs;
  mapping(uint => uint) bal;
}

section
local instance : InContract := ⟨Shapes⟩

-- Refuted only where every shape holds something: the random search draws
-- such a storage, and the kernel checks it quoted.
/--
info: counterexample (certified):
  msg.sender = 1, msg.value = 0
  before: alice = {account: {balance: 1, token: {value: 2}}, age: 2}; pair = [1, 3]; xs = [3, 3]; bal = {1: 3, _: 0}
  after: alice = {account: {balance: 1, token: {value: 2}}, age: 1}; pair = [1, 3]; xs = [3, 3]; bal = {1: 3, _: 0}
-/
#guard_msgs in #counterexample dl!{ [ alice.age = 1; ]
  (xs.length == 0 ∨ bal[1] == 0 ∨ pair[0] == 0 ∨ alice.account.balance == 0) }
end

/-- Declaration ranges include struct fields, nested mappings, signed keys
and values, and boolean keys and values. Arrays retain their partial reads. -/
def Declarations : Contract := contract!{
  mapping(uint => Person) people;
  mapping(int => mapping(bool => int)) debts;
  mapping(bool => bool) flags;
  uint[] xs;
}

/-- These are the actual generated premises, compiled by the specification
reader. Compilation errors are reported, never silently dropped. -/
def declarationRanges : Fml Declarations [] :=
  declaration_facts[Declarations]

theorem declarationRanges_valid : ⊨ declarationRanges := by sol_decl_facts

section
local instance : InContract := ⟨Declarations⟩

/-- A declaration supplies a range, not a particular stored value. -/
example : True := by
  fail_if_success
    have : ⊨ dl!{ ∀ uint k; people[k].age == 0 } := by sol_decl_facts
  trivial

/-- An array's index can fail even though its element type is a uint. -/
example : True := by
  fail_if_success
    have : ⊨ dl!{ 0 <= xs[0] ∧ xs[0] <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 } := by
      sol_decl_facts
  trivial

/-- A false quantified entry clause must not be treated as a declaration
fact when the fallback assembles a refutation of the original implication. -/
def refusesFalsePremise : Lean.Elab.Term.TermElabM Bool := do
  let c : Cand Declarations := { st := Storage.init Declarations, args := [] }
  let φ : Fml Declarations [] := dl!{ (∀ uint k; people[k].age == 1) → false }
  let cE := Lean.mkConst ``Declarations
  certifyDeclarations cE (Fml.quote cE φ) [] [] c

/-- info: false -/
#guard_msgs in #eval refusesFalsePremise

end

end Solidity.Examples.Verify
