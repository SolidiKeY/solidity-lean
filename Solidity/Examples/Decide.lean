import Solidity.Calculus.Decide

/-!
# `sol_decide`: the storage goals, decided

`sol_close` (`Calculus/Close.lean`) finishes a goal with `simp` and `grind`
on whatever facts the formula states; it cannot split on two keys being
equal.  `sol_decide` (`Calculus/Decide.lean`) rewrites the goal by an
equivalence, `Fml.valid_iff_reduce`, into a statement about the initial
state in which every read of a write is a case tree over key equalities,
and closes that.  Nothing is lost on the way, so a goal it does not close is
either not valid (the examples at the end), outside the fragment, or beyond
the final `simp`/`omega`/`grind` (mini-solkey's `Examples/Decide.lean`).

Every goal is stated with `⊨`, over **every** state: one whose `balances`
is an array, whose `alice.account.balance` holds a `bool`, or that has no
`alice` at all.  Under the box a write that halts proves the formula, so
the programs below may write anywhere; a read of the initial storage is
another matter (`deleteWithoutWrite`).
-/

namespace Solidity.Examples.Decide

open Proves Decide Semantics

local instance : InContract := ⟨StandardExample⟩

/-! ## Two symbolic keys

A write at `balances[j]` after one at `balances[k]` overwrites it when
`k = j`, and leaves it otherwise.  `sol_decide` splits on `k = j` itself:
the formula need not. -/

/-- `balances[k] = 5; balances[j] = 6; uint y = balances[k];` — `y` is `6`
where the keys meet and `5` where they do not.  `sol_close` does not close
it, the two cases stated in the formula notwithstanding. -/
theorem twoKeysBothWays :
    ⊨ dl!{ [ balances[k] = 5; balances[j] = 6; uint y = balances[k]; ]
           ((k == j → y == 6) ∧ (k != j → y == 5)) } := by
  sol_symex
  sol_decide

set_option maxHeartbeats 400000 in
example : ⊨ dl!{ [ balances[k] = 5; balances[j] = 6; uint y = balances[k]; ]
                 ((k == j → y == 6) ∧ (k != j → y == 5)) } := by
  sol_symex
  fail_if_success sol_close
  sol_decide

/-- `balances[k] = 5; balances[j] = 5;` — whichever key wins, `balances[k]`
reads `5`.  No hypothesis names `k = j`, so `sol_close` has no fact to
rewrite with and does not close it. -/
theorem sameValueEitherKey :
    ⊨ dl!{ [ balances[k] = 5; balances[j] = 5; ] balances[k] == 5 } := by
  sol_symex
  sol_decide

example : ⊨ dl!{ [ balances[k] = 5; balances[j] = 5; ] balances[k] == 5 } := by
  sol_symex
  fail_if_success sol_close
  sol_decide

/-- `a != b → balances[a] = 1; balances[b] = 2;` — the frame across two
keys the formula tells apart. -/
theorem twoKeys :
    ⊨ dl!{ a != b → [ balances[a] = 1; balances[b] = 2; ] balances[a] == 1 } := by
  sol_symex
  sol_decide

/-! ## Keys that are reads

A key can be a read itself, of the storage as the writes left it. -/

/-- `balances[a] = b; balances[b] = a;` — `balances[balances[a]]` reads at
the key `balances[a]` holds after both writes: `b` when `a ≠ b`, `a` when
they are equal, and in both cases the entry there is `a`. -/
theorem keyThroughKey :
    ⊨ dl!{ [ balances[a] = b; balances[b] = a; ] balances[balances[a]] == a } := by
  sol_symex
  sol_decide

/-- `balances[a] = 5; people[balances[a]].age = 7;` — the index of `people`
is a read of `balances`. -/
theorem nestedKey :
    ⊨ dl!{ [ balances[a] = 5; people[balances[a]].age = 7; ] people[5].age == 7 } := by
  sol_symex
  sol_decide

/-! ## Reads of the initial storage

No program at all: equal keys read equal words.  The reduction leaves the
reads of `balances[a]` and `balances[b]` as they are; `a == b` makes them
one. -/

theorem sameKeySameWord :
    ⊨ dl!{ balances[a] == c → balances[b] == d → a == b → c == d } := by
  sol_decide

/-! ## A swap, and a branch -/

/-- `uint t = balances[a]; uint u = balances[b]; balances[a] = u;
balances[b] = t;` — the two entries swapped, `a = b` included. -/
theorem swap :
    ⊨ dl!{ [ uint t = balances[a]; uint u = balances[b]; balances[a] = u; balances[b] = t; ]
           (balances[a] == u && balances[b] == t) } := by
  sol_symex
  sol_decide

/-- mini-solkey's `whichWriteWins`: the branch agrees with the key split. -/
theorem whichWriteWins :
    ⊨ dl!{ [ balances[a] = 1; balances[b] = 2; uint x = 0;
             if (a == b) { x = 2; } else { x = 1; }; ] balances[a] == x } := by
  sol_symex
  sol_decide

/-! ## Below a `delete`

A read at or below a deleted location, before any key, reads the default of
what was there (`find_defaultOf`): `0` for a `uint` that held one. -/

/-- `alice.account.balance = 100; delete alice.account;` — the member below
the deleted struct reads `0`.  The gap `Close.lean` lists: `sol_close` does
not read below a deleted struct. -/
theorem deleteBelow :
    ⊨ dl!{ [ alice.account.balance = 100; delete alice.account; ]
           alice.account.balance == 0 } := by
  sol_symex
  sol_decide

example : ⊨ dl!{ [ alice.account.balance = 100; delete alice.account; ]
                 alice.account.balance == 0 } := by
  sol_symex
  fail_if_success sol_close
  sol_decide

/-- The same through a local, and a member beside the deleted one kept. -/
theorem deleteBelowAndBeside :
    ⊨ dl!{ [ alice.account.balance = 100; alice.age = 30; delete alice.account;
             uint y = alice.account.balance; uint z = alice.age; ] (y == 0 && z == 30) } := by
  sol_symex
  sol_decide

/-- `people[a].age = 1; people[b].age = 2; delete people[a];` — the element
deleted reads `0` below it, and the other keeps its value when the indices
differ (mini-solkey's `deleteEntry_decide`).  `sol_close` does not finish it
within the default heartbeats. -/
theorem deleteEntry :
    ⊨ dl!{ [ people[a].age = 1; people[b].age = 2; delete people[a]; ]
           (people[a].age == 0 && (a != b → people[b].age == 2)) } := by
  sol_symex
  sol_decide

/-- `balances[k] = 5; balances[j] = 6; delete balances[j];` — the entry
beside the deleted one keeps its value, and the deleted one is `0`. -/
theorem deleteEntryBeside :
    ⊨ dl!{ [ balances[k] = 5; balances[j] = 6; delete balances[j]; uint r = balances[k]; ]
           ((k != j → r == 5) ∧ (k == j → r == 0)) } := by
  sol_symex
  sol_decide

/-! ## Under the diamond

A diamond update's term has to return, so it becomes a conjunct of the
reduction; the locals of the formula are read as they are. -/

/-- `a == 1 → ⟨ uint x = a; uint y = x + 1; ⟩ y == 2` — valid, since `a`
returns and `a + 1` is in range. -/
theorem diamondLocals :
    ⊨ dl!{ a == 1 → ⟨ uint x = a; uint y = x + 1; ⟩ y == 2 } := by
  sol_symex
  sol_decide

/-! ## Outside the fragment

A copy between storage locations (`alice = bob;`) writes a subtree, not a
word, and is outside the fragment; `sol_decide` says so. -/

example : True := by
  fail_if_success
    have : ⊨ dl!{ [ alice = bob; ] alice.age == bob.age } := by
      sol_symex
      sol_decide
  trivial

/-! ## Formulas that are not valid

`sol_decide` fails on them, and it is right to: the reduction is an
equivalence. -/

/-- Without `a != b` the frame fails where `a = b`. -/
example : True := by
  fail_if_success
    have : ⊨ dl!{ [ balances[a] = 1; balances[b] = 2; ] balances[a] == 1 } := by
      sol_symex
      sol_decide
  trivial

/-- A storage in which `alice.account.balance` holds a `bool`. -/
def boolBalance : State :=
  { storage := [("alice", .struct [("account", .struct [("balance", .bool true)])])] }

/-- **`delete` without a write before it is not valid**: where the old
member was a `bool`, the delete leaves `false`, not `0`.  What a read below
a delete returns is the default of the old *value*, and `⊨` does not know
the old value's type; `deleteBelow` fixes it by writing first.  With a
well-typed storage as a premise it would be valid — a hypothesis `⊨` cannot
state. -/
theorem deleteWithoutWrite :
    ¬ (⊨ dl!{ [ delete alice.account; ] alice.account.balance == 0 }) :=
  fun h => nomatch h boolBalance

example : True := by
  fail_if_success
    have : ⊨ dl!{ [ delete alice.account; ] alice.account.balance == 0 } := by
      sol_symex
      sol_decide
  trivial

/-! ## The ledger of `Examples/LedgerDelete.lean`

`Ledger` is `nonce` beside the mapping `balances`. -/

section Ledger

local instance : InContract := ⟨TestSuite⟩

/-- The whole program of `LedgerDelete.lean`, both `delete`s included, in
one call: `ledger.nonce = 5; ledger.balances[1] = 10; ledger.balances[2] = 20;
delete ledger.balances[1]; uint gone = ledger.balances[1];
uint kept = ledger.balances[2]; uint before = ledger.nonce; delete ledger;
uint after = ledger.nonce; uint survives = ledger.balances[2];`.
`LedgerDelete.lean` closes the first three reads with `sol_close` and runs
the interpreter for the last two. -/
theorem ledger :
    ⊨ dl!{ [ ledger.nonce = 5; ledger.balances[1] = 10; ledger.balances[2] = 20;
             delete ledger.balances[1];
             uint gone = ledger.balances[1]; uint kept = ledger.balances[2];
             uint before = ledger.nonce;
             delete ledger;
             uint after = ledger.nonce; uint survives = ledger.balances[2]; ]
           (gone == 0 && kept == 20 && before == 5 && after == 0 && survives == 20) } := by
  sol_symex
  sol_decide

/-- **What survives `delete ledger`**: a `delete` keeps a mapping's
entries and empties an array, and `⊨` includes states where
`ledger.balances` is either.  Where it is a mapping `survives` is `20`;
where it is an array the read reverts, which the box allows.  The reduction
guards the read below the key by the location above the key being a
mapping (`LStor.mapU`). -/
theorem survives :
    ⊨ dl!{ [ ledger.balances[2] = 20; delete ledger; uint survives = ledger.balances[2]; ]
           survives == 20 } := by
  sol_symex
  sol_decide

end Ledger

end Solidity.Examples.Decide
