import Solidity.Calculus.DecideComplete

/-!
# `sol_decide`: the storage goals, decided

`sol_close` (`Calculus/Close.lean`) finishes a goal with `simp` and `grind`
on whatever facts the formula states; it cannot split on two keys being
equal.  `sol_decide` (`Calculus/Decide.lean`) rewrites the goal by an
equivalence, `Fml.valid_iff_reduce`, into a statement about the initial
state in which every read of a write is a case tree over key equalities;
then by a second one, `Fml.valid_iff_cons` (`Calculus/DecideComplete.lean`),
into a statement about free reads under the constraints a storage puts on
them, and closes that.  Nothing is lost on the way, so a goal it does not
close is either not valid (the examples at the end), outside the fragment,
or beyond the final `omega`/`grind`.

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

/-! ## Reads that constrain each other

Two reads of the initial storage are atoms of the reduction, and a valid goal
can hang on how they constrain each other: a location below a word shows
nothing, an array has its elements at the indices below its length, a
mapping has every key.  `sol_decide` states those constraints (`consAll`:
for each read path, `ChildOk` between the location it names and the one
above) and decides the goal under them.  Nothing is lost, since any choice
of reads that meets them is what some storage shows (`realize_findLive`).
The reduction alone, read with unrelated atoms (`sol_decide_unconstrained`),
does not close any of these. -/

/-- `uint y = values[5];` then `values[3] = 1;` — where `values[5]` is
there, `values` is a mapping or an array longer than `5`, and either way
`values[3]` is there to write. -/
theorem belowAnIndex : ⊨ dl!{ [ uint y = values[5]; ] ⟨ values[3] = 1; ⟩ true } := by
  sol_symex
  fail_if_success sol_decide_unconstrained
  sol_decide

/-- `uint y = matrix[i][j];` then `matrix[i][0] = 1;` — the row
`matrix[i]` has an element, so it has a first one. -/
theorem firstOfARow : ⊨ dl!{ [ uint y = matrix[i][j]; ] ⟨ matrix[i][0] = 1; ⟩ true } := by
  sol_symex
  fail_if_success sol_decide_unconstrained
  sol_decide

/-- `uint y = values[-1];` then `values[7] = 1;` — no array has an element
at `-1`, so `values` is a mapping, which has every key. -/
theorem negativeKey : ⊨ dl!{ [ uint y = values[-1]; ] ⟨ values[7] = 1; ⟩ true } := by
  sol_symex
  fail_if_success sol_decide_unconstrained
  sol_decide

/-- `uint y = alice.account.balance;` then `delete alice.account;` — a read
above one that returns: `alice.account` is there, so it can be deleted. -/
theorem aboveARead :
    ⊨ dl!{ [ uint y = alice.account.balance; ] ⟨ delete alice.account; ⟩ true } := by
  sol_symex
  fail_if_success sol_decide_unconstrained
  sol_decide

/-- `uint y = values[3]; uint n = values.length;` — `values.length` reads an
array, and `values[3]` is below its length. -/
theorem lengthAboveIndex :
    ⊨ dl!{ [ uint y = values[3]; uint n = values.length; ] n != 3 } := by
  sol_symex
  fail_if_success sol_decide_unconstrained
  sol_decide

/-- `uint y = values[i]; uint n = values.length; bool c = i < n;` — an
index read in bounds, the bound being the length. -/
theorem indexBelowLength :
    ⊨ dl!{ [ uint y = values[i]; uint n = values.length; bool c = i < n; ] c == true } := by
  sol_symex
  fail_if_success sol_decide_unconstrained
  sol_decide

/-- `values[2] = 7; uint n = values.length; delete values; uint m =
values.length;` — a `delete` empties a dynamic array and keeps a
fixed-size one's length (`LStor.lenU`). -/
theorem lengthAfterDelete :
    ⊨ dl!{ [ values[2] = 7; uint n = values.length; delete values; uint m = values.length; ]
           (m != 0 → m == n) } := by
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

/-- An index read does not make another one of the same array in bounds:
`balances` may be an array longer than `k` and no longer than `j`. -/
example : True := by
  fail_if_success
    have : ⊨ dl!{ [ uint y = balances[k]; ] ⟨ balances[j] = 1; ⟩ true } := by
      sol_symex
      sol_decide
  trivial

/-- An empty array has no last element. -/
example : True := by
  fail_if_success
    have : ⊨ dl!{ [ uint n = values.length; ] ⟨ values[n - 1] = 0; ⟩ true } := by
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

set_option maxHeartbeats 1600000 in
/-- The whole program of `LedgerDelete.lean`, both `delete`s included, in
one call: `ledger.nonce = 5; ledger.balances[1] = 10; ledger.balances[2] = 20;
delete ledger.balances[1]; uint gone = ledger.balances[1];
uint kept = ledger.balances[2]; uint before = ledger.nonce; delete ledger;
uint after = ledger.nonce; uint survives = ledger.balances[2];`.
`LedgerDelete.lean` closes the first three reads with `sol_close` and runs
the interpreter for the last two.  What `survives` is depends on what
`ledger.balances` is in the state, below. -/
theorem ledger :
    ⊨ dl!{ [ ledger.nonce = 5; ledger.balances[1] = 10; ledger.balances[2] = 20;
             delete ledger.balances[1];
             uint gone = ledger.balances[1]; uint kept = ledger.balances[2];
             uint before = ledger.nonce;
             delete ledger;
             uint after = ledger.nonce; uint survives = ledger.balances[2]; ]
           (gone == 0 && kept == 20 && before == 5 && after == 0 &&
             (survives != 20 → survives == 0)) } := by
  sol_symex
  sol_decide

/-- **What survives `delete ledger`**: a `delete` keeps a mapping's entries,
resets a fixed-size array's elements in place, and empties a dynamic array,
and `⊨` includes states where `ledger.balances` is any of them.  Where it is a
mapping `survives` is `20`; where it is a fixed-size array (a `uint[3]`, say)
it is `0`; where it is a dynamic array the read reverts, which the box allows.
The reduction tests the location above the key for a mapping, then for a
fixed-size array (`delBelow`, `LStor.mapU`). -/
theorem survives :
    ⊨ dl!{ [ ledger.balances[2] = 20; delete ledger; uint survives = ledger.balances[2]; ]
           (survives != 20 → survives == 0) } := by
  sol_symex
  sol_decide

/-- A storage in which `ledger.balances` is a fixed-size array of three
`uint`s. -/
def fixedBalances : State :=
  { storage := [("ledger", .struct [("nonce", .int 0),
      ("balances", .array [.int 0, .int 0, .int 0] [] true)])] }

/-- `fixedValues[1] = 7; delete fixedValues; uint x = fixedValues[1];` — `x` is
`0` where `fixedValues` holds a fixed-size array (`delete` resets its elements
in place), `7` where it holds a mapping (which `delete` leaves alone: a state
`⊨` quantifies over), and the read reverts where it holds a dynamic array. -/
theorem fixedDelete :
    ⊨ dl!{ [ fixedValues[1] = 7; delete fixedValues; uint x = fixedValues[1]; ]
           (x != 7 → x == 0) } := by
  sol_symex
  sol_decide

/-- **`survives == 20` alone is not valid**: where `ledger.balances` is a
fixed-size array, `delete ledger` resets its element `2` to `0`. -/
theorem survivesMappingOnly :
    ¬ (⊨ dl!{ [ ledger.balances[2] = 20; delete ledger; uint survives = ledger.balances[2]; ]
              survives == 20 }) :=
  fun h => nomatch h fixedBalances

end Ledger

end Solidity.Examples.Decide
