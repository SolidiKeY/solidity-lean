import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Closer
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

/-!
# `sol_decide`: the storage and memory goals, decided

`sol_close` (`Calculus/Close.lean`) finishes a goal with `simp` and `grind`
on whatever facts the formula states; it cannot split on two keys being
equal.  `sol_decide` (`Calculus/DecideComplete.lean`) pushes the leaf's
updates in, its locals and its binders' locals by position (`Fml.toLS`,
`Calculus/DecideScoped.lean`), into a formula over the initial typed state
(`LFml`, `Calculus/DecideLang.lean`) in which every read of a write is a
case tree over key equalities.  It eliminates the writes
(`LFml.elimF`, `Calculus/ElimFacts.lean`), reads memory as solkey does
(`Calculus/MemRead.lean`), and closes what is left with the closer
(`Calculus/Closer.lean`); the kernel evaluates all of it once
(`Valid.of_close`).  Each step is sound over the typed state
(`Valid.of_toLS`, `Calculus/DecideTyped.lean`), not an equivalence, so a
goal `sol_decide` does not close may still be valid.

Every goal is stated with `⊨`, which (under `open scoped Scoped`) ranges
over typed states: a parameter is a word of its type, in range, and the
storage holds the layout its contract declares (`balances` is a mapping,
`alice.account.balance` a `uint`).  Under the box a write that halts proves
the formula, so the programs below may write anywhere.
-/

namespace Solidity.Examples.Tactics.Decide

open Decide Semantics

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## Two symbolic keys

A write at `balances[j]` after one at `balances[k]` overwrites it when
`k = j`, and leaves it otherwise.  `sol_decide` splits on `k = j` itself:
the formula need not. -/

set_option maxHeartbeats 400000 in
/-- `balances[k] = 5; balances[j] = 6; uint y = balances[k];` — `y` is `6`
where the keys meet and `5` where they do not.  `sol_close` closes it too,
from the two cases the formula states (W9.8.4: a case `k == j` makes the
two typed references one). -/
theorem twoKeysBothWays :
    ⊨ dl!{ [ balances[k] = 5; balances[j] = 6; uint y = balances[k]; ]
           ((k == j → y == 6) ∧ (k != j → y == 5)) } := by
  sol_symex
  sol_decide

example : ⊨ dl!{ [ balances[k] = 5; balances[j] = 6; uint y = balances[k]; ]
    ((k == j → y == 6) ∧ (k != j → y == 5)) } := by
  sol_symex
  sol_close

/-- `balances[k] = 5; balances[j] = 5;` — whichever key wins, `balances[k]`
reads `5`.  No hypothesis names `k = j`, so `sol_close` has no fact to
rewrite with and does not close it. -/
theorem sameValueEitherKey :
    ⊨ dl!{ [ balances[k] = 5; balances[j] = 5; ] balances[k] == 5 } := by
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
the deleted struct reads `0`.  `sol_close` reads it too (W9.8.4: the typed
delete's member below, `SVal.find_defaultOf_field`). -/
theorem deleteBelow :
    ⊨ dl!{ [ alice.account.balance = 100; delete alice.account; ]
           alice.account.balance == 0 } := by
  sol_symex
  sol_decide

example : ⊨ dl!{ [ alice.account.balance = 100; delete alice.account; ]
    alice.account.balance == 0 } := by
  sol_symex
  sol_close

/-- The same through a local, and a member beside the deleted one kept. -/
theorem deleteBelowAndBeside :
    ⊨ dl!{ [ alice.account.balance = 100; alice.age = 30; delete alice.account;
             uint y = alice.account.balance; uint z = alice.age; ] (y == 0 && z == 30) } := by
  sol_symex
  sol_decide

/-- **`delete` without a write before it**: the member below reads the
default of its declared type, `0`.  (The premise `wt(storage)` once stood
in for the typing the erased storage dropped.) -/
theorem deleteWithoutWrite :
    ⊨ dl!{ defined(wt(storage)) → [ delete alice.account; ] alice.account.balance == 0 } := by
  sol_prove

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
can hang on how they constrain each other: an array has its elements at the
indices below its length, a mapping has every key.  A read that returns
states its guards (the index below the length, the location there), and
the closer reads the later ones under them. -/

/-- `uint y = values[5];` then `values[3] = 1;` — where `values[5]` is
there, `values` is longer than `5`, so `values[3]` is there to write. -/
theorem belowAnIndex : ⊨ dl!{ [ uint y = values[5]; ] ⟨ values[3] = 1; ⟩ true } := by
  sol_symex
  sol_decide

/-- `uint y = matrix[i][j];` then `matrix[i][0] = 1;` — the row
`matrix[i]` has an element, so it has a first one. -/
theorem firstOfARow : ⊨ dl!{ [ uint y = matrix[i][j]; ] ⟨ matrix[i][0] = 1; ⟩ true } := by
  sol_symex
  sol_decide

/- `negativeKey`: `uint y = values[-1];` — the typed elaborator refuses
it: `-1` is no `uint`, as solc refuses it (`docs/intrinsic.md`, decision
79). -/
/--
error: Solidity elaboration failed: operator - does not take uint
-/
#guard_msgs in #check dl!{ [ uint y = values[-1]; ] ⟨ values[7] = 1; ⟩ true }

/-- `uint y = alice.account.balance;` then `delete alice.account;` — a read
above one that returns: `alice.account` is there, so it can be deleted. -/
theorem aboveARead :
    ⊨ dl!{ [ uint y = alice.account.balance; ] ⟨ delete alice.account; ⟩ true } := by
  sol_symex
  sol_decide

/-- `uint y = values[3]; uint n = values.length;` — `values[3]` is below
the length. -/
theorem lengthAboveIndex :
    ⊨ dl!{ [ uint y = values[3]; uint n = values.length; ] n != 3 } := by
  sol_symex
  sol_decide

/-- `uint y = values[i]; uint n = values.length; bool c = i < n;` — an
index read in bounds, the bound being the length. -/
theorem indexBelowLength :
    ⊨ dl!{ [ uint y = values[i]; uint n = values.length; bool c = i < n; ] c == true } := by
  sol_symex
  sol_decide

/-- `values[2] = 7; uint n = values.length; delete values; uint m =
values.length;` — a `delete` empties a dynamic array and keeps a
fixed-size one's length. -/
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

/-! ## The parameters, typed

A parameter is a `uint`: it returns, in range.  The leaf's erasure read it
as a name bound to anything (no value, a `bool`), where neither formula
below is valid. -/

/-- `⟨ uint x = a; ⟩ x == a` — `a` returns. -/
theorem parameterReturns : ⊨ dl!{ ⟨ uint x = a; ⟩ x == a } := by
  sol_symex
  sol_decide

/-- `a < 10 → ⟨ uint y = a + 1; ⟩ y == a + 1` — `a + 1` does not overflow. -/
theorem parameterInRange : ⊨ dl!{ a < 10 → ⟨ uint y = a + 1; ⟩ y == a + 1 } := by
  sol_symex
  sol_decide

/-! ## The closer on the reduction

`sol_decide` is the closer on the reduction (`Valid.of_close`);
`sol_decide_close` is the same step, failing where the closer does not
close the leaf, and `sol_reduce` shows the reduction. -/

/-- `⟨ uint x = a; ⟩ x >= 0` — the order a `uint` parameter's range gives
is the closer's. -/
theorem closerOnReduction : ⊨ dl!{ ⟨ uint x = a; ⟩ x >= 0 } := by
  sol_symex
  sol_decide_close

/-! ## Two elements in one update, and the layout

An update of two elements both read in the state it is applied in
(`{x := x + 1 ‖ se1 := x}`, what `x++` inside an expression leaves) is
pushed in element by element, each read before the update.  A premise
`wt(storage)` holds in every typed state; the closer reads it as `true`. -/

/-- `values[0] = x++;` — the slot holds the old `x`, and `x` the next. -/
theorem postIncrementParallel :
    ⊨ dl!{ a < 10 → [ uint x = a; values[0] = x++; ] (x == a + 1 && values[0] == a) } := by
  sol_symex
  sol_decide

/-- `deleteWithoutWrite` by the closer alone: `alice.account` is at its
declared type, so its member reads `0` after the `delete`. -/
theorem deleteWithoutWriteScoped :
    ⊨ dl!{ defined(wt(storage)) → [ delete alice.account; ] alice.account.balance == 0 } := by
  sol_symex
  sol_decide_close

/-! ## Pushes, pops and copies

A push or a pop is one write of the array: a read below it compares its
index with the old length, and the length after it is the old one plus or
minus one.  A copy between storage locations (`alice = bob;`) writes a
subtree, read through its source. -/

/-- `values.push(3);` — the array is not empty after it. -/
theorem pushLength :
    ⊨ dl!{ [ values.push(3); uint n = values.length; ] n > 0 } := by
  sol_symex
  sol_decide

/-- `values.push(3);` — the pushed word is the last element. -/
theorem pushReadBack :
    ⊨ dl!{ [ values.push(3); uint r = values[values.length - 1]; ] r == 3 } := by
  sol_symex
  sol_decide

/-- A `pop` after a `push` gives the length back. -/
theorem pushPopLength :
    ⊨ dl!{ [ uint n = values.length; values.push(3); values.pop(); uint m = values.length; ]
           m == n } := by
  sol_symex
  sol_decide

/-- `alice = bob;` — a member of the copy is the source's. -/
theorem copyReadsSource :
    ⊨ dl!{ [ alice = bob; uint x = bob.age; ] alice.age == x } := by
  sol_symex
  sol_decide

/-! ## Formulas valid over typed states

Over the erased storage `sol_decide` once read, these two were left open:
there `bob` need not have an `age`, and `balances` may be an array.  The
typed reading closes them. -/

/-- `alice = bob;` — the copy's member is the source's, with nothing in the
program reading `bob.age` first. -/
theorem copyFrame : ⊨ dl!{ [ alice = bob; ] alice.age == bob.age } := by
  sol_symex
  sol_decide

/-- `balances` is a mapping: every key is there to write. -/
theorem mappingEveryKey : ⊨ dl!{ [ uint y = balances[k]; ] ⟨ balances[j] = 1; ⟩ true } := by
  sol_symex
  sol_decide

/-! ## Formulas `sol_decide` does not close

Neither is valid. -/

/-- Without `a != b` the frame fails where `a = b`. -/
example : True := by
  fail_if_success
    have : ⊨ dl!{ [ balances[a] = 1; balances[b] = 2; ] balances[a] == 1 } := by
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


/-! ## The ledger of `Examples/Tactics/LedgerDelete.lean`

`Ledger` is `nonce` beside the mapping `balances`. -/

section Ledger

local instance : InContract := ⟨TestSuite⟩

open scoped Scoped

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

/-- **What survives `delete ledger`**: a `delete` keeps a mapping's
entries, and `ledger.balances` is the mapping `TestSuite` declares, so
`survives` is `20` (`survivesMappingOnly`); the disjunction once stated
what the erased storage allowed. -/
theorem survives :
    ⊨ dl!{ [ ledger.balances[2] = 20; delete ledger; uint survives = ledger.balances[2]; ]
           (survives != 20 → survives == 0) } := by
  sol_symex
  sol_decide

/-- **`survives` is `20`**: `ledger.balances` is the mapping `TestSuite`
declares, whose entries a `delete` keeps. -/
theorem survivesMappingOnly :
    ⊨ dl!{ defined(wt(storage)) →
      [ ledger.balances[2] = 20; delete ledger; uint survives = ledger.balances[2]; ]
        survives == 20 } := by
  sol_prove


/-- `fixedValues[1] = 7; delete fixedValues; uint x = fixedValues[1];` —
`fixedValues` is a `uint[3]`, whose elements a `delete` resets in place. -/
theorem fixedDelete :
    ⊨ dl!{ [ fixedValues[1] = 7; delete fixedValues; uint x = fixedValues[1]; ]
           (x != 7 → x == 0) } := by
  sol_symex
  sol_decide


end Ledger

/-! ## Memory through the closer

A memory is read as solkey reads it (`Calculus/MemRead.lean`): the writes
are walked from the newest down to the allocation of the name's root, each
step a law of `Theory/Typed/Mem.lean` by its solkey name, and no default
value is ever built, so a long `new` costs what a short one does. -/

/-- `Person memory carol; carol.age = 5;` — the pair, a member write, and
the read of it (`readOnWrite`). -/
theorem memoryFieldWriteRead :
    ⊨ dl!{ [ Person memory carol; carol.age = 5; uint x = carol.age; ] x == 5 } := by
  sol_symex
  sol_decide

/-- A member nothing wrote is its default (`initMember`). -/
theorem memoryFieldDefault :
    ⊨ dl!{ [ Person memory carol; uint x = carol.age; ] x == 0 } := by
  sol_symex
  sol_decide

/-- A write and a read at an index that is no literal: one `kite` on the
index, the write's guard the length. -/
theorem memoryIndexSymbolic :
    ⊨ dl!{ [ uint[] memory xs = new uint[](3); xs[i] = 7; uint y = xs[i]; ] y == 7 } := by
  sol_symex
  sol_decide

/-- A million elements: the length is read off `new`, nothing allocated. -/
theorem memoryNewLarge :
    ⊨ dl!{ [ uint[] memory xs = new uint[](1000000); xs[5] = 7; uint y = xs[5];
             uint l = xs.length; ] (y == 7 ∧ l == 1000000) } := by
  sol_symex
  sol_decide

/-- `delete carol.account;` writes a fresh default `Account` into the member
(`memoryFieldDeleteReference`): its balance reads `0` again. -/
theorem memoryDeleteRefFresh :
    ⊨ dl!{ [ Person memory carol; Account memory acc = carol.account; acc.balance = 9;
             delete carol.account; uint b = carol.account.balance; ] b == 0 } := by
  sol_symex
  sol_decide

/-- `Person memory carol = alice;` copies the storage in
(`memoryStorageCopy`); a later write to `alice` is not seen (`readCopySt`
reads the storage of the copy). -/
theorem memoryStorageCopyRead :
    ⊨ dl!{ [ alice.age = 27; Person memory carol = alice; alice.age = 30;
             uint x = carol.age; ] x == 27 } := by
  sol_symex
  sol_decide

/-- `alice = carol;` copies memory out (`memoryToStorageStoreRoot`, the
copy of `carol` laid over `alice`); the storage reads what was copied
(`findCopyMem`), so a later write to `carol` is not seen. -/
theorem memoryToStorageRead :
    ⊨ dl!{ [ Person memory carol; carol.age = 42; alice = carol; carol.age = 43;
             uint x = alice.age; ] x == 42 } := by
  sol_symex
  sol_decide

end Solidity.Examples.Tactics.Decide

/-! ## On the closer's formulas

The fragment is where the leaf's updates push in (`Fml.toLS`,
`Calculus/DecideScoped.lean`), checked on the scoped leaf itself. -/

namespace Solidity.Examples.Tactics.Decide

open Decide Semantics

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-- info: false -/
#guard_msgs in -- a read of the ledger is outside the fragment
#eval ((dl!{ { y := net(a) } y = 0 }).toLS true Solidity.Decide.SymS.init).isSome

end Solidity.Examples.Tactics.Decide
