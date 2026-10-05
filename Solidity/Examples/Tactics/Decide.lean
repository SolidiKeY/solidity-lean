import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Closer

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

namespace Solidity.Examples.Tactics.Decide

open Proves Decide Semantics

local instance : InContract := ⟨StandardExample⟩

/-! ## Two symbolic keys

A write at `balances[j]` after one at `balances[k]` overwrites it when
`k = j`, and leaves it otherwise.  `sol_decide` splits on `k = j` itself:
the formula need not. -/

set_option maxHeartbeats 400000 in
/-- `balances[k] = 5; balances[j] = 6; uint y = balances[k];` — `y` is `6`
where the keys meet and `5` where they do not.  `sol_close` does not close
it, the two cases stated in the formula notwithstanding. -/
theorem twoKeysBothWays :
    ⊨ dl!{ [ balances[k] = 5; balances[j] = 6; uint y = balances[k]; ]
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

/-! ## Pushes, pops and copies

A push or a pop is one write of the array (`LStor.arr`): a read below it
compares its index with the old length, and the length after it is the old
one plus or minus one, counted unchecked.  A copy between storage locations
(`alice = bob;`, `LStor.copy`) writes a subtree, read through its source. -/

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

/-! ## Formulas that are not valid

`sol_decide` fails on them, and it is right to: the reduction is an
equivalence. -/

/-- Over every state `bob` need not have an `age` (it may hold a word),
and nothing in the program reads it, so the equation may compare two reads
that halt.  With `uint x = bob.age;` in the program it is valid
(`copyReadsSource`). -/
example : True := by
  fail_if_success
    have : ⊨ dl!{ [ alice = bob; ] alice.age == bob.age } := by
      sol_symex
      sol_decide
  trivial

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
  fun h => match (h boolBalance).1 with
    | ⟨_, _, he⟩ => nomatch Theory.StValue.Equiv.prim_iff.1 he

example : True := by
  fail_if_success
    have : ⊨ dl!{ [ delete alice.account; ] alice.account.balance == 0 } := by
      sol_symex
      sol_decide
  trivial

/-! ## The ledger of `Examples/Tactics/LedgerDelete.lean`

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
  fun h => match (h fixedBalances).1 with
    | ⟨_, _, he⟩ => nomatch Theory.StValue.Equiv.prim_iff.1 he

end Ledger

/-! ## The memory clauses

A memory is read as solkey reads it (`Calculus/MemRead.lean`): the writes are
walked from the newest down to the allocation of the name's root, every
comparison static.  Each clause is pinned here on a memory written out, and
on programs at the end of the file.  `alice` copied into memory is the
allocation `0`, a fresh `Person` the allocation `1`. -/

section MemoryClauses

open Solidity.Decide

/-- `Person memory p;` -/
private def pNew : LMem := .addM .init 0 (.struct "Person")
/-- `p.age = 5;` -/
private def pAge : LMem := .write pNew ⟨0, []⟩ (.fld "age") (.word (.lit (.int 5)))
/-- `uint[] memory xs = new uint[](3); xs[i] = 7;` -/
private def xsNew : LMem :=
  .write (.newArr .init 0 (.array .uint) (.lit (.int 3))) ⟨0, []⟩ (.idx (.var (.user "i")))
    (.word (.lit (.int 7)))
/-- `Person memory a = alice; Person memory q;` -/
private def aCopy : LMem := .addM (.copySt .init 0 .init (.root "alice")) 1 (.struct "Person")

/-- info: true -/
#guard_msgs in -- `readOnWrite`: the slot written reads the word written
#eval pAge.readT ⟨0, []⟩ (.fld "age") == some (.lit (.int 5))

/-- info: true -/
#guard_msgs in -- `readOnAddM`, `initMember`, `defaultValueInt`: a default member
#eval pNew.readT ⟨0, []⟩ (.fld "age") == some (.lit (.int 0))

/-- info: true -/
#guard_msgs in -- `initIdentity`: a reference member is the name one segment longer
#eval pAge.readI ⟨0, []⟩ (.fld "account") == some ⟨0, [.field "account"]⟩

/-- info: true -/
#guard_msgs in -- `readOnWrite` at a symbolic index: one `kite`; `initElement` below it
#eval xsNew.readT ⟨0, []⟩ (.idx (.lit (.int 1))) ==
  some (.kite (.lit (.int 1)) (.var (.user "i")) (.lit (.int 7)) (.lit (.int 0)))

/-- info: true -/
#guard_msgs in -- `memoryArrayFreshAlloc`: the length allocated
#eval xsNew.lenT ⟨0, []⟩ == some (.lit (.int 3))

/-- info: true -/
#guard_msgs in -- `readFromCopyToStorage`: a member of a copy reads the storage copied
#eval aCopy.readT ⟨0, []⟩ (.fld "age") == some (.find .init ((LPath.root "alice").field "age"))

/-- info: true -/
#guard_msgs in -- `newFromAdd`: another root is apart, `q.age` reads its default
#eval aCopy.readT ⟨1, []⟩ (.fld "age") == some (.lit (.int 0))

/-- info: true -/
#guard_msgs in -- `readFromCopyToStorageIdentity`: a reference member of a copy is there
-- where the storage holds no word at it
#eval aCopy.nameG ⟨0, [.field "account"]⟩ ==
  some (refT .init ((LPath.root "alice").field "account"))

/-- info: true -/
#guard_msgs in -- the write guard (Lean only): an index below the length
#eval xsNew.writeG ⟨0, []⟩ (.idx (.var (.user "j"))) ==
  some (ltG (.var (.user "j")) (.lit (.int 3)))

/-- info: [true, false] -/
#guard_msgs in -- `refDesc` (Lean only): a reference written names an older root
#eval [(LMem.write aCopy ⟨1, []⟩ (.fld "account") (.ref ⟨0, [.field "account"]⟩)).refDesc,
  (LMem.write aCopy ⟨0, []⟩ (.fld "account") (.ref ⟨1, [.field "account"]⟩)).refDesc]

/-- info: true -/
#guard_msgs in -- `findOnCopy`, `selectOnCopyMemPrim`: a read below a view reads memory
#eval (LStor.view pAge ⟨0, []⟩).readU ((LPath.root viewRoot).field "age") == .lit (.int 5)

/-- info: true -/
#guard_msgs in -- `selectOnCopyMemRef`, `readRCons`: a path below a view walks the names
#eval (LStor.view aCopy ⟨1, []⟩).readU (((LPath.root viewRoot).field "account").field "balance")
  == .lit (.int 0)

/-- info: true -/
#guard_msgs in -- a view holds no mapping (Lean only)
#eval (LStor.view pNew ⟨0, []⟩).mapU .map ((LPath.root viewRoot).field "age") == .err

/-- info: true -/
#guard_msgs in -- constants are folded where a term is built, and a big power is not
#eval LTerm.mkBin .add .uint (.lit (.int 2)) (.lit (.int 3)) == .lit (.int 5) &&
  LTerm.mkBin .pow .uint (.lit (.int 2)) (.lit (.int 1000)) matches .binop ..

/-- info: true -/
#guard_msgs in -- a word written over a word keeps whether a copy succeeds (Lean only)
#eval (LStor.save .init ((LPath.root "alice").field "age") (.lit (.int 30))).cpokU (.root "alice")
  == .ite (isT (LStor.init.readU ((LPath.root "alice").field "age"))) (.cpok .init (.root "alice"))
    (.cpok (.save .init ((LPath.root "alice").field "age") (.lit (.int 30))) (.root "alice"))

/-- info: [true, false] -/
#guard_msgs in -- `Facts.cpokInit` (Lean only): `wt` types the path, and no mapping is below it
#eval [({ lay := [("xs", .ref (.array .uint))] } : Facts).cpokInit (.root "xs"),
  ({ lay := [("m", .ref (.mapping .uint .uint))] } : Facts).cpokInit (.root "m")]

/-- info: [true, true, true] -/
#guard_msgs in -- the run guard (Lean only): an allocation at its ordinal, of a type with no
-- mapping and a well-formed default
#eval [pAge.okU.isSome, (LMem.addM .init 0 (.struct "Wallet")).okU.isNone,
  (LMem.addM .init 1 (.struct "Person")).okU.isNone]

/-- info: [true, true] -/
#guard_msgs in -- a view's guard where every reference names an older root, kept whole elsewhere
#eval [(LStor.view pAge ⟨0, []⟩).okE matches .seq _ (.seq _ _),
  (LStor.view (LMem.write aCopy ⟨0, []⟩ (.fld "account") (.ref ⟨1, [.field "account"]⟩))
    ⟨0, []⟩).okE matches .sok _]

/-- info: [true, true] -/
#guard_msgs in -- `initSize`, `sizeOfFixed`, `sizeOfDyn`: a fresh member's length is its
-- declared one, `uint[3]`'s `3` and `uint[]`'s `0`
#eval [(LMem.addM .init 0 (.struct "FixedTriple")).lenT ⟨0, [.field "items"]⟩ ==
    some (.lit (.int 3)),
  (LMem.addM .init 0 (.struct "Basket")).lenT ⟨0, [.field "items"]⟩ == some (.lit (.int 0))]

/-- info: true -/
#guard_msgs in -- `initElement`: an element of a fresh `uint[3]` is `0` below the length
#eval (LMem.addM .init 0 (.struct "FixedTriple")).readT ⟨0, [.field "items"]⟩
    (.idx (.var (.user "i"))) ==
  some (seqL (ltR (.var (.user "i")) (.lit (.int 3))) (.lit (.int 0)))

/-- info: true -/
#guard_msgs in -- `defaultValueBool`: a fresh `bool` member is `false`
#eval (LMem.addM .init 0 (.struct "Toggle")).readT ⟨0, []⟩ (.fld "on") ==
  some (.lit (.bool false))

/-- info: true -/
#guard_msgs in -- `findDefinitionSize`: a copied array's length is the storage's
#eval (LMem.copySt .init 0 .init (.root "bk")).lenT ⟨0, [.field "items"]⟩ ==
  some (.len .init ((LPath.root "bk").field "items"))

/-- info: [true, true] -/
#guard_msgs in -- `structG` (Lean only): a fresh struct member is a struct; below a copy, the
-- storage holds a struct there, no array and no word
#eval [aCopy.structG ⟨1, [.field "account"]⟩ == some (.lit (.bool true)),
  aCopy.structG ⟨0, [.field "account"]⟩ ==
    some (.ite (isT (.len .init ((LPath.root "alice").field "account"))) .err
      (refT .init ((LPath.root "alice").field "account")))]

/-- info: true -/
#guard_msgs in -- `selectOnCopyMemPrim` at a length: a view's length is memory's
#eval (LStor.view xsNew ⟨0, []⟩).lenU (LPath.root viewRoot) == .lit (.int 3)

/-- info: [true, true] -/
#guard_msgs in -- `hasU` of a view (Lean only): its root is there (`isViewRoot`), and a member
-- below it as the view guard and `nameG` say
#eval [(LStor.view pAge ⟨0, []⟩).hasU (LPath.root viewRoot) == .lit (.bool true),
  (LStor.view pAge ⟨0, []⟩).hasU ((LPath.root viewRoot).field "account") ==
    .orElse (.seq .err (.lit (.bool true))) (.seq (.lit (.bool true)) (.lit (.bool true)))]

/-- info: [true, false] -/
#guard_msgs in -- `memSize` (Lean only): 400 writes and allocations are within, 401 are not
#eval let w (n : Nat) : LMem :=
    (List.range n).foldl (fun m _ => .write m ⟨0, []⟩ (.fld "age") (.word (.lit (.int 1)))) pNew
  [(w 399).within memSize, (w 400).within memSize]

/-- info: [true, false] -/
#guard_msgs in -- `memL` (Lean only): a copy of memory needs guards that are literals
#eval [(memL (some (pNew, .lit (.bool true))) (some (⟨0, []⟩, .lit (.bool true)))).isSome,
  (memL (some (pNew, .seq .err (.lit (.bool true)))) (some (⟨0, []⟩, .lit (.bool true)))).isSome]

end MemoryClauses

/-! ## Memory through the closer

The updates of a memory program, pushed in, are one `LMem`
(`Calculus/Decide.lean`): an allocation's pair is one update (`pairL`), a
member deleted gets a fresh root (`freshRef`), and no default value is ever
built, so a long `new` costs what a short one does. -/

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

/-- `Person memory carol = alice;` copies the storage in (`memoryStorageCopy`,
one pair under `copyG`); a later write to `alice` is not seen
(`readFromCopyToStorage` reads the storage of the copy). -/
theorem memoryStorageCopyRead :
    ⊨ dl!{ [ alice.age = 27; Person memory carol = alice; alice.age = 30;
             uint x = carol.age; ] x == 27 } := by
  sol_symex
  sol_decide

/-- `alice = carol;` copies memory out (`memoryToStorageStoreRoot`, the
view of `carol` laid over `alice`); the storage reads through the view
(`findOnCopy`, `selectOnCopyMemPrim`), so a later write to `carol` is not
seen. -/
theorem memoryToStorageRead :
    ⊨ dl!{ [ Person memory carol; carol.age = 42; alice = carol; carol.age = 43;
             uint x = alice.age; ] x == 42 } := by
  sol_symex
  sol_decide

/-- info: false -/
#guard_msgs in -- a copy from storage outside its pair is outside the fragment
#eval (dl!{ { memory := copySt(memory, find(storage, alice)) } true }).inL Decide.Sym.empty

/-- info: false -/
#guard_msgs in -- a memory local no update bound is outside the fragment
#eval (dl!{ { x := read(memory, carol.age) } x == 0 }).inL Decide.Sym.empty

/--
error: sol_decide: the formula is outside the fragment (a modality, a push of a memory object, a copy of memory whose guards are not literals, a copy from storage outside its allocation's pair, a memory past memSize, a read of the ledger, an alias no update binds, or one through an index used after a write)
⊢ Fml.inL Decide.Sym.empty dl{ [ uint x = 1; ] x = 1 } = true
-/
#guard_msgs in -- a modality is outside the fragment, and `sol_decide` says what is
example : ⊨ dl!{ [ uint x = 1; ] x == 1 } := by
  sol_decide

end Solidity.Examples.Tactics.Decide
