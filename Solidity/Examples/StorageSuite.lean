import Solidity.Calculus.Close

/-!
# solkey's `taclets` suite, on storage

The storage programs of `keyext.solidity.examples/taclets` (each docstring
names its `.key` file), as theorems of the calculus: `⊨ dl!{ … }` by
`sol_symex` and `sol_close`.  The statement forms themselves, with the
derivations for them, are `StorageSteps.lean`; this file is the suite's
programs, deduplicated: one example per program the forms there do not already
state, and one per operator family where solkey has a file per operator.

A `.key` file states its claim in the contract's initial store, where every
array is empty; a claim that is only about that store is a run of the
interpreter from `State.exampleStore` (`Prog.localAfter`), checked by `rfl`, or
printed by `#eval` where `rfl` cannot unfold a struct's default (`defaultForTy`
is well-founded).  A length premise (`1 < values.length`) is dropped instead:
under the box a write out of bounds reverts, which satisfies the formula, so
`values[1] = 42; … result == 42` holds in every state.
-/

namespace Solidity.Examples.StorageSuite

open Proves Semantics

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · Roots and fields -/

/-- `age = 34; uint result = age;` — a root is written with `store`
(`storage-root-read-write.key`). -/
theorem rootWriteRead : ⊨ dl!{ [ age = 34; uint result = age; ] result == 34 } := by
  sol_symex
  sol_close

/-- `age = 1; age = 2; uint result = age;` — the last write wins
(`storage-root-multiple-writes.key`). -/
theorem rootMultipleWrites :
    ⊨ dl!{ [ age = 1; age = 2; uint result = age; ] result == 2 } := by
  sol_symex
  sol_close

/-- `alice.age = 17; total = alice.age; uint result = total;` — a root written
from a field read: the source is captured first (`storage-field-global-age.key`). -/
theorem rootFromField :
    ⊨ dl!{ [ alice.age = 17; total = alice.age; uint result = total; ] result == 17 } := by
  sol_symex
  sol_close

/-- `age = 34; balance = age; uint result = balance;` — a root from a root
(`storage-root-copy-source.key`). -/
theorem rootFromRoot :
    ⊨ dl!{ [ age = 34; balance = age; uint result = balance; ] result == 34 } := by
  sol_symex
  sol_close

/-- `alice.age = 1; bob.age = 2;` — two roots do not interfere
(`storage-field-disjoint-roots.key`). -/
theorem disjointRoots :
    ⊨ dl!{ [ alice.age = 1; bob.age = 2; ] alice.age == 1 && bob.age == 2 } := by
  sol_symex
  sol_close

/-- `alice.account.balance = 1; alice.account.token.value = 2;` — nor do two
members of one struct (`storage-field-disjoint-fields.key`). -/
theorem disjointFields :
    ⊨ dl!{ [ alice.account.balance = 1; alice.account.token.value = 2; ]
           alice.account.balance == 1 && alice.account.token.value == 2 } := by
  sol_symex
  sol_close

/-- `bob.age = 7; alice = bob; uint result = alice.age;` — a root copy is deep
(`storage-root-copy-struct.key`) … -/
theorem rootCopyStruct :
    ⊨ dl!{ [ bob.age = 7; alice = bob; uint result = alice.age; ] result == 7 } := by
  sol_symex
  sol_close

/-- … and by value: writing the source afterwards leaves the copy as it was. -/
theorem rootCopyByValue :
    ⊨ dl!{ [ bob.age = 7; alice = bob; bob.age = 9; uint result = alice.age; ]
           result == 7 } := by
  sol_symex
  sol_close

/-- `bob.account.balance = 11; Account storage acc = bob.account;
alice.account = acc; uint result = alice.account.balance;` — a member copied
from an alias (`storage-field-copy-struct.key`). -/
theorem fieldCopyStruct :
    ⊨ dl!{ [ bob.account.balance = 11; Account storage acc = bob.account;
             alice.account = acc; uint result = alice.account.balance; ] result == 11 } := by
  sol_symex
  sol_close

/-! ## 2 · Aliases -/

/-- `Person storage p = alice; bob.age = 20; p = bob; uint result = p.age;` — a
root rebind (`storageLocalRootRebind`), read through
(`storage-alias-rebind-alias.key`). -/
theorem aliasRebind :
    ⊨ dl!{ [ Person storage p = alice; bob.age = 20; p = bob; uint result = p.age; ]
           result == 20 } := by
  sol_symex
  sol_close

/-- `uint before = alice.age; Person storage p = alice; bob.age = 20; p = bob;
uint result = alice.age;` — rebinding leaves the original untouched
(`storage-alias-rebind-original.key`). -/
theorem aliasRebindOriginal :
    ⊨ dl!{ [ uint before = alice.age; Person storage p = alice; bob.age = 20; p = bob;
             uint result = alice.age; ] result == before } := by
  sol_symex
  sol_close

/-- `Person storage p = alice; Account storage acc = p.account; acc.balance = 100;
p.account.token.value = 3;` — writes through two aliases, read through the root
(`storage-alias-write-balance.key`, `storage-alias-write-token.key`). -/
theorem aliasWrites :
    ⊨ dl!{ [ Person storage p = alice; Account storage acc = p.account; acc.balance = 100;
             p.account.token.value = 3;
             uint b = alice.account.balance; uint v = alice.account.token.value; ]
           b == 100 && v == 3 } := by
  sol_symex
  sol_close

/-- `Account storage acc = alice.account; bob.account.balance = 42;
acc = bob.account; uint result = acc.balance;` (`storage-field-read-bind-local.key`). -/
theorem aliasBindMember :
    ⊨ dl!{ [ Account storage acc = alice.account; bob.account.balance = 42;
             acc = bob.account; uint result = acc.balance; ] result == 42 } := by
  sol_symex
  sol_close

/-- `Person storage p; age = 7;` — an alias declared without a target binds
nothing (`storageLocalDeclSkip`, `storage-local-decl-skip.key`). -/
theorem localDeclSkip :
    ⊨ dl!{ [ Person storage p; age = 7; uint result = age; ] result == 7 } := by
  sol_symex
  sol_close

/-! ## 3 · Arrays and mappings -/

/-- `values[3] = 5; values[3] = 8; uint result = values[3];`
(`storage-index-multiple-writes.key`). -/
theorem arrayMultipleWrites :
    ⊨ dl!{ [ values[3] = 5; values[3] = 8; uint result = values[3]; ] result == 8 } := by
  sol_symex
  sol_close

/-- `matrix[2][3] = 99; uint result = matrix[2][3];`
(`storage-matrix-write-read.key`, `storage-index-decomposition.key`). -/
theorem matrixWriteRead :
    ⊨ dl!{ [ matrix[2][3] = 99; uint result = matrix[2][3]; ] result == 99 } := by
  sol_symex
  sol_close

/-- `values[1] = 7;` from the initial store, where `values` is empty: out of
bounds, the write reverts (`storage-index-array-out-of-bounds-box.key`). -/
theorem arrayOutOfBounds :
    Prog.run State.exampleStore (sol{ values[1] = 7; } : Prog StandardExample) = .error .revert :=
  rfl

/-- `balances[1] = 42; uint result = balances[1];` (`storage-index-root-mapping.key`). -/
theorem mappingWriteRead :
    ⊨ dl!{ [ balances[1] = 42; uint result = balances[1]; ] result == 42 } := by
  sol_symex
  sol_close

/-! ## 4 · Push and pop -/

/-- `matrix.push(); matrix[0].push(100); matrix[0][0] = 7;` — a pushed row
extended and written (`storage-index-decompose-after-push.key`). -/
theorem decomposeAfterPush :
    ⊨ dl!{ [ matrix.push(); matrix[0].push(100); matrix[0][0] = 7;
             uint result = matrix[0][0]; ] result == 7 } := by
  sol_symex
  sol_close

/-! `values.push(); values.push(); values.push(); uint result = values[2];` — a
bare push leaves the default (`storage-push-empty.key`). -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0))
-/
#guard_msgs in
#eval Prog.localAfter State.exampleStore
  sol{ values.push(); values.push(); values.push(); uint result = values[2]; } "result"

/-- `values.push(); values.push(); values.push(42); uint result = values[2];`
(`storage-push-value.key`). -/
theorem pushValue :
    Prog.localAfter State.exampleStore
      sol{ values.push(); values.push(); values.push(42); uint result = values[2]; } "result" =
      .ok (.val (.int 42)) := rfl

/-- `uint x = 40; uint y = 2; values.push(x + y); uint result = values[0];` — the
argument is captured first (`storage-push-nonsimple-arg.key`). -/
theorem pushNonsimpleArg :
    Prog.localAfter State.exampleStore
      sol{ uint x = 40; uint y = 2; values.push(x + y); uint result = values[0]; } "result" =
      .ok (.val (.int 42)) := rfl

/-! `values.push(); values.push(); values.pop(); uint result = values[0];`
(`storage-pop-nonempty.key`). -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0))
-/
#guard_msgs in
#eval Prog.localAfter State.exampleStore
  sol{ values.push(); values.push(); values.pop(); uint result = values[0]; } "result"

/-- `values.push(); values.push(); values.pop(); uint result = values[1];` — the
popped slot is gone: reading it reverts. -/
theorem popNonemptyGone :
    Prog.run State.exampleStore
      (sol{ values.push(); values.push(); values.pop(); uint result = values[1]; } :
        Prog StandardExample) = .error .revert := rfl

/-- `values.pop();` on the empty array reverts (`storage-pop-empty-box.key`). -/
theorem popEmpty :
    Prog.run State.exampleStore (sol{ values.pop(); } : Prog StandardExample) = .error .revert :=
  rfl

/-- `values.push(); values.pop(); uint result = values[0];` reverts
(`storage-pop-after-push.key`). -/
theorem popAfterPushRead :
    Prog.run State.exampleStore
      (sol{ values.push(); values.pop(); uint result = values[0]; } : Prog StandardExample) =
      .error .revert := rfl

/-! `tokens.push(); tokens[0].value = 7; tokens.pop(); Token storage t = tokens.push();
uint r = t.value;` — the push-after-pop example (`sec:push-pop-example`):
the slot `pop()` cleared is not restored by the next `push()`, so the value
written before the pop is not seen through the returned reference, and the
program reaches the read without reverting.  Run on `testSuiteStore`, the store
that has `tokens`; a `Token` default is not unfolded by `rfl`, so it is printed. -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0))
-/
#guard_msgs in
#eval Prog.localAfter State.testSuiteStore
  sol[TestSuite]{ tokens.push(); tokens[0].value = 7; tokens.pop();
                  Token storage t = tokens.push(); uint r = t.value; } "r"

/-! `persons.push(); persons.push(); Person storage p; p = persons.push();
p.age = 5; uint result = persons[2].age;` (`storage-push-local-bind.key`).  Pushing
a `Person` builds its default, which `rfl` cannot unfold, so the run is printed. -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 5))
-/
#guard_msgs in
#eval Prog.localAfter State.exampleStore
  sol{ persons.push(); persons.push(); Person storage p; p = persons.push(); p.age = 5;
       uint result = persons[2].age; } "result"

/-! `values.push(5); values.push(6); uint[][] storage m = matrix; m.push();
m[0] = values; uint result = matrix[0][1];` — an array copied into a pushed row
(`storage-index-copysource-after-push.key`). -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 6))
-/
#guard_msgs in
#eval Prog.localAfter State.exampleStore
  sol{ values.push(5); values.push(6); uint[][] storage m = matrix; m.push(); m[0] = values;
       uint result = matrix[0][1]; } "result"

/-! A popped slot keeps its mappings (`TestSuite.testDeepPopDoesNotResetMappingMember`):
`pop()` deletes the removed element, `delete` never clears a mapping, so the slot
the next `push()` recycles still holds the entry — while its value members are
reset. -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 10))
-/
#guard_msgs in
#eval Prog.localAfter State.testSuiteStore
  sol[TestSuite]{ ledgerUses.push(); Ledger storage l = ledgerUses[0].ledger; l.balances[1] = 10;
                  ledgerUses.pop(); ledgerUses.push(); Ledger storage l2 = ledgerUses[0].ledger;
                  uint result = l2.balances[1]; } "result"

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0))
-/
#guard_msgs in
#eval Prog.localAfter State.testSuiteStore
  sol[TestSuite]{ ledgerUses.push(); Ledger storage l = ledgerUses[0].ledger; l.nonce = 7;
                  ledgerUses.pop(); ledgerUses.push(); Ledger storage l2 = ledgerUses[0].ledger;
                  uint result = l2.nonce; } "result"

/-! ## 5 · Compound assignment and `++` -/

/-- `alice.age = 30; alice.age -= 5;` (`storage-field-sub-assign.key`). -/
theorem fieldOpAssign :
    ⊨ dl!{ [ alice.age = 30; alice.age -= 5; uint result = alice.age; ] result == 25 } := by
  sol_symex
  sol_close

/-- `age = 6; age *= 3;` (`storage-root-mul-assign.key`). -/
theorem rootMulAssign : ⊨ dl!{ [ age = 6; age *= 3; uint result = age; ] result == 18 } := by
  sol_symex
  sol_close

/-- `age = 10; age /= 0;` — a zero divisor reverts, so nothing after it holds or
fails: the box proves `false`. -/
theorem divByZero : ⊨ dl!{ [ age = 10; age /= 0; ] false } := by
  sol_symex
  sol_close

/-- `alice.age = 30; ++alice.age;` (`storageFieldIncrement`,
`storage-field-preincrement.key`). -/
theorem fieldIncrement :
    ⊨ dl!{ [ alice.age = 30; ++alice.age; uint result = alice.age; ] result == 31 } := by
  sol_symex
  sol_close

/-- `alice.account.balance = 30; alice.account.balance += 4;` — through the
alias Step 2 binds (`storage-field-deep-add-assign.key`). -/
theorem deepOpAssignRead :
    ⊨ dl!{ [ alice.account.balance = 30; alice.account.balance += 4;
             uint result = alice.account.balance; ] result == 34 } := by
  sol_symex
  sol_close

/-- `alice.account.balance = 100; ++alice.account.balance;`
(`storage-deep-field-preincrement.key`). -/
theorem deepIncrementRead :
    ⊨ dl!{ [ alice.account.balance = 100; ++alice.account.balance;
             uint result = alice.account.balance; ] result == 101 } := by
  sol_symex
  sol_close

/-! ## 6 · Branches and guards -/

/-- `age = 10; if (age < 20) { result = 1; } else { result = 2; }` -/
theorem ifOnStorage :
    ⊨ dl!{ [ age = 10; if (age < 20) { result = 1; } else { result = 2; }; ] result == 1 } := by
  sol_symex
  sol_close

/-- `age = 10; assert(age == 10); result = 1;` — a holding `assert` goes on. -/
theorem assertHolds : ⊨ dl!{ [ age = 10; assert(age == 10); result = 1; ] result == 1 } := by
  sol_symex
  sol_close

/-- `assert(false); result = 1;` — a failing `assert` reverts: the box holds of
anything … -/
theorem assertFails : ⊨ dl!{ [ assert(false); result = 1; ] false } := by
  sol_symex
  sol_close

/-- … and the diamond of nothing. -/
theorem assertFailsDiamond : ¬ (⊨ dl!{ ⟨ assert(false); result = 1; ⟩ result == 1 }) :=
  fun h => h State.exampleStore

/-- `age = 10; require(age == 10); result = 1;` -/
theorem requireHolds : ⊨ dl!{ [ age = 10; require(age == 10); result = 1; ] result == 1 } := by
  sol_symex
  sol_close

/-- `require(false); result = 1;` — the box `c → φ` … -/
theorem requireFails : ⊨ dl!{ [ require(false); result = 1; ] false } := by
  sol_symex
  sol_close

/-- … the diamond `c ∧ φ` (solkey `docs/require-assert.md`). -/
theorem requireFailsDiamond : ¬ (⊨ dl!{ ⟨ require(false); result = 1; ⟩ result == 1 }) :=
  fun h => h State.exampleStore

/-! ## 7 · Fixed-size arrays

`TestSuite`'s `uint[3] fixedValues;`, `Token[2] fixedTokens;`,
`FixedTriple triple;` (`struct Triple { uint[3] items; uint tag; }`, renamed)
and `uint[3][] rows;`.  A fixed-size array is indexed by the array rules
(`storageIndexReadArrayFind`, `storageIndexWriteArraySave`: solkey's
`Path[…,array]` takes either kind) and bounds-checked against its length; it
has no `push` or `pop`, and its `.length` is its type's, the literal the
elaborator writes. -/

section Fixed

local instance : InContract := ⟨TestSuite⟩

/-- `fixedValues[2] = 1; uint result = fixedValues[2];`
(`TestSuite.testFixedArrayIndexInBounds`). -/
theorem fixedWriteRead :
    ⊨ dl!{ [ fixedValues[2] = 1; uint result = fixedValues[2]; ] result == 1 } := by
  sol_symex
  sol_close

/-- `triple.items[1] = 7; uint result = triple.items[1];` — an element of a
fixed-size member. -/
theorem fixedMemberWriteRead :
    ⊨ dl!{ [ triple.items[1] = 7; uint result = triple.items[1]; ] result == 7 } := by
  sol_symex
  sol_close

/-- The lengths are the declared ones, in every state
(`testFixedArrayLength`, `testStructFixedMemberLength`,
`testFixedStructArrayLength`). -/
theorem fixedLengths :
    ⊨ dl!{ [ uint n = fixedValues.length; uint m = triple.items.length;
             uint t = fixedTokens.length; ] (n == 3 && m == 3 && t == 2) } := by
  sol_symex
  sol_close

/-- `rows[0].length` with `rows : uint[3][]`: `rows[0]` is evaluated (bound to
a fresh alias, so an index past `rows`'s end reverts), and the length is `3`
(`testFixedElementOfDynamicArrayLength`). -/
theorem fixedElementLength : ⊨ dl!{ [ uint k = rows[0].length; ] k == 3 } := by
  sol_symex
  sol_close

/-! From the initial store: an index past the declared length reverts, and
`rows[0].length` reverts while `rows` is empty. -/

/-- info: (Except.error (Solidity.Semantics.Halt.revert), Except.error (Solidity.Semantics.Halt.revert)) -/
#guard_msgs in
#eval (Prog.run State.testSuiteStore (sol{ uint k = 3; fixedValues[k] = 1; }),
  Prog.run State.testSuiteStore (sol{ uint k = rows[0].length; }))

/-- A literal index past the end, and a `push` onto a fixed-size array, are
solc's compile errors, and the elaborator's. -/
example : True := by
  fail_if_success have : Prog TestSuite := sol{ fixedValues[3] = 1; }
  fail_if_success have : Prog TestSuite := sol{ fixedValues.push(1); }
  trivial

end Fixed

end Solidity.Examples.StorageSuite
