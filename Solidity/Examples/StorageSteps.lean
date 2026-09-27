import Solidity.Calculus.Close

/-!
# Storage, one statement form at a time

Every storage statement form with a worked derivation, stated in the
calculus's own terms (mini-solkey's `Examples/StorageSteps.lean`).  Every example
is a theorem `⊨ dl!{ … }`, proved one of two ways:

* by the strategy: `sol_symex` fires the one rule each statement has, and
  `sol_close` applies the updates in an arbitrary state and reads back the
  writes;
* for a worked example, by a **walk**: `apply Proves.valid` turns
  the goal into the judgement `⊢ φ` (`Calculus/Logic.lean`), and the derivation
  is built one `apply` per taclet, so each rule the derivation names is named here —
  `unfold r` for Steps 1 and 2, `update r` for Step 3, `empty` for
  `emptyModality`, `intro` for a precondition.  Put the cursor after an `apply`
  to see the next line as a sequent `dl{ Γ ⟹ φ }`.  `apply close` leaves the
  calculus; the `sol_symex` after it runs nothing, it only normalises the goal
  for `sol_close`.  The headline is proved both ways.

Where the derivation is the claim — the order in which Step 2 captures, a
`push`, a memory target — and `sol_close` cannot read the result back, or reads
it back slowly, the postcondition is `true`: the walk still has to take every
rule the derivation draws.

The three steps: Step 1 unfolds a read whose receiver or index
is not simple, Step 2 decomposes a write (source, receiver, index, in that
order), Step 3 turns a statement whose parts are simple into an update.  The
rule names are solkey's (`Calculus/Rules.lean`).

Writes are under the box: `⊨` quantifies over every state, including those
without `alice`, where `alice.age = 1;` is stuck, so the diamond of a write is
not valid (`Close.lean`).  The programs of solkey's `taclets` suite, and the
claims that need the contract's initial store, are `StorageSuite.lean`.

A Step 1 rule whose read lands in a hole (`storageFieldRead_unfold_rightFst`,
`storageIndexRead_unfold_rightSndIndex`: the `lhs` of `lhs = nsp.fld`) is not
applied by name: its conclusion is `Hole.fill lhs …`, whose dependent match does
not reduce while unifying, so `apply unfold .storageFieldRead_unfold_rightFst`
cannot see the statement it matches.  The walk takes the strategy's rule for
that statement instead, `(Stmt.step _ _ _).taclet`, and a comment names it.
-/

namespace Solidity.Examples.StorageSteps

open Proves Semantics

local instance : InContract := ⟨StandardExample⟩

/-! ## 0 · The headline: `alice.account.balance = 10;` -/

/-- `alice.account.balance = 10;` — the receiver `alice.account` is not simple.
Step 2 captures the source into `se1`, then aliases the receiver as `sp1`, then
writes through the alias. -/
theorem deepFieldWrite :
    ⊨ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } := by
  apply Proves.valid
  apply unfold .storageFieldWrite_unfold_leftFst
  -- dl{ ⟹ [ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ] … }
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  -- Step 3: `sp1.balance = se1;` has only simple parts
  apply update .storageFieldWriteSave
  apply empty
  -- dl{ { se1 := 10 }, { sp1 := alice.account }, { storage := save(storage, sp1.balance, se1) } ⟹
  --     find(storage, alice.account.balance) = 10 }
  apply close
  sol_symex
  sol_close

/-- The same, with the strategy choosing the rules. -/
theorem deepFieldWrite_symex :
    ⊨ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } := by
  sol_symex
  sol_close

/-! ## 1 · Fields and roots -/

/-- `alice.age = 7;` — both sides simple: one Step 3 rule. -/
theorem fieldWriteSimple : ⊨ dl!{ [ alice.age = 7; ] alice.age == 7 } := by
  apply Proves.valid
  apply update .storageFieldWriteSave
  apply empty
  apply close
  sol_symex
  sol_close

/-- `uint v = alice.age;` — a read with a simple receiver: `find` at once. -/
theorem fieldRead : ⊨ dl!{ [ uint v = alice.age; ] v == alice.age } := by
  sol_symex
  sol_close

/-- `uint v = alice.account.balance;` — the read twin of the headline: Step 1
aliases the receiver, then `find` reads through the alias. -/
theorem deepFieldRead :
    ⊨ dl!{ [ uint v = alice.account.balance; ] v == alice.account.balance } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  -- Step 1, `storageFieldRead_unfold_rightFst` (see the module docstring)
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadFind
  apply empty
  apply close
  sol_symex
  sol_close

/-- `alice.account.token.value = 5;` — one selector deeper, and the same chain:
Step 2 hoists the whole prefix `alice.account.token` into one alias. -/
theorem deeperFieldWrite :
    ⊨ dl!{ [ alice.account.token.value = 5; ] alice.account.token.value == 5 } := by
  apply Proves.valid
  apply unfold .storageFieldWrite_unfold_leftFst
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .storageLocalDeclInitDrop
  -- the alias's own right-hand side `alice.account.token` is a read with a
  -- non-simple receiver: Step 1 (`storageFieldRead_unfold_rightFst`) unfolds it
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldWriteSave
  apply empty
  apply close
  sol_symex
  sol_close

/-- `Account storage acc = bob.account; alice.account = acc;` — the write stores
the value found at the alias (`storageFieldWriteCopySource`), a copy, so the
source is left as it was. -/
theorem fieldWriteFromAlias :
    ⊨ dl!{ [ uint b = bob.account.balance; Account storage acc = bob.account;
             alice.account = acc; ] bob.account.balance == b } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  -- Step 1, `storageFieldRead_unfold_rightFst` (see the module docstring)
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadFind
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldWriteCopySource
  apply empty
  apply close
  sol_symex
  sol_close

/-- `uint v = total;` — a root is read with `select`, not `find`. -/
theorem rootRead : ⊨ dl!{ [ uint v = total; ] v == total } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  apply update .storageRootReadSelect
  apply empty
  apply close
  sol_symex
  sol_close

/-- `alice = bob;` — a whole-struct write from another root is a deep copy
(`storageRootWriteCopySource`); the source keeps its value. -/
theorem rootWriteFromGlobal :
    ⊨ dl!{ [ uint b = bob.age; alice = bob; ] bob.age == b } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply update .storageRootWriteCopySource
  apply empty
  apply close
  sol_symex
  sol_close

/-- `Person storage p = bob; alice = p;` — the same copy from an alias. -/
theorem rootWriteFromAlias :
    ⊨ dl!{ [ uint b = bob.age; Person storage p = bob; alice = p; ] bob.age == b } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply unfold .storageLocalDeclInitDrop
  apply update .storageLocalRootRebind
  apply update .storageRootWriteCopySource
  apply empty
  apply close
  sol_symex
  sol_close

/-- `tok = bob.account.token;` (`TestSuite`) — a root copied from a member
(`storageFieldReadStoreRoot`), after Step 1 has aliased `bob.account`: the
same syntactic form as an alias rebind, and a deep copy because `tok` is a
state variable. -/
theorem globalRootCopy :
    ⊨ dl[TestSuite]{ [ uint b = bob.age; tok = bob.account.token; ] bob.age == b } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  -- Step 1, `storageFieldRead_unfold_rightFst`
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadStoreRoot
  apply empty
  apply close
  sol_symex
  sol_close

/-! ## 2 · Aliases -/

/-- `uint old = alice.account.balance; Account storage acc = alice.account;
acc = bob.account; acc.balance = 10;` — the alias is rebound
(`storageFieldReadBindLocalRoot`), not copied into, so the write lands in
`bob` and `alice` keeps its balance. -/
theorem localRebindThenWrite :
    ⊨ dl!{ [ uint old = alice.account.balance; Account storage acc = alice.account;
             acc = bob.account; acc.balance = 10; ]
           bob.account.balance == 10 && alice.account.balance == old } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  -- Step 1, `storageFieldRead_unfold_rightFst` (see the module docstring)
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadFind
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldWriteSave
  apply empty
  apply close
  sol_symex
  sol_close

/-! ## 3 · Arrays and mappings

An array access has no bounds branch in the calculus: `storageIndexReadArrayFind`
is one update, and an index out of bounds halts in the interpreter.  Under the
box that run satisfies the formula; under the diamond it does not
(`arrayIndexReadDiamond`). -/

/-- `uint v = values[i];` -/
theorem arrayIndexRead : ⊨ dl!{ [ uint v = values[i]; ] v == values[i] } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  apply update .storageIndexReadArrayFind
  apply empty
  apply close
  sol_symex
  sol_close

/-- `uint v = values[i];` under the diamond is not valid: in `StandardExample`'s
initial store `values` is empty (and `i` unbound), so the read halts. -/
theorem arrayIndexReadDiamond : ¬ (⊨ dl!{ ⟨ uint v = values[i]; ⟩ true }) :=
  fun h => h State.exampleStore

/-- `values[i] = 100;` -/
theorem arrayIndexWrite : ⊨ dl!{ [ values[i] = 100; ] values[i] == 100 } := by
  apply Proves.valid
  apply update .storageIndexWriteArraySave
  apply empty
  apply close
  sol_symex
  sol_close

/-- `uint v = balances[i];` — a mapping key needs no bounds. -/
theorem mappingIndexRead : ⊨ dl!{ [ uint v = balances[i]; ] v == balances[i] } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  apply update .storageIndexReadMappingFind
  apply empty
  apply close
  sol_symex
  sol_close

/-- `Person storage p = bob; people[i] = p;` — a struct entry written from an
alias copies what the alias finds (`storageIndexWriteArrayCopySource`). -/
theorem arrayIndexWriteRefSource :
    ⊨ dl!{ [ uint b = bob.age; Person storage p = bob; people[i] = p; ] bob.age == b } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply unfold .storageLocalDeclInitDrop
  apply update .storageLocalRootRebind
  apply update .storageIndexWriteArrayCopySource
  apply empty
  apply close
  sol_symex
  sol_close

/-- `Person storage p = people[i]; p.age = 3;` — an alias bound to an entry
(`storageIndexReadArrayBindLocalRoot`): the write through it lands in
`people[i]`. -/
theorem aliasFromIndex :
    ⊨ dl!{ [ Person storage p = people[i]; p.age = 3; ] people[i].age == 3 } := by
  sol_symex
  sol_close

/-- `matrix[i][j] = 100;` — a non-simple receiver under an index: the source is
captured, then the receiver `matrix[i]` aliased
(`storageIndexReadArrayBindLocalRoot`), then the index.  The order is the claim;
reading the entry back is `nonSimpleIndexWrite`'s. -/
theorem nonsimplePathIndexWrite :
    ⊨ dl!{ [ matrix[i][j] = 100; ] true } := by
  apply Proves.valid
  apply unfold .storageIndexWriteCaptureAllComplexRecv
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .storageLocalDeclInitDrop
  apply update .storageIndexReadArrayBindLocalRoot
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply update .storageIndexWriteArraySave
  apply empty
  apply close
  sol_symex
  sol_close

/-- `values[i + 1] = 5;` — a non-simple index: source first, then the
receiver (bound again, as solkey does), then the index
(`storageIndexWriteCaptureAllNonSimpleIndex`), so the value written is the one
the source had before the index was computed. -/
theorem nonSimpleIndexWrite : ⊨ dl!{ [ values[i + 1] = 5; ] values[i + 1] == 5 } := by
  apply Proves.valid
  apply unfold .storageIndexWriteCaptureAllNonSimpleIndex
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .storageLocalDeclInitDrop
  apply update .storageLocalRootRebind
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply update .storageIndexWriteArraySave
  apply empty
  apply close
  sol_symex
  sol_close

/-- `matrix[i + 1][j + 1] = 77;` — both the receiver and the index are not
simple.  The order is source, receiver, index: the receiver's own index is
captured while the alias is bound (`storageIndexRead_unfold_rightSndIndex`),
before the write's index. -/
theorem receiverAndIndexCaptured :
    ⊨ dl!{ [ matrix[i + 1][j + 1] = 77; ] true } := by
  apply Proves.valid
  apply unfold .storageIndexWriteCaptureAllComplexRecv
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .storageLocalDeclInitDrop
  -- Step 1, `storageIndexRead_unfold_rightSndIndex`
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply update .storageIndexReadArrayBindLocalRoot
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply update .storageIndexWriteArraySave
  apply empty
  apply close
  sol_symex
  sol_close

/-- `bucket.tokens[i] = tok;` (`TestSuite`) — a struct entry under a non-simple
receiver, written from a root: no source to freeze, the receiver is aliased
(`storageIndexWriteStorageRef_unfold_leftFst`). -/
theorem refIndexWriteNonsimpleReceiver : ⊨ dl[TestSuite]{ [ bucket.tokens[i] = tok; ] true } := by
  apply Proves.valid
  apply unfold .storageIndexWriteStorageRefCaptureAllComplexRecv
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply update .storageIndexWriteArrayCopySource
  apply empty
  apply close
  sol_symex
  sol_close

/-! ## 4 · Push and pop

`push` writes the new element and the length in one update; `pop` deletes the
last element and shortens.  What they write is not read back by `sol_close`
(`Close.lean`), so the walks end in `true`: they are the rule, and the runs
from the initial store in `StorageSuite.lean` are the values. -/

/-- `values.push(42);` -/
theorem arrayPush : ⊨ dl!{ [ values.push(42); ] true } := by
  apply Proves.valid
  apply update .storagePushValueSave
  apply empty
  apply close
  sol_symex
  sol_close

/-- `people.pop();` -/
theorem arrayPop : ⊨ dl!{ [ people.pop(); ] true } := by
  apply Proves.valid
  apply update .storagePopSave
  apply empty
  apply close
  sol_symex
  sol_close

/-- `people.pop();` under the diamond is not valid: `people` starts empty, and
a `pop` of an empty array reverts. -/
theorem arrayPopDiamond : ¬ (⊨ dl!{ ⟨ people.pop(); ⟩ true }) :=
  fun h => h State.exampleStore

/-- `Person storage p = bob; people.push(p);` — the pushed element is a copy of
what the alias finds (`storagePushValueCopySource`). -/
theorem pushRefSource : ⊨ dl!{ [ Person storage p = bob; people.push(p); ] true } := by
  apply Proves.valid
  apply unfold .storageLocalDeclInitDrop
  apply update .storageLocalRootRebind
  apply update .storagePushValueCopySource
  apply empty
  apply close
  sol_symex
  sol_close

/-- `Token storage t = tok; bucket.tokens.push(t);` (`TestSuite`) — a
non-simple receiver is aliased first. -/
theorem pushNonsimpleReceiver :
    ⊨ dl[TestSuite]{ [ Token storage t = tok; bucket.tokens.push(t); ] true } := by
  apply Proves.valid
  apply unfold .storageLocalDeclInitDrop
  apply update .storageLocalRootRebind
  apply unfold .storagePushValue_unfold_leftFstReceiver
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storagePushValueCopySource
  apply empty
  apply close
  sol_symex
  sol_close

/-- `bucket.tokens.push();` (`TestSuite`) — the bare push on a non-simple
receiver. -/
theorem bucketPushBare : ⊨ dl[TestSuite]{ [ bucket.tokens.push(); ] true } := by
  apply Proves.valid
  apply unfold .storagePush_unfold_leftFstReceiver
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storagePushLengthSaveReferenceElement
  apply empty
  apply close
  sol_symex
  sol_close

/-- `people.push();` — a struct element: the slot is taken as it is
(`storagePushLengthSaveReferenceElement`), no `delAt`; the pop that recycled
it cleared it, and a mapping in it survives (solkey, solc). -/
theorem pushBare : ⊨ dl!{ [ people.push(); ] true } := by
  apply Proves.valid
  apply update .storagePushLengthSaveReferenceElement
  apply empty
  apply close
  sol_symex
  sol_close

/-- `Person storage p = people.push(); p.age = 11;` — the slot a bare push
returns is a path like any other (`storageLocalRootPushBind`), so it can be
written, and read, through an alias. -/
theorem pushSlotWrite :
    ⊨ dl!{ [ Person storage p = people.push(); p.age = 11; ] p.age == 11 } := by
  apply Proves.valid
  apply unfold .storageLocalDeclInitDrop
  apply update .storageLocalRootPushBind
  apply update .storageFieldWriteSave
  apply empty
  apply close
  sol_symex
  sol_close

/-- `values.push(); values.pop();` — the pop's guard is read under the push. -/
theorem popAfterPush : ⊨ dl!{ [ values.push(); values.pop(); ] true } := by
  apply Proves.valid
  apply update .storagePushLengthSave
  apply update .storagePopSave
  apply empty
  apply close
  sol_symex
  sol_close

/-! ## 5 · Compound assignment

`l op= e;` is one write-back of `l op e`, computed and range-checked at the
target's type (`storageFieldOpAssign` and its siblings), not a read–compute–write
desugaring.  One rule serves the five operators (`⊕` is its schema variable). -/

/-- `alice.age += 1;` -/
theorem fieldCompoundAssign :
    ⊨ dl!{ [ uint before = alice.age; alice.age += 1; uint after = alice.age; ]
           after == before + 1 } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply update .storageFieldOpAssign
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply empty
  apply close
  sol_symex
  sol_close

/-- `uint x = alice.age; uint y = x + 1; alice.age = y;` — the read–compute–write
block that `alice.age += 1;` is not desugared to writes the same value. -/
theorem compoundDesugared :
    ⊨ dl!{ [ uint x = alice.age; uint y = x + 1; alice.age = y; ] alice.age == x + 1 } := by
  sol_symex
  sol_close

/-- `age = 10; age += 5;` — a root (`storageRootOpAssign`, `storage-root-add-assign.key`). -/
theorem rootOpAssign : ⊨ dl!{ [ age = 10; age += 5; uint result = age; ] result == 15 } := by
  sol_symex
  sol_close

/-- `alice.account.balance += a;` — a non-simple receiver is aliased first
(`storageFieldOpAssignUnfoldLeftFst`); the source is simple, so nothing is
frozen.  The walk is the claim, so the postcondition is `true`. -/
theorem deepOpAssign : ⊨ dl!{ [ alice.account.balance += a; ] true } := by
  apply Proves.valid
  apply unfold .storageFieldOpAssignUnfoldLeftFst
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldOpAssign
  apply empty
  apply close
  sol_symex
  sol_close

/-- `values[1] = 40; values[1] /= 8;` (`storageIndexArrayOpAssign`,
`storage-index-div-assign.key`). -/
theorem indexOpAssign :
    ⊨ dl!{ [ values[1] = 40; values[1] /= 8; uint result = values[1]; ] result == 5 } := by
  sol_symex
  sol_close

/-! ## 6 · `++` and `--`

One rule per target serves all four operators (`⊕⊕`), so the increments below
stand for the decrements too: `--` has no `sol{ … }` spelling (it starts a
comment in Lean). -/

/-- `age = 10; age++;` — a root write, then the increment
(`storageRootIncrement`). -/
theorem rootWriteThenIncrement : ⊨ dl!{ [ age = 10; age++; ] age == 11 } := by
  apply Proves.valid
  apply update .storageRootWriteStore
  apply update .storageRootIncrement
  apply empty
  apply close
  sol_symex
  sol_close

/-- `alice.account.balance++;` — the receiver is aliased first
(`storageFieldIncrementUnfoldLeftFst`), then incremented through the alias. -/
theorem deepIncrement : ⊨ dl!{ [ alice.account.balance++; ] true } := by
  apply Proves.valid
  apply unfold .storageFieldIncrementUnfoldLeftFst
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldIncrement
  apply empty
  apply close
  sol_symex
  sol_close

/-- `values[1] = 40; ++values[1];` (`storageIndexIncrement`). -/
theorem indexIncrement :
    ⊨ dl!{ [ values[1] = 40; ++values[1]; uint result = values[1]; ] result == 41 } := by
  sol_symex
  sol_close

/-- `age = 10; result = age++;` — the postfix yields the old value
(`storageRootIncrementAssignment`). -/
theorem rootPostIncrementAssign :
    ⊨ dl!{ [ age = 10; result = age++; ] result == 10 && age == 11 } := by
  sol_symex
  sol_close

/-- `age = 10; result = ++age;` — the prefix yields the new one. -/
theorem rootPreIncrementAssign : ⊨ dl!{ [ age = 10; result = ++age; ] result == 11 } := by
  sol_symex
  sol_close

/-- `alice.age = 30; result = alice.age++;` (`storageFieldIncrementAssignment`). -/
theorem fieldPostIncrementAssign :
    ⊨ dl!{ [ alice.age = 30; result = alice.age++; ] result == 30 && alice.age == 31 } := by
  sol_symex
  sol_close

/-- `values[1] = 40; result = values[1]++;` (`storageIndexIncrementAssignment`). -/
theorem indexPostIncrementAssign :
    ⊨ dl!{ [ values[1] = 40; result = values[1]++; ] result == 40 && values[1] == 41 } := by
  sol_symex
  sol_close

/-! ## 7 · Operands captured

An operator computes only on simple operands; a read is captured into a fresh
local first (`binopUnfoldLeft`), and a value written to storage is frozen by the
write's own capture rule (`fieldWriteValueRhsCapture`).  A state variable is
not simple: it is read like any other location. -/

/-- `result = i + a;` — both operands simple (`binopAssignment`). -/
theorem binopSimple : ⊨ dl!{ [ result = i + a; ] result == i + a } := by
  sol_symex
  sol_close

/-- `uint r = alice.age + a;` — the field operand is captured. -/
theorem addFieldOperandCaptured :
    ⊨ dl!{ [ uint r = alice.age + a; ] r == alice.age + a } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  apply unfold .binopUnfoldLeft
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply update .binopAssignment
  apply empty
  apply close
  sol_symex
  sol_close

/-- `result = age + a;` — a state variable operand is not simple either: it is
captured and read with `select`. -/
theorem rootOperandCaptured : ⊨ dl!{ [ result = age + a; ] result == age + a } := by
  sol_symex
  sol_close

/-- `alice.age = x + y;` — the source is frozen before the write. -/
theorem addResultCaptured :
    ⊨ dl!{ x == 1 && y == 2 → [ alice.age = x + y; ] alice.age == 3 } := by
  apply Proves.valid
  apply intro
  apply unfold .fieldWriteValueRhsCapture
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply update .storageFieldWriteSave
  apply empty
  apply close
  sol_symex
  sol_close

/-- `assert(a == b);` — the condition is captured, then asserted
(`assertConditionCapture`, `assertSimple`); past it, it holds. -/
theorem assertConditionCaptured : ⊨ dl!{ [ assert(a == b); ] a == b } := by
  sol_symex
  sol_close

/-- `to.transfer(5);` — both operands simple: one update on the `net` ledger
(`transferNoCallback`). -/
theorem transferSimple : ⊨ dl!{ [ to.transfer(5); ] true } := by
  apply Proves.valid
  apply update .transferNoCallback
  apply empty
  apply close
  sol_symex
  sol_close

/-- `owner.transfer(5);` — a state variable as the receiver is captured first
(`transfer_unfold_leftFstReceiver`). -/
theorem transferRootReceiver : ⊨ dl!{ [ owner.transfer(5); ] true } := by
  apply Proves.valid
  apply unfold .transfer_unfold_leftFstReceiver
  apply unfold .localValueDeclInitDrop
  apply update .storageRootReadSelect
  apply update .transferNoCallback
  apply empty
  apply close
  sol_symex
  sol_close

/-- `to.transfer(x + 2);` — a non-simple amount is captured first
(`transfer_unfold_rightSndArgument`, `net-transfer-capture-argument.key`). -/
theorem transferAmountCaptured : ⊨ dl!{ [ to.transfer(x + 2); ] true } := by
  apply Proves.valid
  apply unfold .transfer_unfold_rightSndArgument
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply update .transferNoCallback
  apply empty
  apply close
  sol_symex
  sol_close

/-! ## 8 · Memory targets

The same compound assignments and increments on a memory object: `read`/`write`
on the heap in place of `find`/`save`.  `sol_close` has no equations for the heap
(`Close.lean`), so these are the walks, ending in `true`. -/

/-- `Person memory m; m.age++;` (`memoryFieldIncrement`). -/
theorem memoryFieldIncrement : ⊨ dl!{ [ Person memory m; m.age++; ] true } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply update .memoryFieldIncrement
  apply empty
  apply close
  sol_symex
  sol_close

/-- `Person memory m; result = m.age++;` (`memoryFieldIncrementAssignment`). -/
theorem memoryFieldIncrementAssign :
    ⊨ dl!{ [ Person memory m; result = m.age++; ] true } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply update .memoryFieldIncrementAssignment
  apply empty
  apply close
  sol_symex
  sol_close

/-- `uint[] memory a; ++a[i];` (`memoryIndexArrayIncrement`). -/
theorem memoryIndexIncrement : ⊨ dl!{ [ uint[] memory a; ++a[i]; ] true } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply update .memoryIndexArrayIncrement
  apply empty
  apply close
  sol_symex
  sol_close

/-- `Person memory m; m.account.balance++;` — the receiver is bound to a memory
local first (`memoryFieldIncrementUnfoldLeftFst`). -/
theorem memoryDeepIncrement : ⊨ dl!{ [ Person memory m; m.account.balance++; ] true } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply unfold .memoryFieldIncrementUnfoldLeftFst
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldIncrement
  apply empty
  apply close
  sol_symex
  sol_close

/-- `Person memory m; m.age /= a;` — division is the same rule as the other
operators (`memoryFieldOpAssign`); the zero divisor is the interpreter's. -/
theorem memoryFieldOpAssign : ⊨ dl!{ [ Person memory m; m.age /= a; ] true } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply update .memoryFieldOpAssign
  apply empty
  apply close
  sol_symex
  sol_close

/-- `uint[] memory v; v[i] *= a;` (`memoryIndexArrayOpAssign`). -/
theorem memoryIndexOpAssign : ⊨ dl!{ [ uint[] memory v; v[i] *= a; ] true } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply update .memoryIndexArrayOpAssign
  apply empty
  apply close
  sol_symex
  sol_close

/-- `Person memory m; m.account.balance += a;` (`memoryFieldOpAssignUnfoldLeftFst`). -/
theorem memoryDeepOpAssign :
    ⊨ dl!{ [ Person memory m; m.account.balance += a; ] true } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply unfold .memoryFieldOpAssignUnfoldLeftFst
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldOpAssign
  apply empty
  apply close
  sol_symex
  sol_close

end Solidity.Examples.StorageSteps
