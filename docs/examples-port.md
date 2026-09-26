# Where the storage examples of the untyped layer went

The untyped layer wrote its storage examples as `sol_derivation` chains
(Solidity/Traces/Storage.lean), `seq_steps` lists
(`Solidity/Examples/Derivations/`), single `rule_step`s and `native_decide`
checks over `sol!{ … }` (Solidity/Examples/Taclets/StorageOps.lean and four
small files). They are gone with the layer. This file records, for each of
them, the theorem of the typed layer that states the same program, or why
there is none.

The new homes are all in `Solidity/Examples/`:

| File | What it holds |
|---|---|
| `Tour.lean` | the running example, by hand and by the strategy |
| `StorageSteps.lean` | one statement form at a time: a walk (`apply` per taclet) for each worked example, `sol_symex; sol_close` for the rest |
| `StorageSuite.lean` | solkey's `taclets` suite, deduplicated; claims about the initial store are runs of the interpreter |
| `StorageDelete.lean` | `delete`, and reading after it |
| `LedgerDelete.lean` | the `Ledger` program, in the calculus and in the storage theory |

A name below is a theorem of the file it is prefixed with. **added** marks one
written for this port because nothing stated its program. Reasons for a
dropped example are of three kinds:

* **duplicate of X** — the same taclet on the same shape; the operator, the
  constant, or the source being an alias rather than a root is all that
  differs;
* **not expressible** — the typed syntax does not have it: `--` (it starts a
  comment in Lean; one rule serves `++` and `--`), an increment inside an
  index (`++i`, `i++` parse only as a statement or as the right of an
  assignment), a member of `push()`, `push()` as an assignment target,
  `.length`, and the untyped layer's extra members (`alice.accounts`,
  `alice.friends`, `alice.account.tokens`) and roots (`carol`, `tokens`,
  `account`), which `StandardExample` does not declare. An example the
  elaborator rejects as ill-typed is also here;
* **not closable** — expressible, but `sol_close` leaves a goal. Every such
  goal here is the same one: a read *below* a deleted struct is
  `a.defaultOf.find (f :: q)` for a value `a` it knows nothing about, and
  there is no lemma relating `find` of `SVal.defaultOf` to `find`
  (`Calculus/Close.lean`). The claim is then checked on a run of the
  interpreter from the contract's initial store (`#eval`, since a struct's
  default is the well-founded `defaultForTy`, which `rfl` does not unfold).

For `delete alice.account; uint b = alice.account.balance;` the goal
`sol_close` leaves is

```
h_6  : τ.findStorage "alice" [.field "account"] = .ok a
h_8  : τ.saveStorage "alice" [.field "account"] a.defaultOf = .ok τ₁
h_14 : a.defaultOf.find [.field "balance"] = .ok a₁
h_16 : a₁.asValue = .ok a₂
h_17 : ¬ a₂ = .int 0
⊢ False
```

and for `ledger.nonce = 42; delete ledger; uint v = ledger.nonce;` the same
with `ledger`, `[]` and `nonce`.

## Solidity/Traces/Storage.lean

| Old | New |
|---|---|
| `fieldWriteSimple` | `StorageSteps.fieldWriteSimple` |
| `fieldWriteFromAlias` | `StorageSteps.fieldWriteFromAlias` |
| `deepFieldWrite` | `StorageSteps.deepFieldWrite` (walk), `StorageSteps.deepFieldWrite_symex` |
| `deepFieldRead` | `StorageSteps.deepFieldRead` |
| `deeperFieldWrite` | `StorageSteps.deeperFieldWrite` |
| `rootRead` | `StorageSteps.rootRead` |
| `rootWriteFromGlobal` | `StorageSteps.rootWriteFromGlobal` |
| `rootWriteFromAlias` | `StorageSteps.rootWriteFromAlias` (`alice = pp;` is `Person storage p = bob; alice = p;`) |
| `localRebindThenWrite` | `StorageSteps.localRebindThenWrite` |
| `globalRootCopy` | `StorageSteps.globalRootCopy` (`account = bob.account;` is `tok = bob.account.token;` on `TestSuite`: no `account` root) |
| `arrayIndexReadBox` | `StorageSteps.arrayIndexRead` (no bounds branch: the halt is the interpreter's) |
| `arrayIndexReadDiamond` | `StorageSteps.arrayIndexReadDiamond`, now a refutation |
| `arrayIndexWrite` | `StorageSteps.arrayIndexWrite` |
| `mappingIndexRead` | `StorageSteps.mappingIndexRead` |
| `arrayIndexWriteRefSource` | `StorageSteps.arrayIndexWriteRefSource` (on `people`, from an alias of `bob`) |
| `nonsimplePathIndexWrite` | `StorageSteps.nonsimplePathIndexWrite` (`matrix[i][j] = 100;`: no struct has an array member) |
| `nonsimplePathIncIndexWrite` | `StorageSteps.receiverAndIndexCaptured` — `++i` in an index is not expressible; that theorem has the non-simple receiver and index in the same order |
| `receiverAndIndexSideEffects` | `StorageSteps.receiverAndIndexCaptured` (`matrix[i + 1][j + 1] = 77;`, `i++` in an index not expressible); the whole chain now, not only its first step |
| `arrayPush` | `StorageSteps.arrayPush` |
| `arrayPopBox` | `StorageSteps.arrayPop` |
| `arrayPopDiamond` | `StorageSteps.arrayPopDiamond`, a refutation |
| `pushRefSource` | `StorageSteps.pushRefSource` |
| `pushNonsimpleReceiver` | `StorageSteps.pushNonsimpleReceiver` (`bucket.tokens.push(t);`) |
| `bucketPushBare` | `StorageSteps.bucketPushBare` |
| `pushBare` | `StorageSteps.pushBare` |
| `pushSlotWrite` | `StorageSteps.pushSlotWrite` (a member of `push()` is not expressible: the slot is bound to an alias) |
| `pushThenPushSlotRead` | duplicate of `StorageSteps.pushSlotWrite`, whose postcondition reads the slot back |
| `popAfterPush` | `StorageSteps.popAfterPush` |
| `rootWriteThenIncrement` | `StorageSteps.rootWriteThenIncrement` |
| `deleteField` | `StorageDelete.deleteField` |
| `deleteAccountThenReadLeaves` | not closable (the goal above); the run is `StorageDelete.lean`'s first `#eval` |
| `deleteIncIndexThenLength` | not expressible (`alice.account.tokens`, `++i` in an index, `.length`); the captured-index delete is `StorageDelete.deleteNonSimpleIndex` |
| `deleteStructThenRead` | `LedgerDelete.deleteLedger` for the delete; the read is not closable (the goal above), and is the `#eval` of `after` and `LedgerDelete.Store.nonceAfterDelete` |
| `deleteLedgerMappingSurvives` | not closable (below `delete ledger`); the run is `LedgerDelete.lean`'s last `#eval` (`kept * 100 + nonce0 * 10 + gone == 1000`) |
| `fieldCompoundAssign` | `StorageSteps.fieldCompoundAssign` (no `¬⊤` branch: the divisor guard is the interpreter's) |

## Solidity/Examples/Derivations/StorageSteps.lean

The same chains as Traces/Storage.lean, name for name, as `seq_steps` lists.

| Old | New |
|---|---|
| `deepFieldWrite` | `StorageSteps.deepFieldWrite` |
| `deepFieldWriteListed` | `StorageSteps.deepFieldWrite_symex` (the rules chosen by the strategy) |
| `fieldWriteSimple`, `fieldWriteFromAlias`, `deepFieldRead`, `deeperFieldWrite`, `rootRead`, `rootWriteFromGlobal`, `rootWriteFromAlias`, `localRebindThenWrite`, `globalRootCopy` | as in Traces/Storage.lean above |
| `arrayIndexReadBox`, `arrayIndexReadDiamond`, `arrayIndexWrite`, `mappingIndexRead`, `arrayIndexWriteRefSource`, `nonsimplePathIndexWrite`, `nonsimplePathIncIndexWrite`, `receiverAndIndexSideEffects` | as in Traces/Storage.lean above |
| `arrayPush`, `arrayPopBox`, `arrayPopDiamond`, `pushRefSource`, `pushNonsimpleReceiver`, `bucketPushBare`, `pushBare`, `pushSlotWrite`, `pushThenPushSlotRead`, `popAfterPush`, `rootWriteThenIncrement` | as in Traces/Storage.lean above |
| `deleteField`, `deleteAccountThenReadLeaves`, `deleteIncIndexThenLength`, `deleteStructThenRead`, `deleteLedgerMappingSurvives` | as in Traces/Storage.lean above |
| `fieldCompoundAssign` | `StorageSteps.fieldCompoundAssign` |

## Solidity/Examples/Derivations/IncDec.lean

| Old | New |
|---|---|
| `age++;` | `StorageSteps.rootWriteThenIncrement` |
| `++age;` | duplicate of `StorageSteps.rootWriteThenIncrement` (`storageRootIncrement`) |
| `age--;`, `--age;` | not expressible (`--`) |
| `alice.age++;` | duplicate of `StorageSuite.fieldIncrement` (`storageFieldIncrement`) |
| `result = age++` | `StorageSteps.rootPostIncrementAssign` |
| `result = ++age` | `StorageSteps.rootPreIncrementAssign` |
| `result = values[i]++` | `StorageSteps.indexPostIncrementAssign` |
| `fieldPostIncrementComplexPath` | `StorageSteps.deepIncrement` |
| `rootPostincrementProgram` | `StorageSteps.rootWriteThenIncrement` (the read is its postcondition) |
| `carol.age++;` | `StorageSteps.memoryFieldIncrement` (on `Person memory m;`: `carol` is not a root) |
| `result = carol.age++` | `StorageSteps.memoryFieldIncrementAssign` |
| `++mv[i];` | `StorageSteps.memoryIndexIncrement` |
| `memoryFieldPostIncrementComplexPath` | `StorageSteps.memoryDeepIncrement` |

## Solidity/Examples/Derivations/CompoundAssign.lean

| Old | New |
|---|---|
| `age += amount` | `StorageSteps.rootOpAssign` |
| `alice.age -= amount` | `StorageSuite.fieldOpAssign` |
| `values[i] *= amount` | duplicate of `StorageSteps.indexOpAssign` (`/=`; one rule for the five operators) |
| `fieldAddAssignComplexPath` | `StorageSteps.deepOpAssign` (a simple source is no longer frozen) |
| `fieldAddAssignProgram` | `StorageSteps.fieldCompoundAssign`, `StorageSuite.fieldOpAssign` |
| `carol.age += amount` | duplicate of `StorageSteps.memoryFieldOpAssign` |
| `carol.age /= amount` | `StorageSteps.memoryFieldOpAssign` |
| `mv[i] *= amount` | `StorageSteps.memoryIndexOpAssign` |
| `memoryFieldAddAssignComplexPath` | `StorageSteps.memoryDeepOpAssign` |

## Solidity/Examples/Derivations/ValueCapture.lean

| Old | New |
|---|---|
| `result = i + amount` | `StorageSteps.binopSimple` |
| `result = age + amount` | `StorageSteps.rootOperandCaptured` (**added**; a state variable is no longer simple, so this now captures) |
| `addFieldOperandCaptured` | `StorageSteps.addFieldOperandCaptured` |
| `addResultCaptured` | `StorageSteps.addResultCaptured` |
| `assert(flag)` | duplicate of `StorageSteps.assertConditionCaptured`, whose last step is `assertSimple` |
| `assertConditionCaptured` | `StorageSteps.assertConditionCaptured` |
| `to.transfer(amount)` | `StorageSteps.transferSimple` |
| `owner.transfer(amount)` | `StorageSteps.transferRootReceiver` (the root is now captured first) |
| `transferAmountCaptured` | `StorageSteps.transferAmountCaptured` (**added**) |

## Solidity/Examples/Derivations/LedgerDelete.lean

| Old | New |
|---|---|
| `ledgerWriteThenDelete` | `LedgerDelete.ledgerWriteThenDelete` up to the struct delete; the read after it is not closable (the goal above) and is the `#eval` of `after` and `LedgerDelete.Store.nonceAfterDelete` |
| `deletedEntry` | `LedgerDelete.Store.deletedEntry` |
| `deletedEntryWritten` | `LedgerDelete.Store.deletedEntryWritten` (a `calc` for the `sol_rewrite`) |
| `survivingEntry` | `LedgerDelete.Store.survivingEntry` |
| `nonceBeforeDelete` | `LedgerDelete.Store.nonceBeforeDelete` |
| `nonceAfterDelete` | `LedgerDelete.Store.nonceAfterDelete` |

## Solidity/Examples/Derivations/Walkthroughs.lean

| Old | New |
|---|---|
| `storageFieldDeepWriteRead` | `Tour.runningExample_byHand` (with `10` for `34`) |
| `storageIndexPostincrementAssign` | `StorageSteps.indexPostIncrementAssign` |

## Solidity/Examples/Taclets/StorageOps.lean

Anonymous `example`s, named here by their `.key` file. A length premise is
dropped rather than established by pushes: under the box an out-of-bounds
write reverts, which satisfies the formula.

| Old | New |
|---|---|
| `storage-root-read-write` | `StorageSuite.rootWriteRead` |
| `storage-root-multiple-writes` | `StorageSuite.rootMultipleWrites` |
| `storage-field-write-read` | `StorageSteps.fieldWriteSimple` |
| `storage-field-deep-write-read`, `storage-field-decomposition` | `Tour.runningExample` |
| `storage-field-deep-value` | `StorageSteps.deeperFieldWrite` |
| `storage-field-global-age`, `storage-field-read-store-root` | `StorageSuite.rootFromField` |
| `storage-root-copy-source` | `StorageSuite.rootFromRoot` |
| `storage-root-copy-struct` | `StorageSuite.rootCopyStruct` (**added**) |
| copies are by value | `StorageSuite.rootCopyByValue` (**added**) |
| `storage-field-disjoint-roots` | `StorageSuite.disjointRoots` |
| `storage-field-disjoint-fields` | `StorageSuite.disjointFields` |
| `storage-field-copy-struct` | `StorageSuite.fieldCopyStruct` (**added**) |
| `storage-index-root-array` | `StorageSteps.arrayIndexWrite` |
| `storage-index-multiple-writes` | `StorageSuite.arrayMultipleWrites` |
| `storage-index-root-mapping` | `StorageSuite.mappingWriteRead` |
| `storage-matrix-write-read`, `storage-index-decomposition` | `StorageSuite.matrixWriteRead` (**added**) |
| `storage-index-decompose-after-push` | `StorageSuite.decomposeAfterPush` |
| `storage-index-copysource-after-push` | `StorageSuite.lean`'s `#eval` of `matrix[0][1]`; the `matrix[0][0] == 5` half is a duplicate |
| `storage-index-array-out-of-bounds-box` | `StorageSuite.arrayOutOfBounds` |
| `storage-alias-rebind-alias` | `StorageSuite.aliasRebind` |
| `storage-alias-rebind-original` | `StorageSuite.aliasRebindOriginal` |
| `storage-alias-write-balance`, `storage-alias-write-token` | `StorageSuite.aliasWrites` |
| `storage-field-read-bind-local` | `StorageSuite.aliasBindMember` |
| `storage-local-decl-skip` | `StorageSuite.localDeclSkip` |
| `storage-root-add-assign` | `StorageSteps.rootOpAssign` |
| `storage-root-mul-assign` | `StorageSuite.rootMulAssign` |
| `storage-root-{sub,div,mod}-assign` | duplicates of `StorageSteps.rootOpAssign` |
| `storage-field-add-assign` | `StorageSteps.fieldCompoundAssign` |
| `storage-field-sub-assign` | `StorageSuite.fieldOpAssign` |
| `storage-field-{mul,div,mod}-assign` | duplicates of `StorageSuite.fieldOpAssign` |
| `storage-field-deep-add-assign` | `StorageSuite.deepOpAssignRead` (**added**) |
| `storage-field-deep-{sub,mul,div,mod}-assign` | duplicates of `StorageSuite.deepOpAssignRead` |
| `storage-index-div-assign` | `StorageSteps.indexOpAssign` |
| `storage-index-{add,sub,mul,mod}-assign` | duplicates of `StorageSteps.indexOpAssign` |
| zero divisor in `/=` | `StorageSuite.divByZero` |
| `storage-root-preincrement` | duplicate of `StorageSteps.rootWriteThenIncrement` |
| `storage-root-postincrement` | `StorageSteps.rootWriteThenIncrement` |
| `storage-root-postincrement-assign` | `StorageSteps.rootPostIncrementAssign` |
| `storage-root-preincrement-assign` | `StorageSteps.rootPreIncrementAssign` |
| `storage-field-preincrement` | `StorageSuite.fieldIncrement` |
| `storage-field-postincrement` | duplicate of `StorageSuite.fieldIncrement` |
| `storage-field-postincrement-assign` | `StorageSteps.fieldPostIncrementAssign` |
| `storage-field-preincrement-assign` | duplicate of `StorageSteps.fieldPostIncrementAssign` |
| `storage-deep-field-preincrement` | `StorageSuite.deepIncrementRead` (**added**) |
| `storage-deep-field-postincrement` | duplicate of `StorageSuite.deepIncrementRead` |
| `storage-index-preincrement` | `StorageSteps.indexIncrement` |
| `storage-index-postincrement` | duplicate of `StorageSteps.indexIncrement` |
| `storage-index-postincrement-assign` | `StorageSteps.indexPostIncrementAssign` |
| `storage-index-preincrement-assign` | duplicate of `StorageSteps.indexPostIncrementAssign` |
| `storage-{root,field,index}-{pre,post}decrement`, `…-decrement-assign` (nine examples) | not expressible (`--`) |
| `storage-root-delete` | `StorageDelete.deleteThenRead` |
| `storage-field-delete` | `StorageDelete.deleteFieldThenRead` |
| `storage-root-delete-struct` | not closable; `StorageDelete.lean`'s `#eval` of `delete alice;` |
| `delNode` keeps a mapping member | not closable; `StorageDelete.lean`'s `#eval` of `kept` (`42`) |
| `delNode` resets a value member | not closable; `StorageDelete.lean`'s `#eval` of `o` (`0`) |
| `storage-index-delete` | `StorageDelete.deleteIndexThenRead` |
| `storage-index-delete-mapping-bool` | `StorageDelete.deleteBoolThenRead` |
| `storage-index-delete-mapping-struct` | not closable; `StorageDelete.lean`'s `#eval` of `folks[1].age` |
| `storage-push-empty` | `StorageSuite.lean`'s `#eval` of `values[2]` |
| `storage-push-value` | `StorageSuite.pushValue` |
| `storage-push-nonsimple-arg` | `StorageSuite.pushNonsimpleArg` |
| `storage-push-return-assign` | not expressible (`values.push() = 42;`: `push()` is not an assignment target) |
| `storage-push-local-bind` | `StorageSuite.lean`'s `#eval` of `persons[2].age` |
| `storage-pop-nonempty` | `StorageSuite.lean`'s `#eval` of `values[0]`, and `StorageSuite.popNonemptyGone` |
| `storage-pop-empty-box` | `StorageSuite.popEmpty` |
| `storage-pop-after-push` | `StorageSuite.popAfterPushRead` |
| a popped slot keeps its mappings (two) | `StorageSuite.lean`'s two `#eval`s on `ledgerUses` |
| `ifThenElseRules` | `StorageSuite.ifOnStorage` |
| `assert` holds / violated (box, diamond) | `StorageSuite.assertHolds`, `assertFails`, `assertFailsDiamond` |
| `require` holds / violated (box, diamond) | `StorageSuite.requireHolds`, `requireFails`, `requireFailsDiamond` |

## Solidity/Examples/StorageFieldWriteRead.lean

| Old | New |
|---|---|
| Example 1, `alice.age = amount` | `StorageSteps.fieldWriteSimple` |
| Example 2, `alice.account.balance = amount` | `StorageSteps.deepFieldWrite` |
| Example 3, `alice.account.token.value = amount` | `StorageSteps.deeperFieldWrite` |
| Example 4, `amount = alice.age` | `StorageSteps.fieldRead` |
| Example 5, `amount = alice.account.balance` | `StorageSteps.deepFieldRead` |

## Solidity/Examples/StorageRootOps.lean

| Old | New |
|---|---|
| Example 6, `amount = alice` | not expressible: a struct read into a `uint` is rejected ("a storage reference where a uint is expected"); a root read is `StorageSteps.rootRead` |
| Example 7, `alice = bob` | `StorageSteps.rootWriteFromGlobal` |
| Example 8, `sp = bob` | `StorageSuite.aliasRebind` (`storageLocalRootRebind`, also a step of `StorageSteps.rootWriteFromAlias`) |

## Solidity/Examples/StorageArrayOps.lean

| Old | New |
|---|---|
| Example 9, `people[i] = bob` | duplicate of `StorageSteps.arrayIndexWriteRefSource` (same taclet, the source an alias of `bob`) |
| Example 10, `people[i] = amount` | not expressible: ill-typed, a `uint` where a `Person` is expected |
| Example 11, `sp = people[i]` | `StorageSteps.aliasFromIndex` (**added**) |
| Example 12, `people.push(bob)` | duplicate of `StorageSteps.pushRefSource` (same taclet) |
| Example 13, `people.pop()` | `StorageSteps.arrayPop` |
| Example 14, `alice.friends[i] = bob` | `StorageSteps.refIndexWriteNonsimpleReceiver` (`bucket.tokens[i] = tok;`: `Person` has no array member) |

## Solidity/Examples/StorageCompound.lean

| Old | New |
|---|---|
| Example 18, `alice.age += 1` desugared | `StorageSteps.compoundDesugared` (**added**) |
