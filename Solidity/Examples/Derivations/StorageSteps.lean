import Solidity.Tactics.Derivation
import Solidity.Semantics.DecEq

/-!
# The storage derivations read one step at a time

`Solidity/Paper/Storage.lean` writes the calculus's storage chains as
`sol_derivation`: every intermediate frontier is *written*, and the command
folds the lines into one theorem.  That is what the paper prints.  This file is
the same facts in the other presentation — the two endpoints in the statement,
the rules in the proof — for the times when what you want is to step through a
derivation rather than read one off the page.  Sections and names are that
file's, one for one, so the two read in parallel.

The headline chain, `alice.account.balance = 10;`, is here twice, because it is
where the two spellings can be compared:

* `deepFieldWrite`, one `seq_step` per rule.  The goal between any two lines is
  the frontier the paper draws there, so the derivation can be walked with the
  cursor.
* `deepFieldWriteListed`, the same rules as one `seq_steps [...]`.  The cursor
  on a rule name shows the frontier that rule was applied to; at the end of a
  line, the frontier the rules up to there have reached.

Everything after it is the second spelling only.

`seq_steps?` is how the rule lists were obtained, and how the next one should
be.  It is an oracle and not an authority: `localRebindThenWrite` is a chain it
reports as failing — its merge keeps two of three updates stacked, which
`sameShape` does not recognise — and whose suggested list `seq_steps` then
proves, because `seq_done` calls `upd_merge` directly.

The frontier the goal shows between two steps is printed by
`Update/SequentPP.lean`, so it reads as the line the paper draws rather than as
the constructor applications it is.  Where the two differ it is because the
term does not carry the annotation: `se@uint` is a `Rules.writeBack` whose
left-hand side is gone by the time the update exists, so it comes back as `se`.

Two things the `sol_derivation` command does for a chain that a hand-written
`seq!` line does not.  The bare `(φ)` goal of the last line carries no
modality, so it is read as the **combined** one (`Update/SequentSyntax.lean`) —
which is what `<[ … ]>` on the first line is, so the endpoints still agree.
And the paper draws the merge as its own `=` line; here it is the last thing
`seq_done` does, since a `⇝ᵘ*` may absorb a trailing merge.

This file is in the default build and `Paper/Storage.lean` is not, so these
chains are also what keeps a storage rule rename a `./run-lean.sh` failure.
It can afford to be: all of it elaborates in about eleven seconds, against the
minutes the same chains cost as `sol_derivation`s.  What the paper target pays
for is *writing the intermediate lines down* — each one re-elaborated and
checked against the frontier — and that is exactly what this presentation does
not do.
-/

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax Semantics

set_option maxHeartbeats 8000000

section
variable (φ : WrappedExpr)

/-- `alice.account.balance = 10;` — the paper's headline chain, proved one rule
per line.  Put the cursor on any `seq_step` to see the frontier the rule before
it left. -/
theorem deepFieldWrite :
    [ seq!{ => <[ alice.account.balance = 10 ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { se@uint := 10 ‖ sp@Account := path(alice.account)
                       ‖ storage := save(alice.account.balance, 10) } (φ) } ] := by
  seq_step .storageFieldWriteUnfoldLeftFst
  seq_step .localValueDeclInitDrop
  seq_step .valueDeclSkip
  seq_step .localValueAssign
  seq_step .storagePlaceAlias
  seq_step .storageFieldWriteSave
  seq_done

/-- The same chain as one line.  `seq_steps` gives each rule its own info node,
so the frontiers are still there to look at — they are just not on the page. -/
theorem deepFieldWriteListed :
    [ seq!{ => <[ alice.account.balance = 10 ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { se@uint := 10 ‖ sp@Account := path(alice.account)
                       ‖ storage := save(alice.account.balance, 10) } (φ) } ] := by
  seq_steps [.storageFieldWriteUnfoldLeftFst, .localValueDeclInitDrop,
             .valueDeclSkip, .localValueAssign, .storagePlaceAlias,
             .storageFieldWriteSave]

/-! ## 1 · Storage fields and roots -/

/-- `alice.age = ageVal;` -/
theorem fieldWriteSimple :
    [ seq!{ => <[ alice.age = ageVal ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := save(alice.age, ageVal) } (φ) } ] := by
  seq_steps [.storageFieldWriteSave]

/-- `Account storage acc = bob.account; alice.account = acc;` -/
theorem fieldWriteFromAlias :
    [ seq!{ => <[ Account storage acc = bob.account; alice.account = acc ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { acc := path(bob.account) }
                    { storage := copy(alice.account, acc) } (φ) } ] := by
  seq_steps [.storagePlaceAlias, .storageFieldWriteCopySource]

/-- `v = alice.account.balance;` -/
theorem deepFieldRead :
    [ seq!{ => <[ v = alice.account.balance ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { sp@Account := path(alice.account)
                       ‖ v := alice.account.balance } (φ) } ] := by
  seq_steps [.storageFieldReadUnfoldRightFst, .storagePlaceAlias,
             .storageFieldReadFind]

/-- `alice.account.token.value = 5;` -/
theorem deeperFieldWrite :
    [ seq!{ => <[ alice.account.token.value = 5 ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { se@uint := 5 ‖ sp@Token := path(alice.account.token)
                       ‖ storage := save(alice.account.token.value, 5) } (φ) } ] := by
  seq_steps [.storageFieldWriteUnfoldLeftFst, .localValueDeclInitDrop,
             .valueDeclSkip, .localValueAssign, .storagePlaceAlias,
             .storageFieldWriteSave]

/-- `uint v = total;` -/
theorem rootRead :
    [ seq!{ => <[ uint v = total ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { v := default(uint) } { v := total } (φ) } ] := by
  seq_steps [.localValueDeclInitDrop, .valueDeclSkip,
             .storageRootReadSelect]

/-- `alice = bob;` -/
theorem rootWriteFromGlobal :
    [ seq!{ => <[ alice = bob ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := copy(alice, bob) } (φ) } ] := by
  seq_steps [.storageRootWriteCopySource]

/-- `alice = pp;` -/
theorem rootWriteFromAlias :
    [ seq!{ => <[ alice = pp ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := copy(alice, pp) } (φ) } ] := by
  seq_steps [.storageRootWriteCopySource]

/-- `Account storage acc = alice.account; acc = bob.account; acc.balance = 10;`
-- a rebind, not a copy. -/
theorem localRebindThenWrite :
    [ seq!{ => <[ Account storage acc = alice.account; acc = bob.account;
                  acc.balance = 10 ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { acc := path(alice.account) }
                    { acc := path(bob.account)
                      ‖ storage := save(bob.account.balance, 10) } (φ) } ] := by
  seq_steps [.storagePlaceAlias, .storageFieldReadBindLocalRoot,
             .storageFieldWriteSave]

/-- `account = bob.account;` -- a global root, so a deep copy. -/
theorem globalRootCopy :
    [ seq!{ => <[ account@@Account = bob.account ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := copy(account@@Account, bob.account) } (φ) } ] := by
  seq_steps [.storageFieldReadStoreRoot]

/-! ## 2 · Storage arrays -/

/-- `v = values[i];`, box. -/
theorem arrayIndexReadBox :
    [ seq!{ => [ v = values[i] ](φ) } ]
      ⇝ᵘ* [ seq!{ inBounds(values[i]) => { v := values[i] } [ ](φ) },
            seq!{ ¬inBounds(values[i]) => ⊤ } ] := by
  seq_steps [.storageIndexReadArrayFindBox, .revertBox]

/-- `v = values[i];`, diamond. -/
theorem arrayIndexReadDiamond :
    [ seq!{ => < v = values[i] >(φ) } ]
      ⇝ᵘ* [ seq!{ inBounds(values[i]) => { v := values[i] } < >(φ) },
            seq!{ ¬inBounds(values[i]) => ⊥ } ] := by
  seq_steps [.storageIndexReadArrayFindDiamond, .revertDiamond]

/-- `values[i] = 100;` -/
theorem arrayIndexWrite :
    [ seq!{ => [ values[i] = 100 ](φ) } ]
      ⇝ᵘ* [ seq!{ inBounds(values[i]) =>
                    { storage := save(values[i], 100) } [ ](φ) },
            seq!{ ¬inBounds(values[i]) => ⊤ } ] := by
  seq_steps [.storageIndexWriteArraySaveBox, .revertBox]

/-- `v = balances[i];` -- a mapping key, so no bounds goal. -/
theorem mappingIndexRead :
    [ seq!{ => <[ v = balances[i] ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { v := balances[i] } (φ) } ] := by
  seq_steps [.storageIndexReadMappingFind]

/-- `Token storage tokRef = bob.account.token; tokens[i] = tokRef;` -/
theorem arrayIndexWriteRefSource :
    [ seq!{ => [ Token storage tokRef = bob.account.token;
                 (tokens@@TokenArray)[i] = tokRef ](φ) } ]
      ⇝ᵘ* [ seq!{ { tokRef := path(bob.account.token) }
                    inBounds((tokens@@TokenArray)[i]) =>
                    { tokRef := path(bob.account.token) }
                    { storage := copy((tokens@@TokenArray)[i], tokRef) } [ ](φ) },
            seq!{ { tokRef := path(bob.account.token) }
                    ¬inBounds((tokens@@TokenArray)[i]) =>
                    { tokRef := path(bob.account.token) } ⊤ } ] := by
  seq_steps [.storagePlaceAlias, .storageIndexWriteArrayCopySourceBox,
             .revertBox]

/-- `alice.accounts[i] = 100;` -- a nonsimple path under an index. -/
theorem nonsimplePathIndexWrite :
    [ seq!{ => [ alice.accounts[i] = 100 ](φ) } ]
      ⇝ᵘ* [ seq!{ { se@uint := default(uint) } { se@uint := 100 }
                    { sp@UintArray := path(alice.accounts) }
                    inBounds(sp@UintArray[i]) =>
                    { se@uint := default(uint) } { se@uint := 100 }
                    { sp@UintArray := path(alice.accounts) }
                    { storage := save(sp@UintArray[i], se@uint) } [ ](φ) },
            seq!{ { se@uint := default(uint) } { se@uint := 100 }
                    { sp@UintArray := path(alice.accounts) }
                    ¬inBounds(sp@UintArray[i]) =>
                    { se@uint := default(uint) } { se@uint := 100 }
                    { sp@UintArray := path(alice.accounts) } ⊤ } ] := by
  seq_steps [.storageIndexWriteUnfoldLeftFst, .localValueDeclInitDrop,
             .valueDeclSkip, .localValueAssign, .storagePlaceAlias,
             .storageIndexWriteArraySaveBox, .revertBox]

/-- `alice.accounts[++i] = amount;` -- the index is nonsimple too. -/
theorem nonsimplePathIncIndexWrite :
    [ seq!{ => [ alice.accounts[++i] = amount ](φ) } ]
      ⇝ᵘ* [ seq!{ { se@uint := default(uint) } { se@uint := amount }
                    { sp@UintArray := path(alice.accounts) }
                    { ie@uint := default(uint) } { bump(++i) ‖ ie@uint := ++i }
                    inBounds(sp@UintArray[ie@uint]) =>
                    { se@uint := default(uint) } { se@uint := amount }
                    { sp@UintArray := path(alice.accounts) }
                    { ie@uint := default(uint) } { bump(++i) ‖ ie@uint := ++i }
                    { storage := save(sp@UintArray[ie@uint], se@uint) } [ ](φ) },
            seq!{ { se@uint := default(uint) } { se@uint := amount }
                    { sp@UintArray := path(alice.accounts) }
                    { ie@uint := default(uint) } { bump(++i) ‖ ie@uint := ++i }
                    ¬inBounds(sp@UintArray[ie@uint]) =>
                    { se@uint := default(uint) } { se@uint := amount }
                    { sp@UintArray := path(alice.accounts) }
                    { ie@uint := default(uint) } { bump(++i) ‖ ie@uint := ++i } ⊤ } ] := by
  seq_steps [.storageIndexWriteUnfoldLeftFst, .localValueDeclInitDrop,
             .valueDeclSkip, .localValueAssign, .storagePlaceAlias,
             .localValueDeclInitDrop, .valueDeclSkip,
             (.localAssignIncrement .preInc),
             .storageIndexWriteArraySaveBox, .revertBox]

/-- `matrix[i++][i++] = 77;` -- the one decomposition step; the tail binds the
receiver alias before the receiver's own index, which is not the calculus's
order. -/
theorem receiverAndIndexSideEffects :
    [ seq!{ => [ matrix[i++][i++] = 77 ](φ) } ]
      ⇝ᵘ* [ seq!{ => [ uint se = 77;
                       UintArray storage sp = matrix[i++];
                       uint ie = i++;
                       sp@UintArray[ie@uint] = se@uint ](φ) } ] := by
  seq_steps [.storageIndexWriteUnfoldLeftFst]

/-- `values.push(42);` -/
theorem arrayPush :
    [ seq!{ => <[ values.push(42) ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := push(values, 42) } (φ) } ] := by
  seq_steps [.storagePushValueSave]

/-- `tokens.pop();`, box. -/
theorem arrayPopBox :
    [ seq!{ => [ (tokens@@TokenArray).pop() ](φ) } ]
      ⇝ᵘ* [ seq!{ nonEmpty((tokens@@TokenArray)) =>
                    { storage := pop((tokens@@TokenArray)) } [ ](φ) },
            seq!{ ¬nonEmpty((tokens@@TokenArray)) => ⊤ } ] := by
  seq_steps [.storagePopSaveBox, .revertBox]

/-- `tokens.pop();`, diamond. -/
theorem arrayPopDiamond :
    [ seq!{ => < (tokens@@TokenArray).pop() >(φ) } ]
      ⇝ᵘ* [ seq!{ nonEmpty((tokens@@TokenArray)) =>
                    { storage := pop((tokens@@TokenArray)) } < >(φ) },
            seq!{ ¬nonEmpty((tokens@@TokenArray)) => ⊥ } ] := by
  seq_steps [.storagePopSaveDiamond, .revertDiamond]

/-- `tokens.push(tokRef);` -/
theorem pushRefSource :
    [ seq!{ => <[ (tokens@@TokenArray).push(tokRef) ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := push((tokens@@TokenArray), tokRef) } (φ) } ] := by
  seq_steps [.storagePushValueCopySource]

/-- `alice.account.tokens.push(tokRef);` -- a nonsimple receiver. -/
theorem pushNonsimpleReceiver :
    [ seq!{ => <[ alice.account.tokens.push(tokRef) ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { sp@TokenArray := path(alice.account.tokens) }
                    { storage := push(sp@TokenArray, tokRef) } (φ) } ] := by
  seq_steps [.storagePushValueUnfoldLeftFstReceiver, .storagePlaceAlias,
             .storagePushValueCopySource]

/-- `bucket.tokens.push();` -- a nonsimple receiver on a state variable. -/
theorem bucketPushBare :
    [ seq!{ => <[ (bucket@@TokenBucket.tokens).push() ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { sp@TokenArray := path(bucket@@TokenBucket.tokens) }
                    { storage := push(sp@TokenArray) } (φ) } ] := by
  seq_steps [.storagePushUnfoldLeftFstReceiver, .storagePlaceAlias,
             .storagePushLengthSave]

/-- `tokens.push();` -/
theorem pushBare :
    [ seq!{ => <[ (tokens@@TokenArray).push() ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := push((tokens@@TokenArray)) } (φ) } ] := by
  seq_steps [.storagePushLengthSave]

/-- `tokens.push().value = 11;` -- the slot a bare push returns is a path. -/
theorem pushSlotWrite :
    [ seq!{ => <[ (tokens@@TokenArray).push().value = 11 ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { se@uint := default(uint) } { se@uint := 11 }
                    { sp@Token := path((tokens@@TokenArray).push()) }
                    { storage := save(sp@Token.value, se@uint) } (φ) } ] := by
  seq_steps [.storageFieldWriteUnfoldLeftFst, .localValueDeclInitDrop,
             .valueDeclSkip, .localValueAssign, .storagePlaceAlias,
             .storageFieldWriteSave]

/-- `tokens.push(); uint i = tokens.push().value;` -- the read twin. -/
theorem pushThenPushSlotRead :
    [ seq!{ => <[ (tokens@@TokenArray).push();
                  uint i = (tokens@@TokenArray).push().value ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := push((tokens@@TokenArray)) }
                    { i := default(uint) }
                    { sp@Token := path((tokens@@TokenArray).push()) }
                    { i := sp@Token.value } (φ) } ] := by
  seq_steps [.storagePushLengthSave, .localValueDeclInitDrop,
             .valueDeclSkip, .storageFieldReadUnfoldRightFst,
             .storagePlaceAlias, .storageFieldReadFind]

/-- `values.push(); values.pop();` -- the pop guard read under the push. -/
theorem popAfterPush :
    [ seq!{ => <[ values.push(); values.pop() ]>(φ) } ]
      ⇝ᵘ* [ seq!{ { storage := push(values) } nonEmpty(values) =>
                    { storage := push(values) } { storage := pop(values) }
                    <[ ]>(φ) },
            seq!{ { storage := push(values) } ¬nonEmpty(values) =>
                    { storage := push(values) } ⊤ },
            seq!{ { storage := push(values) } ¬nonEmpty(values) =>
                    { storage := push(values) } ⊥ } ] := by
  seq_steps [.storagePushLengthSave, .storagePopSaveBox, .revertBox]

/-- `age = 10; age++;` -/
theorem rootWriteThenIncrement :
    [ seq!{ => <[ age = 10; age++ ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := save(age, 10) } { bump(age++) } (φ) } ] := by
  seq_steps [.storageRootWriteStore, (.storageRootIncrement .postInc)]

/-! ## 3 · Delete -/

/-- `delete alice.account;` -/
theorem deleteField :
    [ seq!{ => <[ delete alice.account ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := clear(alice.account) } (φ) } ] := by
  seq_steps [.storageFieldDelete]

/-- `delete alice.account;` between writes and reads -- nothing merges, so the
endpoint is the five updates in order. -/
theorem deleteAccountThenReadLeaves :
    [ seq!{ => <[ alice.account.balance = 100; alice.account.token.value = 7;
                  delete alice.account; b = alice.account.balance;
                  v = alice.account.token.value ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { se@uint := default(uint) } { se@uint := 100 }
                    { sp@Account := path(alice.account) }
                    { storage := save(sp@Account.balance, se@uint) }
                    { se@uint := default(uint) } { se@uint := 7 }
                    { sp@Token := path(alice.account.token) }
                    { storage := save(sp@Token.value, se@uint) }
                    { storage := clear(alice.account) }
                    { sp@Account := path(alice.account) }
                    { b := sp@Account.balance }
                    { sp@Token := path(alice.account.token) }
                    { v := sp@Token.value } (φ) } ] := by
  seq_steps [.storageFieldWriteUnfoldLeftFst, .localValueDeclInitDrop,
             .valueDeclSkip, .localValueAssign, .storagePlaceAlias,
             .storageFieldWriteSave, .storageFieldWriteUnfoldLeftFst,
             .localValueDeclInitDrop, .valueDeclSkip, .localValueAssign,
             .storagePlaceAlias, .storageFieldWriteSave,
             .storageFieldDelete, .storageFieldReadUnfoldRightFst,
             .storagePlaceAlias, .storageFieldReadFind,
             .storageFieldReadUnfoldRightFst, .storagePlaceAlias,
             .storageFieldReadFind]

/-- `delete alice.account.tokens[++i]; len = alice.account.tokens.length;` -/
theorem deleteIncIndexThenLength :
    [ seq!{ => <[ delete alice.account.tokens[++i];
                  len = alice.account.tokens.length ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { sp@TokenArray := path(alice.account.tokens) }
                    { ie@uint := default(uint) } { bump(++i) ‖ ie@uint := ++i }
                    { storage := clear(sp@TokenArray[ie@uint]) }
                    { sp@TokenArray := path(alice.account.tokens) }
                    { len := sp@TokenArray.length } (φ) } ] := by
  seq_steps [.storageIndexDeleteUnfoldLeftFst, .storagePlaceAlias,
             .storageIndexDeleteNonSimpleIndexCapture,
             .localValueDeclInitDrop, .valueDeclSkip,
             (.localAssignIncrement .preInc), .storageIndexDelete,
             .storageFieldReadUnfoldRightFst, .storagePlaceAlias,
             .storageFieldReadFind]

/-- `ledger.nonce = 42; delete ledger; v = ledger.nonce;` -/
theorem deleteStructThenRead :
    [ seq!{ => <[ (ledger@@Ledger).nonce = 42; delete (ledger@@Ledger);
                  v = (ledger@@Ledger).nonce ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := save((ledger@@Ledger).nonce, 42) }
                    { storage := clear((ledger@@Ledger)) }
                    { v := (ledger@@Ledger).nonce } (φ) } ] := by
  seq_steps [.storageFieldWriteSave, .storageRootDelete,
             .storageFieldReadFind]

/-- the whole of the calculus's `delete ledger;` program -- the mapping
survives the struct delete, and deleting the entry is what clears it. -/
theorem deleteLedgerMappingSurvives :
    [ seq!{ => <[ (ledger@@Ledger).nonce = 5; (ledger@@Ledger).balances[1] = 10;
                  delete (ledger@@Ledger); kept = (ledger@@Ledger).balances[1];
                  delete (ledger@@Ledger).balances[1];
                  nonce = (ledger@@Ledger).nonce;
                  gone = (ledger@@Ledger).balances[1] ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := save((ledger@@Ledger).nonce, 5) }
                    { se@uint := default(uint) } { se@uint := 10 }
                    { sp@UintMap := path((ledger@@Ledger).balances) }
                    { storage := save(sp@UintMap[1], se@uint) }
                    { storage := clear((ledger@@Ledger)) }
                    { sp@UintMap := path((ledger@@Ledger).balances) }
                    { kept := sp@UintMap[1] }
                    { sp@UintMap := path((ledger@@Ledger).balances) }
                    { storage := clear(sp@UintMap[1]) }
                    { nonce := (ledger@@Ledger).nonce }
                    { sp@UintMap := path((ledger@@Ledger).balances) }
                    { gone := sp@UintMap[1] } (φ) } ] := by
  seq_steps [.storageFieldWriteSave, .storageIndexWriteUnfoldLeftFst,
             .localValueDeclInitDrop, .valueDeclSkip, .localValueAssign,
             .storagePlaceAlias, .storageIndexWriteMappingSave,
             .storageRootDelete, .storageIndexReadUnfoldRightFst,
             .storagePlaceAlias, .storageIndexReadMappingFind,
             .storageIndexDeleteUnfoldLeftFst, .storagePlaceAlias,
             .storageIndexDelete, .storageFieldReadFind,
             .storageIndexReadUnfoldRightFst, .storagePlaceAlias,
             .storageIndexReadMappingFind]

/-! ## 4 · Compound assignment -/

/-- `alice.age += 1;` -- one write-back, and the vacuous `¬⊤` branch KeY's
divisor guard leaves, once per mode. -/
theorem fieldCompoundAssign :
    [ seq!{ => <[ alice.age += 1 ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { alice.age += 1 } (φ) },
            seq!{ ¬⊤ => ⊤ },
            seq!{ ¬⊤ => ⊥ } ] := by
  seq_steps [(.storageFieldOpAssign .add), .revertBox]

end

end Solidity.Examples
