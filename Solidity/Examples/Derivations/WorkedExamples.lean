import Solidity.Examples.Common

namespace Solidity.Examples.Worked

open Rules StandardExample SoliditySyntax Solidity.Examples

set_option maxHeartbeats 8000000

/-! # The worked derivations

One `sol_derivation` (or `sol_runs`) per construct, grouped by family (the
banners below). Each chain starts at a Solidity program and ends at
`solbox!{}`, with every intermediate block spelled out.

**What the derivations assume.**

* *Identifiers come from the standard example.* Where a program needs a
  literal it writes one (`sol_expr` takes a `num`) and where it needs a
  schematic name it writes `ageVal` / `valueVal` / `v`. The auxiliary globals
  are `name@@Type` (`tokens@@TokenArray`, `ledger@@Ledger`, `account@@Account`)
  and the memory locals are the aliases `mv`/`mv2`/`mv3` at an explicit type
  (`mv@Account`, `mv@UintArray`, `mv2@Person`) — `mv` is the calculus's own
  spelling for a memory path alias, beside `sp`, `pv` and `idx`.
  `alice.accounts` and `carol.account.values` are auxiliary `uint[]` members,
  declared in `fieldTy`.

  **Do not give these names explicit `rootExpr`/`rootPlace` arms.** It is
  tempting — `AST.lean`'s note says an explicit arm keeps skip-condition
  goals reducible — but `rootExpr` is on the hot path of *every* `sol!`
  elaboration, and adding `"v" | "ageVal" | "valueVal"` to it made this file
  abort the Lean process (stack) rather than merely slow down. They resolve
  through the default arm, which is what this file needs.

* *Administrative runs are elided.* The calculus freezes a value operand into
  `rv` before capturing the target (`Counterexamples/ErrorOrder.lean` is why),
  which costs three administrative steps. Those are collapsed into a `⇝*`
  line rather than pinned one by one.

* *Every chain ends at the empty block.* The rewrite layer stops there; the
  accumulated update (`{acc := alice·account ‖ storage := save(…)} φ`) lives
  in `Wp/TerminalUpdate.lean`. `Update.lean` and `Update/Examples.lean` write
  that last line down for the headline example, with its merge into the
  parallel form.

* *Branching is by modality.* An array bounds check splits the rule rather
  than the sequent — `storageIndexReadArrayFindBox` vs `…ArrayFindDiamond` —
  so those programs appear twice, once per modality.

**The rule sequences are not written down.** `sol_runs` proves its theorem
with `steps!`, so a rule rename or a changed residual is a build failure here,
not 35 stale lists to re-derive. To see what fired, use
`set_option trace.solidity.steps true in …`, or write `steps?` for a pasteable
`steps [...]`.

Two kinds of derivation keep their rules on the page, because there the rule
name is the content rather than bookkeeping: the single-step examples whose
doc comment makes a point *about* which rule the dispatch picks, and the three
chains written out in full because the step-by-step shape is what they
illustrate.
-/

/-! ## 1 · Storage fields and roots -/

/-! ### `alice.age = ageVal;`
A single step, `storageFieldWriteSave`. -/

sol_derivation fieldWriteSimplePath :
    solbox!{ alice.age = ageVal }
  ⇝[.storageFieldWriteSave] solbox!{}

sol_runs fieldWriteFromAlias
  { Account storage acc = bob.account; alice.account = acc }

/-! ### `alice.account.balance = 10;`
The headline derivation: three rewrite rules, plus the `⇝*` freeze line.
Written out step by step because the shape is the point. -/

sol_derivation deepFieldWrite :
    solbox!{ alice.account.balance = 10 }
  ⇝[.storageFieldWriteUnfoldLeftFst]
    solbox!{ uint rv = 10;
             Account storage sp = alice.account;
             sp@Account.balance = rv }
  ⇝*
    solbox!{ Account storage sp = alice.account; sp@Account.balance = rv }
  ⇝[.storagePlaceAlias]
    solbox!{ sp@Account.balance = rv }
  ⇝[.storageFieldWriteSave]
    solbox!{}

/-! ### `v = alice.account.balance;`
The read twin of the write above. It needs no freeze, so the chain is
exactly three rules. -/

sol_derivation deepFieldRead :
    solbox!{ v = alice.account.balance }
  ⇝[.storageFieldReadUnfoldRightFst]
    solbox!{ Account storage sp = alice.account; v = sp@Account.balance }
  ⇝[.storagePlaceAlias]
    solbox!{ v = sp@Account.balance }
  ⇝[.storageFieldReadFind]
    solbox!{}

/-! ### `alice.account.token.value = 5;`
One selector deeper than the previous example and yet the *same* chain: the unfold rule hoists
the whole path prefix in one step, so depth costs nothing. The calculus takes
seven lines here because it unfolds one selector at a time. -/

sol_runs deeperFieldWrite { alice.account.token.value = 5 }

/-! ### `uint v = total;` — reading a storage root -/

sol_runs rootRead { uint v = total }

/-! ### `alice = pVal;` / `alice = bob;` — whole-struct write
The calculus cites `storageRootWriteStore`; the Lean dispatch picks
`storageRootWriteCopySource`, which is the same rule split by whether the
source is a reference (it is, here — both operands are `Person`s). -/

sol_derivation rootWriteFromGlobal :
    solbox!{ alice = bob } ⇝[.storageRootWriteCopySource] solbox!{}

sol_derivation rootWriteFromAlias :
    solbox!{ alice = pp } ⇝[.storageRootWriteCopySource] solbox!{}

/-! ### local storage rebinding versus global root copy
The calculus's point: the same syntactic form is a *rebind* for a local
reference and a deep *copy* for a global root. Both derivations below, and
they share no rule. -/

sol_runs localRebindThenWrite
  { Account storage acc = alice.account; acc = bob.account;
    acc.balance = 10 }

sol_derivation globalRootCopy :
    solbox!{ account@@Account = bob.account }
  ⇝[.storageFieldReadStoreRoot] solbox!{}

/-! ## 2 · Storage arrays -/

/-! ### index read and write on a storage array
The calculus shows the bounds check as two stacked sequents, one per branch,
and notes the branches close with `revertBox` / `revertDiamond`. The
calculus splits by *modality* instead, so the read is two derivations. -/

sol_derivation arrayIndexReadBox :
    solbox!{ v = values[i] } ⇝[.storageIndexReadArrayFindBox] solbox!{}

sol_derivation arrayIndexReadDiamond :
    soldiamond!{ v = values[i] }
  ⇝[.storageIndexReadArrayFindDiamond] soldiamond!{}

sol_derivation arrayIndexWrite :
    solbox!{ values[i] = 42 } ⇝[.storageIndexWriteArraySaveBox] solbox!{}

/-! `v = balances[a];` — a mapping selector generates no bounds branch. -/

sol_derivation mappingIndexRead :
    solbox!{ v = balances[i] }
  ⇝[.storageIndexReadMappingFind] solbox!{}

/-! `Token storage tokRef = bob.account.token; tokens[i] = tokRef;` -/

sol_runs arrayIndexWriteRefSource
  { Token storage tokRef = bob.account.token; (tokens@@TokenArray)[i] = tokRef }

/-! ### push and pop on a storage array -/

sol_derivation pushValue :
    solbox!{ values.push(7) } ⇝[.storagePushValueSave] solbox!{}

sol_derivation popArray :
    solbox!{ (tokens@@TokenArray).pop() } ⇝[.storagePopSaveBox] solbox!{}

/-! `tokens.push(); tokens[0].value = 7; tokens.pop();` — the calculus's
push/write/pop program. -/

sol_runs pushWritePop
  { (tokens@@TokenArray).push(); (tokens@@TokenArray)[i].value = 7;
    (tokens@@TokenArray).pop() }

/-! The same program with the element reached through a storage alias
bound *before* the `pop()` — the calculus's dangling-alias case. -/

sol_runs pushAliasPopWrite
  { (tokens@@TokenArray).push(); Token storage tokRef = (tokens@@TokenArray)[i];
    (tokens@@TokenArray).pop(); tokRef@Token.value = 7 }

/-! ### pop after push (`sec:pop-after-push`)
The smallest program whose *diamond* proof needs `sizeNotNegative`. The
rewrite layer is modality-uniform here; the first-order side condition the
calculus adds is a sequent-level rule with no `RuleName`. -/

sol_runs popAfterPush { values.push(); values.pop() }

/-! ### `alice.accounts[0] = 100;` — nonsimple path index write
The calculus's three named steps, written out. -/

sol_derivation nonsimplePathIndexWrite :
    solbox!{ alice.accounts[i] = 100 }
  ⇝[.storageIndexWriteUnfoldLeftFst]
    solbox!{ uint rv = 100;
             UintArray storage sp = alice.accounts;
             sp@UintArray[i] = rv }
  ⇝*
    solbox!{ UintArray storage sp = alice.accounts; sp@UintArray[i] = rv }
  ⇝[.storagePlaceAlias]
    solbox!{ sp@UintArray[i] = rv }
  ⇝[.storageIndexWriteArraySaveBox]
    solbox!{}

/-! ### `alice.accounts[++i] = valueVal;`
Nonsimple path *and* a side-effecting index. Note the order: the value is
frozen, then the path, then the index increment runs — the evaluation-order
fix of `Counterexamples/EvaluationOrder.lean`. -/

sol_runs nonsimplePathImpureIndexWrite { alice.accounts[++i] = valueVal }

/-! ### additional storage array cases -/

sol_runs pushRefSource
  { Token storage tokRef = bob.account.token;
    (tokens@@TokenArray).push(tokRef) }

sol_runs pushNonsimpleReceiver { alice.account.tokens.push(tokRef) }

sol_runs pushLhsForm
  { Token storage tokRef = bob.account.token;
    (tokens@@TokenArray).push() = tokRef }

/-! ### storage delete cases -/

sol_derivation deleteSimple :
    solbox!{ delete alice.account } ⇝[.storageDeleteSimpleTarget] solbox!{}

sol_runs deleteComplexIndex { delete alice.account.tokens[++i] }

/-! The calculus's struct-reset program: a `delete` on a struct keeps its
mapping members and resets the rest, so the read afterwards succeeds. -/

sol_runs deleteStructThenRead
  { (ledger@@Ledger).nonce = 42; delete (ledger@@Ledger);
    v = (ledger@@Ledger).nonce }

/-! ## 3 · Compound assignment -/

/-! ### `alice.age += 1;`
The calculus's `storageFieldOpAssign`; Lean spells the family
`storageFieldCompoundAssign`, indexed by the operator. -/

sol_derivation fieldCompoundAssign :
    solbox!{ alice.age += 1 }
  ⇝[.storageFieldCompoundAssign .add] solbox!{}

/-! ## 4 · Memory -/

/-! ### memory aliasing
`Person memory carol; Account memory carolAcc = carol.account;
carolAcc.balance = 100;` — `carol` is already a memory root here, so only
the alias declaration and the write remain. -/

sol_runs memoryAliasWrite
  { Account memory mv = carol.account; mv@Account.balance = 10 }

sol_runs memoryFieldCopy { carol.account = david.account }

/-! ### `carol.account.balance = 10;` — the memory twin of the storage case -/

sol_runs memoryDeepFieldWrite { carol.account.balance = 10 }

/-! ### `v = carol.account.balance;` — the memory twin of the storage read -/

sol_runs memoryDeepFieldRead { v = carol.account.balance }

/-! ### memory reference aliasing via declaration drop -/

sol_runs memoryDeclAlias { Person memory mv2 = carol }

/-! ### `Token memory t = carol.account.token;` -/

sol_runs memoryDeclDeepAlias { Token memory mv3 = carol.account.token }

/-! ### `v = carol;` — a memory root read binds an identity -/

sol_derivation memoryRootRead :
    solbox!{ mv2@Person = carol } ⇝[.memoryRootAlias] solbox!{}

sol_derivation memoryRootAssign :
    solbox!{ carol = david } ⇝[.memoryRootAlias] solbox!{}

/-! ### `carol.age = a + b;` — additional memory write cases -/

sol_runs memoryWriteComputedValue { carol.age = x + y }

/-! ### memory delete cases
The calculus's point: `delete carol` resets the *identity's* members, so an
alias taken beforehand observes the reset. -/

sol_runs memoryDeleteRoot
  { Person memory mv2 = carol; carol.age = 34; delete carol;
    v = mv2@Person.age }

sol_runs memoryDeleteField
  { Account memory mv = carol.account; mv@Account.balance = 34;
    delete carol.account; v = mv@Account.balance }

/-! ### index read and write on a memory array
No bounds branch in the calculus's memory-array read either way: memory
lengths are known, so the modality split is the only difference. -/

sol_derivation memoryArrayRead :
    solbox!{ v = mv@UintArray[i] }
  ⇝[.memoryIndexReadHeapBox] solbox!{}

sol_derivation memoryArrayWrite :
    solbox!{ mv@UintArray[i] = 42 }
  ⇝[.memoryIndexWriteStoreBox] solbox!{}

/-! ### additional memory array cases -/

sol_runs memoryArrayImpureIndexRead { v = mv@UintArray[++i] }

sol_runs memoryNestedArrayWrite { carol.account.values[i] = 42 }

/-! ## 5 · Cross-domain copies -/

/-! ### storage-to-memory copy
`alice.age = 25; Person memory carol = alice; v = carol.age;` — six upstream
lines, three rules here. This is the direction where Lean is *shorter*: the
calculus spells out the `readCopySt` resolution and the read-over-write that the
single terminal rule `memoryFieldReadHeap` already performs. -/

sol_runs storageToMemoryCopy
  { alice.age = 34; Person memory mv2 = alice; v = mv2@Person.age }

/-! ### storage-to-memory copy of a *member* -/

sol_runs storageToMemoryMemberCopy
  { alice.account.balance = 10; Account memory mv = alice.account;
    v = mv@Account.balance }

/-! ### `Token memory t = alice.account.token;` -/

sol_runs storageToMemoryNonsimplePath
  { Token memory mv3 = alice.account.token }

/-! ### memory-to-storage copy
`carol.age = 42; alice = carol; v = alice.age;` -/

sol_runs memoryToStorageRootCopy
  { carol.age = 34; alice = carol; v = alice.age }

/-! ### memory-to-storage copy from an alias -/

sol_runs memoryToStorageFromAlias
  { mv@Account.balance = 10; alice.account = mv@Account;
    v = alice.account.balance }

/-! ### memory-to-storage copy with a nonsimple source
`carol.account.balance = 50; alice.account = carol.account;
v = alice.account.balance;` — the calculus's longest derivation, which it
writes with `\rwStepStar` twice. Fourteen rules here. -/

sol_runs memoryToStorageNonsimpleSource
  { carol.account.balance = 10; alice.account = carol.account;
    v = alice.account.balance }

/-! ### memory-to-storage copy, both sides nonsimple
Twenty-one rules — the deepest example in the calculus. -/

sol_runs memoryToStorageBothNonsimple
  { carol.account.token.value = 5;
    alice.account.token = carol.account.token;
    v = alice.account.token.value }

/-! ## 6 · Payments -/

sol_derivation transferSimple :
    solbox!{ to.transfer(5) } ⇝[.transferNoCallback] solbox!{}

/-! ### `to.transfer(x + 2);` — the amount is captured first -/

sol_runs transferComputedAmount { to.transfer(x + 2) }

/-! ### `owner.transfer(5);`
The calculus cites `transfer_unfold_leftFstReceiver` because a storage root is
not a stack word. In Lean `owner` is an atom (`WrappedExpr.simple`), so the
receiver needs no capture and `transferNoCallback` fires directly — a
genuine difference in where the "simple operand" line is drawn. -/

sol_derivation transferStorageReceiver :
    solbox!{ owner.transfer(5) } ⇝[.transferNoCallback] solbox!{}

/-! ### an unfunded transfer
Not a rewrite example: the program is `to.transfer(5);` again, and what
differs is the
*state* — the balance check fails. It belongs to the semantic layer, and is
covered by `Evm/Examples.lean`'s insufficient-balance revert tests and by
`Examples/Taclets/NetOps.lean`. -/

/-! ## 7 · The constructs that have no `sol!` spelling

Four kinds of program cannot be written in the surface notation, and the
reason is informative in each case:

1. **Call-valued arguments** — `values.push(makeValue());`,
   `values.push() = makeValue();`,
   `choosePersonMem().account = makeAccount();`. `Stmt.callStmt` has
   no surface syntax at all (`Examples/Taclets/FunctionCallOps.lean` drops to
   constructors for the same reason), so a call in argument position cannot be
   written. The rules themselves exist (`functionCallArgCapture`,
   `functionBodyExpand`); it is the notation that is missing.
2. **Bare memory declarations** — `Person memory carol;` (`:2386`, `:2542`,
   `:2710`). `carol` is already a memory root in `SoliditySyntax.rootExpr`, so
   the Lean transcriptions start after the declaration. The rule
   (`memoryDeclFreshAlloc`) is exercised in `Examples/MemoryBasic.lean`.
3. **First-order side conditions** — `sizeNotNegative` (the
   `sec:pop-after-push` example). It is a sequent rule that adds
   `0 ≤ find(storage, sp·length)` to the antecedent, not a program rewrite, so
   it has no `RuleName`. Its content is `WellFormedConsumers.lean`'s row for
   `pop`.
4. **State-dependent examples** — `An Unfunded Transfer` is
   `to.transfer(5);` again; what differs is the balance, not the derivation.
   Semantic layer: `Evm/Examples.lean`, `Examples/Taclets/NetOps.lean`.

Everything else the calculus covers is above. -/

end Solidity.Examples.Worked
