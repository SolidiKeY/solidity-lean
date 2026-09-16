# Paper parity: the calculus's worked examples, one row each

The paper (`../Pre-licenciate-paper`) draws a symbolic execution for each of
its worked examples. `Solidity/Examples/Derivations/Paper/` writes the same
chains as `sol_derivation`s. This file is the map between them: **one row per
worked example**, naming either the theorem that *is* that example or the
reason there is none.

It exists so that "this example has no chain" is a claim in one place with an
argument attached, rather than a prose list in a module docstring that drifts
from the file below it. `./scripts/check-paper-parity.sh` fails when a row
names a theorem no source file declares.

## How to read a row

| Column | Meaning |
|---|---|
| Program | the paper's own listing, abbreviated to its first statement where the program is long |
| Chain | `` `name` `` — a `sol_derivation` or `sol_calculus` in `Examples/Derivations/Paper/`; `` `Module:name` `` — one elsewhere in `Examples/Derivations/`; `— …` — no chain, and why |

The scratch names differ from the paper's, because a fresh name would fall to
`SoliditySyntax.rootExpr`'s stack default and be read as a `uint`. The
translation, which is the same one the umbrella `Paper.lean` docstring states:

| Paper | Here |
|---|---|
| `pv` (frozen value operand) | `rv@uint` |
| `acc`, `aliceAcc`, `aliceTok`, `sp` (storage alias) | `sp@Account`, `sp@Token`, `sp@UintArray`, … |
| `carolAcc`, `carolValues` | `mv@Account`, `mv@UintArray` |
| `carolAlias`, `carolTokens`, `davidTokens` | `mv2@Person`, `mv2@TokenArray` |
| `carolToken`, `tok` | `mv3@Token` |
| `idx`, `idx1`, `idx2` | `idx@uint` |
| `bucket`, `ledger`, `tokens` (auxiliary globals) | `bucket@@TokenBucket`, `ledger@@Ledger`, `tokens@@TokenArray` |

## 1 · Storage fields and roots — `sections/storage-examples.tex`

| Program | Chain |
|---|---|
| `alice.age = ageVal;` | `fieldWriteSimple` |
| `Account storage acc = bob.account; alice.account = acc;` | `fieldWriteFromAlias` |
| `alice.account.balance = 10;` | `deepFieldWrite` |
| `v = alice.account.balance;` | `deepFieldRead` |
| `alice.account.token.value = 5;` | `deeperFieldWrite` |
| `uint v = total;` | `rootRead` |
| `alice = pVal;` | `rootWriteFromAlias` |
| `alice = bob;` | `rootWriteFromGlobal` |
| `Account storage acc = alice.account; acc = bob.account; acc.balance = 10;` | `localRebindThenWrite` |
| `account = bob.account;` | `globalRootCopy` |

## 2 · Storage arrays — `sections/storage-examples.tex`, `sections/storage-examples-arrays.tex`

| Program | Chain |
|---|---|
| `v = values[i];` (box) | `arrayIndexReadBox` |
| `v = values[i];` (diamond) | `arrayIndexReadDiamond` |
| `values[i] = 100;` | `arrayIndexWrite` |
| `v = balances[a];` | `mappingIndexRead` |
| `Token storage tokRef = bob.account.token; tokens[i] = tokRef;` | `arrayIndexWriteRefSource` |
| `alice.accounts[0] = 100;` | `nonsimplePathIndexWrite` |
| `alice.accounts[++i] = valueVal;` | `nonsimplePathIncIndexWrite` |
| `matrix[i++][i++] = 77;` | `receiverAndIndexSideEffects` |
| `values.push(42);` | `arrayPush` |
| `tokens.pop();` (box) | `arrayPopBox` |
| `tokens.pop();` (diamond) | `arrayPopDiamond` |
| `tokens.push(tokRef);` | `pushRefSource` |
| `alice.account.tokens.push(tok);` | `pushNonsimpleReceiver` |
| `tokens.push();` | `pushBare` |
| `bucket.tokens.push();` | `bucketPushBare` |
| `tokens.push().value = 11;` | `pushSlotWrite` |
| `tokens.push(); uint i = tokens.push().value;` | `pushThenPushSlotRead` |
| `values.push(); values.pop();` | `popAfterPush` |
| `age = 10; age++;` | `rootWriteThenIncrement` |
| `values.push(makeValue());` | — call-valued operand, below |
| `values.push() = makeValue();` | — call-valued operand, below |

`bucket.tokens.push();` is written `(bucket@@TokenBucket.tokens).push()`: `@@`
binds the whole path, and the parentheses are not decoration — `.push()` cannot
follow a field access in the surface grammar, so `(x@@T).tokens.push()` does
not parse. The ported corpus spells it the same way.

### The push/pop aliasing programs (`\label{sec:push-pop-example}`)

Three programs whose point is not the shape of an update but the value a later
read sees. They are checks, not chains: the accumulated update of a
five-statement program is not something to write out, and the claim is the
value anyway.

| Program | Chain |
|---|---|
| `tokens.push(); tokens[0].value = 7; tokens.pop(); uint r = tokens.push().value;` — `r == 0` | `pushPopSlotCleared` |
| `tokens.push(); Token storage tokRef = tokens[0]; tokens.pop(); tokRef.value = 7; uint r = tokens.push().value;` — `r == 7` | — the model does not agree, below |
| the same ending `tokens.push(); uint r = tokens[0].value;` — `r == 0` | — the model does not agree, below |

`pushPopSlotCleared` is in `Paper/Checks.lean`, run on `State.testSuiteStore`
(the store that has `tokens`) and in the **diamond**, so it also says the
program reaches the read without reverting. That is the first program, and it
holds exactly as the paper says.

The other two do not, and the disagreement is worth stating precisely, because
it is about the very thing the section exists to show — a write through a
storage alias to a slot `pop()` has hidden:

- **The interpreter refutes both, in both modalities.** For the alias program
  neither `r == 7` nor `r == 0` holds in the box, so the line is not vacuous:
  the program does not reach the read with either value. The likeliest reading
  is that `tokRef.value = 7` after the `pop()` is an out-of-bounds write the
  interpreter reverts on, where the paper's logic keeps recording a value for
  the removed slot. That is `docs/solc-alignment.md`'s kind of question.
- **The rule table does not discharge even the first.** A `sol_calculus` of
  the `r == 0` program at `testSuiteStore` runs to a closed frontier, and the
  frontier does not hold. So the calculus and the interpreter disagree here
  too, in the direction `docs/calculus-parity.md` tracks.

Neither is written as a passing theorem, because neither is one. Resolving it
is its own change: it needs a decision about whether a dangling reference to a
popped slot writes or reverts, and that decision belongs with the `pop`/`push`
rules, not with an example file.

## 3 · Delete — `sections/storage-examples-delete.tex`

| Program | Chain |
|---|---|
| `delete alice.account;` | `deleteField` |
| `alice.account.balance = 100; … delete alice.account; …` | `deleteAccountThenReadLeaves` |
| `ledger.nonce = 42; delete ledger; v = ledger.nonce;` | `deleteStructThenRead` |
| `ledger.nonce = 5; … delete ledger.balances[1]; …` | `deleteLedgerMappingSurvives` |
| `delete alice.account.tokens[++i]; len = alice.account.tokens.length;` | `deleteIncIndexThenLength` |

## 4 · Compound assignment — `sections/arithmetic.tex`

| Program | Chain |
|---|---|
| `alice.age += 1;` | `fieldCompoundAssign` |
| `uint8 x = 250; x += 10;` | — checked arithmetic, below |

## 5 · Memory — `sections/memory-examples.tex`

| Program | Chain |
|---|---|
| `Account memory carolAcc = carol.account; carolAcc.balance = 100;` | `memoryAliasWrite` |
| `carol.account = david.account;` | `memoryFieldCopy` |
| `carol.account.balance = 10;` | `memoryDeepFieldWrite` |
| `v = carol.account.balance;` | `memoryDeepFieldRead` |
| `Person memory carolAlias = carol;` | `memoryDeclAlias` |
| `Token memory t = carol.account.token;` | `memoryDeclDeepAlias` |
| `carolAcc = david.account;` | `memoryRootRebind` |
| `v = carol;` | `memoryRootRead` |
| `carol = david;` | `memoryRootAssign` |
| `carol.age = a + b;` | `memoryFieldWriteCapturedRhs` |
| `Person memory carol;` | — a worked-example root, below |
| `choosePersonMem().account = makeAccount();` | — call-valued operand, below |

## 6 · Memory delete — `sections/memory-examples-delete.tex`

| Program | Chain |
|---|---|
| `Person memory carolAlias = carol; carol.age = 33; delete carol; oldAge = …; newAge = …;` | `memoryDeleteRoot` |
| `Account memory carolAcc = carol.account; … delete carol.account; oldBal = …; newBal = …;` | `memoryDeleteField` |
| `delete carolValues[i];` | `memoryIndexDeletePrimitive` |
| `delete carolTokens[i];` | `memoryIndexDeleteReference` |
| `delete carol.account.tokens[i];` | `memoryIndexDeleteNonsimplePath` |

## 7 · Memory arrays and allocation — `sections/memory-examples-arrays.tex`

| Program | Chain |
|---|---|
| `UintArray memory mv;` | `memoryArrayAlloc` |
| `v = carolValues[i];` | `memoryArrayReadBox` |
| `carolValues[i] = 100;` | `memoryArrayWriteBox` |
| `v = carolValues[++i];` | `memoryArrayIncIndexRead` |
| `carolValues[++i] = val;` | `memoryArrayIncIndexWrite` |
| `carol.account.values[i] = 42;` | `memoryNestedArrayWrite` |
| `carolTokens[i] = david.account.token;` | `memoryArrayWriteRefSource` |
| `carol.account.token = davidTokens[i];` | `memoryFieldWriteFromArrayElem` |
| `Token memory tok = carol.account.tokens[i];` | `memoryDeclFromNestedArrayElem` |
| `Token memory tok = carolTokens[++i];` | `memoryDeclFromIncIndexElem` |
| `xs = new uint[](n);` | — `memoryArrayFreshAlloc` is merged into `memoryDeclFreshAlloc` in `Rules.lean`, which `memoryArrayAlloc` is the chain of. There is no second rule to draw. |
| `carolValues[i] = makeValue();`, `carolValues[++i] = makeValue();` | — call-valued operand, below |

## 8 · Cross-domain copies — `sections/storage-to-memory.tex`, `sections/memory-to-storage.tex`

| Program | Chain |
|---|---|
| `Token memory t = alice.account.token;` | `storageToMemoryNonsimplePath` |
| `alice.age = 25; Person memory carol = alice; v = carol.age;` | `storageToMemoryRootCopy` |
| `alice.account.balance = 10; Account memory acc = alice.account; v = acc.balance;` | `storageToMemoryMemberCopy` |
| `carol.age = 42; alice = carol; v = alice.age;` | `memoryToStorageRootCopy` |
| `carolAcc.balance = 50; alice.account = carolAcc; v = …;` | `memoryToStorageFromAlias` |
| `carol.account.balance = 50; alice.account = carol.account; v = …;` | `memoryToStorageFromMemberSource` |
| `carolToken.value = 99; alice.account.token = carolToken; v = …;` | `memoryToStorageNonsimplePath` |

## 9 · Payment — `sections/payment.tex`

| Program | Chain |
|---|---|
| `to.transfer(5);` (box) | `transferBox` |
| `to.transfer(5);` (diamond) | `transferDiamond` |
| `owner.transfer(5);` (box) | `transferStorageReceiverBox` |
| `owner.transfer(5);` (diamond) | `transferStorageReceiverDiamond` |
| `to.transfer(x + 2);` | `transferCapturedAmount` |
| an unfunded `to.transfer(5);` | — the same derivation, below |

## 10 · Require, assert and control flow — `sections/storage-rules.tex`

| Program | Chain |
|---|---|
| `require(ok);` | `requireSimple` |
| `assert(ok);` | `assertSimple` |
| `if (true) s0 else s1` | `ControlFlow:ifElseTrueThenWrite` |
| `if (false) s0 else s1` | `ControlFlow:ifElseFalseThenWrite` |
| `if (!true) s0 else s1` | `ControlFlow:ifElseNegatedThenWrite` |
| `if (ok) s0 else s1` | — `ifElseSplit` is a sequent rule, below |
| `revert();` | — two `example`s in `Examples/Derivations/ControlFlow.lean`, one per modality; they are single steps, not chains, so they have no name to cite |

## 11 · Not implemented — `sections/not-implemented.tex`

| Program | Where it lives |
|---|---|
| `m[i++] = i;` | `Counterexamples/EvaluationOrder.lean` — a refutation, which is what the paper calls it |
| `persons[p.age++] = p;` | `Counterexamples/RefSourceOrder.lean` |
| `uint8 x = 250; x += 10;` | checked arithmetic, below |

## Why an example has no chain

**Call-valued operands.** `Stmt.callStmt` has no surface syntax at all, so
`values.push(makeValue());`, `values.push() = makeValue();`,
`carolValues[i] = makeValue();`, `carolValues[++i] = makeValue();` and
`choosePersonMem().account = makeAccount();` cannot be written as programs
here. The *rules* exist — `functionCallArgCapture`, `functionBodyExpand` — and
`Examples/Taclets/FunctionCallOps.lean` drops to constructors to run them.
The notation is what is missing, and extending it is its own change.

**A declaration of one of the worked-example roots.** `Person memory carol;`
is not writable because `carol` is already a memory root in
`SoliditySyntax.rootExpr`, which is what every other memory chain reads it as,
so those chains start after the declaration. The declaration *rule* is not
missing: `memoryArrayAlloc` runs it on the scratch array and
`Examples/MemoryBasic.lean` runs it on a struct. What cannot be written is a
declaration of a *fresh* name, because `rootExpr` reads a name it does not
know as a stack `uint`.

**First-order side conditions.** `sizeNotNegative`, which the pop-after-push
example needs, adds `0 ≤ find(storage, sp·length)` to the antecedent rather
than rewriting a program, so it has no `RuleName`. Its content is
`WellFormedConsumers.lean`'s row for `pop`. `popAfterPush` therefore ends with
the empty-array branch still open in the diamond; the paper closes it with
this rule, and the difference is exactly the rule.

**Sequent rules with two goals.** The calculus's `ifElseSplit` is not a
`BlockStep` — it splits one sequent into two on a symbolic condition — so it
has no `RuleName` either; it is `JudgmentSplit.ite_split`. The four
condition-directed rewrites that *are* rules (`ifElseUnfold`, `ifElseTrue`,
`ifElseFalse`, `ifElseNegated`) have chains in
`Examples/Derivations/ControlFlow.lean`.

**The memory identity layer.** The calculus's `new(mem, r) →` freshness
prefix, `idC`/`add`, and the lazy `copySt`/`copyMem` views. The first two are
terms in `Theory/Memory.lean` and the freshness premise is *discharged* there
(`Update/Theory.lean`, `denoteMem_new`), but a rule's update is not written in
them: the cross-domain chains end at the `alloc`/`copyMem` element the Lean
rule states, one line before the calculus's. `copySt`/`copyMem` have no
term-level spelling at all.

**The unfunded transfer.** It is `to.transfer(5);` again, and what differs is
the *state*, not the derivation. The semantic layer covers it
(`Evm/Examples.lean`, `Examples/Taclets/NetOps.lean`).

**Checked arithmetic.** `uint8 x = 250; x += 10;` needs the range predicates
and the guarded `intRules` expansion, which this package does not model; the
paper lists it under "Not Implemented Yet" for the same reason.

## Where a chain is written long

Most chains elide the administrative steps into one `~*>`, because the rules
they hide are bookkeeping. Three do not, and the reason is the same in each:
the paper's argument *is* the intermediate line.

- `deeperFieldWrite` is written at the same length as `deepFieldWrite`, so
  that "one selector deeper costs nothing" can be read off the two chains
  being line-for-line the same.
- `fieldWriteFromAlias` shows the declaration dropping into an update on its
  own line, which is where one sees that `acc` binds a *path*.
- `memoryDeepFieldWrite` keeps the middle line its storage twin has, so the
  two can be read side by side and the only difference is the last element.

## The lines, run

`Paper/Checks.lean` is the semantic half: `Sequent.check` applies a line's
accumulated update, runs what is left of the program, and reads the
postcondition, so the *first* line of a chain and its *last* can be run
against each other on a concrete store. These are the only `native_decide` in
`Paper/`; the chains themselves are ordinary proofs.

Coverage is one check per section, not one per chain:

| Section | Check |
|---|---|
| 1 storage fields | `deepFieldWrite`, first line against last, and both hold |
| 2 storage arrays | `rootWriteThenIncrement`; a branching line on a store where `values` is empty |
| 3 delete | `deleteAccountThenReadLeaves`, first line against last |
| 2 storage arrays (push/pop) | `pushPopSlotCleared`, in the diamond on `testSuiteStore` |
| 5–7 memory | `memoryAliasWrite`; the freshly allocated array, whose in-bounds goal is vacuous |
| 8 cross-domain | `storageToMemoryRootCopy` |
| 9 payment | `transferBox`, first line against last |
