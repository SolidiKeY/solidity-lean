# Aligning the executable semantics with solc

The interpreter in `Solidity/Semantics.lean` started as a
Lean port of the KeY state layer, and KeY's calculus was in several places
more liberal than the Solidity compiler it models. This note records where
the executable semantics now follows **solc** (the reference compiler,
current 0.8 line) rather than the original KeY rules, what that means
operationally, and what is still a documented modeling delta rather than a
behavioral match.

Everything here is about the *official* interpreter (`evalValue` /
`execStmt` / `execAssign`); the EVM layer's own deltas are documented in
`Evm/Machine.lean` and `docs/compiler-verification.md`.

## Checked arithmetic (solc ≥ 0.8)

`checkArith (ty : Ty) : Value -> Res Value` is applied to every arithmetic
result at the operation's result type:

- `uint` models `uint256`: results outside `[0, 2^256)` revert
  (`uintBound = 2^256`);
- `int` models `int256`: results outside `[-2^255, 2^255)` revert
  (`intBound = 2^255`);
- `bool`-typed results (comparisons, connectives) are unconstrained.

Application points:

- binary operators, at `BinOp.retTy` of the left operand's type
  (`evalValue`, `.mkBinop`);
- unary minus at `int` only — `-(-2^255)` overflows; solc rejects unary
  minus on unsigned operands at compile time, so `uint` negation stays
  out of the checked fragment (`.mkUnop`);
- `++`/`--`, at the target's type (`.mkIncDec`);
- compound assignment (`op=`), at the target's type (`execStmt`,
  `Stmt.compoundAssign`).

A failed check is `.error .revert`: the executable image of `Panic(0x11)`.
The semantics does not model Panic *codes* — all reverts collapse into the
single `Halt.revert` verdict (see "Remaining deltas").

Division and modulo by zero already reverted (KeY and solc agree); the
zero-divisor guard is unchanged.

## Assignment order and single l-value resolution

solc compiles `lhs = rhs` by evaluating the **right-hand side first**, in
both the legacy and the IR (via-IR) pipelines, and resolves an
increment/decrement/compound-assignment target exactly **once**. The KeY
rewrite calculus agreed only where the right-hand side is *complex* — the
`*ValueRhsCapture` rules hoist it in front of the target capture, which is
what `testStorageEvaluationOrder` exercises (`a[++i] = ++i` leaves
`a[2] == 1`). A right-hand side that is *already simple* was left unfrozen,
so `a[i++] = i` had the index captured first and KeY proved `a[0] == 1`
where solc writes `0`; that was fixed upstream on 2026-09-09 by binding the
right-hand side ahead of the index capture. The old interpreter, separately,
evaluated target-first and re-resolved l-values on write-back.

Now:

- `execAssignNested` (field/index/push targets) runs `rhsToSVal` /
  `rhsToMVal` **before** `resolveLoc` on the target, so index side
  effects interleave in solc's order;
- `.mkIncDec` resolves its target once with `resolveLoc`, reads through
  `readLoc`, writes through `writeLoc` — the old double resolution re-ran
  the target's index side effects on the write-back;
- `Stmt.compoundAssign` follows the same single-resolution read/write
  path, with `checkArith` at the target type.

`RuleValidation.lean`'s evaluation-order section
(`storageEvaluationOrder_interpreter_rhsFirst`) pins the interpreter to
the KeY/solc order on the `a[++i] = ++i` witness.

### Known divergence: reference (struct) sources are *not* right-hand-side-first

"Right-hand side first" holds for a **primitive** source only. When the
source is a struct or array, solc resolves the target slot first and then
copies member by member, reading the source at copy time — so an impure
index in the target has already run before anything is read. The
interpreter is uniformly value-first (`rhsToSVal` / `rhsToMVal` before
`resolveLoc`, above) and therefore disagrees on exactly that shape.

Witness, run on a real EVM as solkey's
`TestSuite.storageIndexWriteRefSourceImpureIndex`
(`SolidityRuntimeExecutionTest`):

```solidity
Person memory p;          // p.age == 0
persons.push();           // persons[0].age == 0
persons[p.age++] = p;
assert(persons[0].age == 1);   // holds on chain; KeY closes it
```

`Counterexamples/RefSourceOrder.lean` shows this interpreter storing `0`
instead. The calculus is right here and the interpreter is wrong; the
`hprim : rhs.ty.isPrimitive = true` hypothesis on the `*UnfoldLeft*`
soundness theorems (`RuleSoundness.lean`) is what keeps them from
asserting the interpreter's answer. **Open:** make `execAssignNested`
target-first when the source is reference-typed, then drop `hprim`.

## Storage-to-storage copies of mapping-carrying types

solc ≥ 0.7 rejects assignments that would copy a mapping (directly, or
nested inside a struct/array) into storage. The old interpreter happily
deep-copied mapping members on storage-to-storage struct assignment —
behavior no compiled contract can exhibit.

`tyHasMapping` (fuel-bounded through `structDef`) now guards the
storage-source read `rhsToSVal`: a storage-to-storage assignment whose
right-hand side's type contains a mapping is `.error .stuck` — the
executable image of "rejected at compile time", deliberately *not*
`.revert` (no compiled program reaches this state). `delete` is unchanged:
solc permits `delete` on structs with mapping members (mappings are left
in place), and the semantics keeps that mapping-preserving behavior.
Memory types cannot contain mappings, so `rhsToMVal` needs no guard.

The same fact is in the syntax. `TypedStmt.Assign.mk` carries a `mapFree`
obligation, so the typed AST cannot express the copy at all — solkey's
`ParserUtils.parseAssignmentMaybe` at the type level — and `stmtTypingOk`
states the predicate for the untyped `Stmt.assign` the calculus works on.
That is what lets `Theory/Storage.lean`, solkey's storage theory as a term
algebra, collapse the leaf of a write (`save(st, nil, v) ⇝ v`) instead of
carrying solkey's mapping-preserving one. Its `delete`, on the other hand,
resets mapping members: a `Seg` carries no `MapField` sort, so the
mapping-preserving `delete` below is the interpreter's alone.

`pop`/`push` keep it too, and that is what `SVal.array`'s second field is
for. `arr.pop()` implicitly `delete`s the removed element and `arr.push()`
lands on the same storage slot, so a mapping nested in a popped struct
element is visible again after the push — solc's behaviour, and solkey's
(`storagePopSave` and `storagePushLengthSave` both write
`save(delAt(storage, at(n)), size, n ± 1)`). `Semantics.pushSlot` is that
`delAt` read eagerly: the cleared slot stays addressable beyond the new
length and the next `push` recycles it.

- **`delete arr` on a whole array.** On the EVM the mapping entries nested
  in a deleted element live at hashed slots that no clearing reaches, so
  `delete arr; arr.push();` sees them again. Here `SVal.defaultOf` empties
  the array outright, which is **KeY's** reading
  (`selectStDelNodeIndexStruct` reads every index of a deleted node as
  `mtSt`) and not solc's. Matching solc means handing the cleared elements
  back as recycled slots, which takes the value out of
  `Reachability.SVal.canonical` — the shadow-free fragment `writeProg`
  builds — and so costs `WellFormedConsumers` row C6 its value-level
  proof. Recorded here rather than made silently; `pop`/`push` are not
  affected.

## `transfer` checks and debits the sender's balance

`a.transfer(v)` in the old semantics only booked `net(a) += v` — it could
not fail and moved no funds *out* of anything. On the EVM, a value
transfer fails (and with `transfer`, reverts) when the sending contract's
balance does not cover the amount.

`State` now carries `selfBalance : Int` (the executing contract's own
funds). `Stmt.transfer`:

- a negative amount is `.stuck` (unrepresentable in the EVM's unsigned
  value field — outside the fragment);
- `amt > selfBalance` reverts — the EVM balance check;
- otherwise `selfBalance -= amt` and the ledger is *debited*: `net(addr) := net(addr) - amt` (`State.setNet addr (getNet addr - amt)`; the module header of `Semantics.lean` states the same sign).

The example stores (`exampleStore`, `testSuiteStore`) fund the contract with
a large balance so the ported KeY tests keep their meaning;
`Semantics/Callback.lean`'s havoc quantifies over the balance like it does
over storage and the ledger, so the callback boxes remain sound.

solkey has since adopted the same check: `084de89677` adds `selfBalance`
to the ledger update of every `transfer` taclet, and `333cc7b353` splits
each one into a box rule (the debit booked unconditionally — a reverting
run satisfies any box) and a diamond rule owing `0 <= se & se <=
selfBalance` as a "sufficient funds" goal. That is exactly the revert
condition above, so this item no longer diverges
(the `SolKey` reader’s `SolKey/Corresp/SolcDelta.lean` records the four rows as
resolved).

## Taclet updates, and where the rule table is stricter than the interpreter

Since `Rules.lean` became a taclet table, each terminal rule *states* its KeY
update and guard rather than deferring the whole state change to
`Semantics.execStmt`. That makes a second class of divergence visible: not
"KeY vs solc" but "the taclet's guard vs the interpreter's fault order". The
updates themselves are evaluated with the interpreter's own readers
(`Update/Eval.lean`), so a divergence is a real disagreement, not a
re-definition; `Update/SolcDelta.lean` is the table and
`Update/TacletTable.lean` the theorems.

One of them is new, and it is an **interpreter** gap rather than a KeY one:

- **Bounds on a storage-alias bind.** KeY's `storageIndexReadArrayBindLocalRoot`
  guards `uint[] storage p = arr[i];` with `0 <= i & i < length(arr)` and
  reverts otherwise, exactly as it guards the value read. The interpreter does
  not: `Wp.storageAssignUpd`'s local-root arm resolves the right-hand side
  with `placePath`, which builds the path `arr[i]` without consulting the
  array's length, and binds it. solc agrees with KeY — an out-of-range index on
  a storage array is `Panic(0x32)` whether the result is read or aliased — so
  the Lean rule carries KeY's guard and `Update/TacletTable.lean` states that
  rule's bridge under it. Closing the gap means a bounds check in `placePath`'s
  index arm, which is a change to `Semantics.lean` and to every theorem about
  it, so it is recorded here rather than made silently.

Three older divergences are the same kind of thing seen from the rule side, and
were already known: checked arithmetic in `Sym.combined` (KeY's `+` is
unbounded, the interpreter's reverts on overflow), a mapping-carrying storage
copy (refused by `rhsSVal`, allowed by KeY's `find<[StValue]>`), and
`assertSimple`, where KeY's "Violated" goal is an *obligation* to prove the
condition and the interpreter simply reverts — so under the box modality the
rule is strictly stronger than the program it describes
(`assertSimple_box_gap`).

## Remaining deltas (documented, intentionally out of scope)

- **Error classification.** All failure modes collapse into
  `Halt.revert` / `Halt.stuck`; solc distinguishes `Panic(uint256)`
  codes, `Error(string)`, and empty revert data. The mapping is:
  checked-arithmetic overflow ≈ Panic 0x11, out-of-bounds index ≈ Panic
  0x32, empty `pop` ≈ Panic 0x31, zero divisor ≈ Panic 0x12, failing
  `assert` ≈ Panic 0x01 — all `.revert` here; "rejected at compile time"
  and "outside the fragment" are `.stuck`.
- **Fragment width.** No loops, no `uintN`/`intN` for `N < 256`, no
  `address`/`bytes`/`string` types, no external calls beyond `transfer`
  and the `net` ledger, no gas. Nothing in the fragment silently
  *diverges* from solc; these constructs simply do not occur.
- **`sol!` name typing.** The surface macro types bare local names by
  a name table that defaults to `uint`; an `int`-declared local read
  back in an expression is therefore *checked* at `uint`, so a
  negative intermediate reverts where solc would not (see the
  `exponentiationSignedBaseOddExponent` row of
  `tests/solkey/expected.tsv`). A macro-level typing environment would
  close this; it is a surface-syntax gap, not an interpreter one.
- **EVM layer.** `Evm/Machine.lean` documents its own deltas (arithmetic
  `MAPSLOT` in place of Keccak slot derivation, no gas, relative forward
  jumps, unbounded stack).
