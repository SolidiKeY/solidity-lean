# Aligning the executable semantics with solc

The interpreter in `Solidity/Semantics.lean` started as a
Lean port of the KeY state layer, and KeY's calculus was in several places
more liberal than the Solidity compiler it models. This note records where
the executable semantics now follows **solc** (the reference compiler,
current 0.8 line) rather than the original KeY rules, what that means
operationally, and what is still a documented modeling delta rather than a
behavioral match.

Everything here is about the interpreter (`Stmt.run`, `Semantics.lean`).
The EVM compiler's own deltas are in `docs/compiler-verification.md`.

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
- compound assignment (`op=`), at the target's type (`OpLoc.store`,
  `Stmt.opAssign`).

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

The removed `Calculus/` module that validated rule shapes pinned the
interpreter to the KeY/solc order on the `a[++i] = ++i` witness
(`storageEvaluationOrder_interpreter_rhsFirst`); that regression test is not
yet ported to the typed layer.

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

The old untyped interpreter stored `0` instead (its refutation,
`Counterexamples/RefSourceOrder`, was removed with the untyped layer).  In the
typed syntax a value has no effects: `persons[p.age++] = p;` elaborates to
`Person memory mv1 = p; uint se2; se2 = p.age++; persons[se2] = mv1;` — the
source captured as a *reference* (an alias of the same object), so its
members are read at copy time, after the increment, as solc reads them.  The
run from `State.testSuiteStore` ends with `persons[0].age == 1`.

### `++`/`−−` inside an expression: captured in solc's order

An effect inside an expression is captured before its statement by the
elaborator (`hoist`, `Syntax.lean`), and an operand solc reads *before* the
effect is captured first (`captureExpr`):

| Form | solc reads | Elaborated |
|---|---|---|
| `x = i++ + i` | the right operand first: `1 + 1` | `uint se1 = i; uint se2; se2 = i++; x = se2 + se1;` |
| `a[++i] = ++i` | the right-hand side, then the target: `a[2] = 1` | `se1 = ++i; se2 = ++i; a[se2] = se1;` |
| `matrix[k][k++] = 77` | the base, then the index: `matrix[0][0]` | `uint[] storage sp1 = matrix[k]; se2 = k++; sp1[se2] = 77;` |
| `matrix[i++].push(i)` | the receiver, then the argument | `se1 = i++; matrix[se1].push(i);` |
| `persons[i++].age += i` | the right-hand side, then the target | `uint se1 = i; se2 = i++; persons[se2].age += se1;` |

`Semantics.lean`'s examples pin three of them; all of `TestSuite.sol`'s
evaluation-order functions run to their asserts.  An effect under the right
operand of `&&`/`||`, or in a branch of a conditional, would be evaluated
where solc does not evaluate it, so it is an elaboration error.

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

## Arrays past their end: `pop`, `push`, `delete`, copies

An array's storage is a run of slots, and solc never shrinks it: `pop()`
clears the last element and decrements the length, `delete arr` clears every
element and sets the length to `0`, and the slots past the new length keep
what the clearing left, which is not always nothing — a mapping nested in an
element lives at hashed slots no clearing reaches, and a reference taken
before the `pop` still points there. `SVal.array elems shadow` is that run:
`elems` the live elements, `shadow` the slots past the end. solkey
`f2eb3d98eb` reads storage the same way, and the three places where the
interpreter used to be stricter than both now follow them.

- **A path is checked where the program takes it.** `State.checkIndex`
  bounds an array index against the live length once, when the path is
  resolved (`Loc.resolve`, `PTerm.at`): for a read, a write, and an alias
  bind (`uint[] storage p = arr[i];` reverts out of range, as KeY's
  `storageIndexReadArrayBindLocalRoot` guard and solc's `Panic(0x32)` say).
  `SVal.find` and `SVal.save` then address the slot, past the end included,
  so an alias used later is not checked again. An index into a word or a
  struct is `.stuck`: no typed program has one.
- **A write through a reference to a popped element writes the slot.**
  `Token storage r = tokens[0]; tokens.pop(); r.value = 5;` writes the
  cleared slot past the end, and a `push()` of a struct or array element
  takes that slot as it is (`storagePushLengthSaveReferenceElement`), so
  `tokens.push(); tokens[0].value` reads `5`, as solc does
  (`testDanglingReferenceSurvivesPush`). A `push()` of a primitive element
  clears its slot first (`storagePushLengthSave`: `delAt(storage, at(n))`),
  and a `pop()` clears the element into the slots past the end
  (`storagePopSave`), where an element that is a mapping is kept as it is
  (`storagePopSaveMappingElement`; `delete` of a mapping changes nothing).
- **`delete arr` keeps the elements' mapping entries.** `SVal.defaultOf`
  clears each live element in place (`defaultOf` on it: words to `0`,
  structs member by member, mappings kept) and moves it past the end, ahead
  of the slots already there, so `delete arr; arr.push();` sees a nested
  mapping's entries again — solc, and solkey's `selectStDelNodeIndexStruct`,
  which reads an index of a deleted node below its old `size` as the element
  deleted and one past it as it was (`testDeleteArrayDoesNotResetElementMappingMember`).
  KeY used to read every index of a deleted node as `mtSt`; that was the old
  reading here too, and it no longer holds on either side.

A copy into storage (`alice = bob;`, `arr = m;`) is a write over what is
there (`State.writeStorage`, `SVal.overlay`): a struct member by member, an
array taking the source's length and elements, each laid over the slot it
lands on, the old slots past the new length cleared up to the old length and
left as they were beyond it — solc's copy, and solkey's
`selectOnSaveEmptyIndexStruct` (`testArrayCopyClearsOldElements`,
`testArrayCopyKeepsDestinationTail`). A mapping met on the way keeps its
entries (a copy is `mapFree`). One delta is left: `arr.push(v)` of a struct
or array value lays it on fresh slots (`SVal.strip`), not over the recycled
slot it lands on, so what a reference wrote into that slot's own arrays past
their ends is dropped where solc would keep it. No test in the corpus reads
it.

`Calculus/Decide.lean` reads the live storage only (`SVal.findLive`,
`SVal.saveLive`) and bridges the two: a path the program checked reads the
same either way, and an alias through an index is outside its fragment once
the storage has been written after the bind.

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
a large balance so the ported KeY tests keep their meaning. The old,
untyped layer's callback semantics — a `Semantics/Callback` module whose
havoc quantified over the balance like it did over storage and the ledger,
so the callback boxes stayed sound — is not in the typed layer: it has no
call statement at all yet (`docs/kernel-port.md`'s "Port later").

solkey has since adopted the same check: `084de89677` adds `selfBalance`
to the ledger update of every `transfer` taclet, and `333cc7b353` splits
each one into a box rule (the debit booked unconditionally — a reverting
run satisfies any box) and a diamond rule owing `0 <= se & se <=
selfBalance` as a "sufficient funds" goal. That is exactly the revert
condition above, so this item no longer diverges
(the `SolKey` reader’s `SolKey/Corresp/SolcDelta.lean` records the four rows as
resolved).

## Taclet updates, and where the rule table is stricter than the interpreter

Since `Calculus/Rules.lean` became a taclet table, each terminal rule *states* its KeY
update and guard rather than deferring the whole state change to
the interpreter. That makes a second class of divergence visible: not
"KeY vs solc" but "the taclet's guard vs the interpreter's fault order". The
updates themselves are evaluated with the interpreter's own readers
(`Term.eval`, `Update.lean`), so a divergence is a real disagreement, not a
re-definition; `Update/SolcDelta.lean` is the table and
`Calculus/SoundUpdate.lean` the theorems that a taclet's update has the
statement's effect.

The bounds on a storage-alias bind were one, an **interpreter** gap: KeY's
`storageIndexReadArrayBindLocalRoot` guards `uint[] storage p = arr[i];` with
`0 <= i & i < length(arr)`, and the interpreter used to bind without looking.
It checks there now (`State.checkIndex`, above), which is where solc's
`Panic(0x32)` is.

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
- **EVM layer.** The compiler had its own deltas (arithmetic `MAPSLOT` in
  place of Keccak slot derivation, no gas, relative forward jumps, unbounded
  stack); it was removed with the untyped syntax (`docs/compiler-verification.md`).
