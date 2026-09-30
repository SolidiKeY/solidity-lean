# Aligning the executable semantics with solc

The interpreter (`Stmt.run`, `Solidity/Semantics.lean`) is a port of KeY's
state layer, and KeY's calculus is in several places more liberal than the
Solidity compiler it models. Where the two differ the interpreter follows
**solc** (the 0.8 line), and this document is the authority for where and
why. solkey `f2eb3d98eb` reads storage the same way in the array items
below. The EVM compiler's own deltas are in `docs/compiler-verification.md`;
the plan to test these claims against solc is `docs/solc-validation.md`.

## Where the interpreter follows solc, not KeY

| Topic | Behaviour | Lean anchor | Witness |
|---|---|---|---|
| Checked arithmetic | `uint` is `uint256`, `int` is `int256`; a result outside the range reverts (`Panic(0x11)`), at the result type of `+ - * **`, `++`/`−−`, and `op=` | `checkArith`, `evalBinop`, `OpLoc.store`, `OpLoc.bump` | `Evm/Examples.lean` (`**`) |
| Unary minus | checked at `int` only; solc rejects it on `uint` | `unopCheck` | |
| `**` | reverts on overflow (`2 ** 256`), `0 ** 0` is `1`, a negative exponent is `.stuck` | `applyBinOp` | `Evm/Examples.lean` |
| `unchecked { }`, shifts | `+ - * **` in `unchecked` wrap modulo `2^256` (`+%` …); `~`, `<<`, `>>` are solc's at `uint256` | `applyBinOp`, `RawExpr.uncheck` | |
| Division | `/` and `%` by zero revert (KeY agrees) | `applyBinOp` | |
| `assert` | a failing `assert` reverts like `require`; KeY's "violated" goal is an obligation instead, and the rule table follows the interpreter | `Taclet.assertSimple` | `Examples/Revert.lean` |
| Assignment order | right-hand side first, target resolved once | `Stmt.run` (`.assign`, `.opAssign`, `.incDec`) | `Semantics.lean` examples |
| Effects in an expression | captured before the statement in solc's order (table below) | `hoist`, `captureExpr` | `Semantics.lean` examples |
| Mapping-carrying copy | a storage copy of a type containing a mapping cannot be written | `Src.copy` (`mapFree`), `tyHasMapping` | |
| Arrays past their end | `pop`, `delete`, `push` and copies keep the slots past the length; an index is checked when the path is taken | `SVal.array`, `State.checkIndex`, `SVal.overlay` | `testDanglingReferenceSurvivesPush` and three more |
| Fixed-size arrays | `delete` resets in place, the length is the literal `n`, a literal index `≥ n` is a compile error | `SVal.array … fixed`, `MObj.array` | |
| `transfer` | reverts unless the contract's funds cover the amount, and debits them | `transferAt`, `State.selfBalance` | `Semantics.lean` |
| Call arguments | all read, left to right, before the callee runs | `Arg.bindSeq`, `Arg.separatedFrom` | |

## Evaluation order

solc compiles `lhs = rhs` by evaluating the right-hand side first, in both
the legacy and the via-IR pipeline, and resolves an increment, decrement or
compound-assignment target once. `Stmt.run` does the same: `.assign` and
`.opAssign` evaluate the source before resolving the target, and `.incDec`
reads and writes through one resolved location. KeY's calculus agrees only
where the right-hand side is complex (`a[++i] = ++i` leaves `a[2] == 1`);
solkey's rule for a simple right-hand side bound the index first, so
`a[i++] = i` proved `a[0] == 1` where solc writes `0`, until solkey fixed it
on 2026-09-09.

An effect inside an expression cannot occur in `Stmt.run`: a value has no
effects, and the elaborator captures each `++`/`−−` (and call) into a fresh
local before its statement (`hoist`, `Syntax.lean`). An operand solc reads
*before* the effect is captured first (`captureExpr`):

| Form | solc reads | Elaborated |
|---|---|---|
| `x = i++ + i` | the right operand first: `1 + 1` | `uint se1 = i; uint se2; se2 = i++; x = se2 + se1;` |
| `a[++i] = ++i` | the right-hand side, then the target: `a[2] = 1` | `se1 = ++i; se2 = ++i; a[se2] = se1;` |
| `matrix[k][k++] = 77` | the base, then the index: `matrix[0][0]` | `uint[] storage sp1 = matrix[k]; se2 = k++; sp1[se2] = 77;` |
| `matrix[i++].push(i)` | the receiver, then the argument | `se1 = i++; matrix[se1].push(i);` |
| `persons[i++].age += i` | the right-hand side, then the target | `uint se1 = i; se2 = i++; persons[se2].age += se1;` |

`Semantics.lean`'s examples pin three of them. An effect under the right
operand of `&&`/`||`, or in a branch of a conditional, would run where solc
does not run it, so it is an elaboration error.

**Binary operators follow the legacy pipeline.** solc's legacy generator
evaluates the right operand first (`ExpressionCompiler.cpp`); the IR generator
evaluates the left first, so `++a + a` at `a = 1` is `3` in legacy and `4`
via IR, and neither is guaranteed (`docs/ir-breaking-changes.rst` in solc).
A proof about `x = i++ + i` holds for the legacy pipeline only;
`docs/solc-validation.md` weighs the options.

### Known divergence: reference sources are not right-hand-side first

"Right-hand side first" holds for a primitive source. For a struct or array
source solc resolves the target slot first, then copies member by member,
reading the source at copy time. `Stmt.run` is uniformly value-first, so it
disagrees on that shape. Witness, run on a real EVM
as solkey's `TestSuite.storageIndexWriteRefSourceImpureIndex`:

```solidity
Person memory p;          // p.age == 0
persons.push();           // persons[0].age == 0
persons[p.age++] = p;
assert(persons[0].age == 1);   // holds on chain
```

The typed layer does not reproduce the divergence: the index effect is
captured first and the source as a *reference* (`Person memory mv1 = p; uint
se2; se2 = p.age++; persons[se2] = mv1;`), so its members are read at copy
time, after the increment, as solc reads them. What remains is only the
order of two failing reads (the source's and the target index's bounds
check), and both are `.revert`.

## Storage-to-storage copies of mapping-carrying types

solc ≥ 0.7 rejects an assignment that would copy a mapping (directly or
nested in a struct or array) into storage. `Src.copy` carries a `mapFree`
obligation, so the typed syntax cannot express it (solkey's
`ParserUtils.parseAssignmentMaybe`, at the type level); `tyHasMapping` guards
the storage-source read, which is `.stuck` on such a type, the image of
"rejected at compile time" and deliberately not `.revert`. `delete` keeps a
mapping member in place, as solc does, and memory types contain no mappings.

The Theory (solkey's storage term algebra) has both of solkey's writes: the
collapsing `save` (`Theory/Storage.lean`), and the non-collapsing `copyTo`
(`Theory/Copy.lean`), which keeps a mapping member of the old node
(`selectOnCopyMap`) though no program here writes such a copy. Its `delete`
keeps mapping members as the interpreter's does (`keepsOnDelete`,
`selectStDelNodeMap`), and `State.abs_delete` (`Theory/Bridge/Delete.lean`)
proves the two agree on every read.

## Arrays past their end

solc never shrinks an array's storage. `pop()` clears the last element and
decrements the length, `delete arr` clears every element and sets the length
to `0`, and the slots past the new length keep what the clearing left, which
is not always nothing: a mapping nested in an element lives at hashed slots
no clearing reaches, and a reference taken before the `pop` still points
there. `SVal.array elems shadow fixed` is that run: `elems` the live
elements, `shadow` the slots past the end.

- **A path is checked where the program takes it.** `State.checkIndex` bounds
  an index against the live length once, when the path is resolved
  (`Loc.resolve`, `PTerm.at`), for a read, a write and an alias bind
  (`uint[] storage p = arr[i];` reverts out of range, as solkey's
  `storageIndexReadArrayBindLocalRoot` guard and solc's `Panic(0x32)` say).
  `SVal.find`/`SVal.save` then address the slot, past the end included, so
  an alias used later is not checked again. An index into a word or a struct
  is `.stuck`.
- **A write through a reference to a popped element writes the slot.**
  `Token storage r = tokens[0]; tokens.pop(); r.value = 5;` writes the
  cleared slot, and a `push()` of a struct or array element takes that slot
  as it is (`storagePushLengthSaveReferenceElement`), so `tokens.push();
  tokens[0].value` reads `5` (`testDanglingReferenceSurvivesPush`). A `push()`
  of a primitive clears its slot first (`storagePushLengthSave`); a `pop()`
  clears the element into the shadow (`storagePopSave`), but keeps a mapping
  element as it is (`storagePopSaveMappingElement`).
- **`delete arr` keeps the elements' mapping entries.** `SVal.defaultOf`
  clears each live element in place (words to `0`, structs member by member,
  mappings kept) and moves it in front of the shadow, so `delete arr;
  arr.push();` sees a nested mapping's entries again, as solc and solkey's
  `selectStDelNodeIndexStruct` do
  (`testDeleteArrayDoesNotResetElementMappingMember`).
- **A copy into storage is a write over what is there** (`State.writeStorage`,
  `SVal.overlay`): a struct member by member, an array taking the source's
  length and elements, the old slots past the new length cleared up to the
  old length and left beyond it (`testArrayCopyClearsOldElements`,
  `testArrayCopyKeepsDestinationTail`).
- **A fixed-size array keeps its length.** `delete` of a `T[n]` resets its
  `n` elements in place, a copy takes the source's elements, and there is no
  `length` slot (solc lays the array out inline).

`Calculus/Decide.lean` reads the live storage only (`SVal.findLive`,
`SVal.saveLive`) and is bridged to the program's checked paths; an alias
through an index is outside its fragment once the storage was written after
the bind.

## `transfer`

On the EVM a value transfer fails, and with `transfer` reverts, when the
sending contract's balance does not cover the amount. `State.selfBalance`
holds the executing contract's funds, and `transferAt`: a negative amount is
`.stuck` (unrepresentable in the unsigned value field); `amt > selfBalance`
reverts; otherwise `selfBalance -= amt` and the ledger is debited,
`net(addr) := net(addr) - amt`. The example stores (`exampleStore`,
`testSuiteStore`) fund the contract with a large balance so the ported KeY
tests keep their meaning.

The callback semantics (`Semantics/Callback.lean`) is a relation over this
one: after the debit `State.havoc` replaces storage, ledger and balance, so
the callee may move funds into or out of the contract. solkey agrees since
`084de89677`/`333cc7b353`: its `transfer` taclets update `selfBalance`, and
the diamond rule owes `0 <= se & se <= selfBalance`, which is the revert
condition above.

## Calls

solc evaluates every argument of an internal call, left to right, before the
callee runs. `Stmt.run` binds them one after another (`Arg.bindSeq`), as
KeY's function-body expansion declares them. The two agree because a call is
*separated* (`Arg.separatedFrom`: no non-simple argument reads a parameter
bound before it) and the elaborator's parameters are fresh names. A callee's
locals are renamed fresh at each call, so they live in the caller's locals as
they would in a frame of their own.

## Remaining deltas (documented, intentionally out of scope)

- **Error classification.** All failures collapse into `Halt.revert` and
  `Halt.stuck`; solc distinguishes `Panic(uint256)` codes, `Error(string)`
  and empty revert data. Checked overflow (Panic 0x11), an out-of-range index
  (0x32), an empty `pop` (0x31), a zero divisor (0x12) and a failing `assert`
  (0x01) are all `.revert`; "rejected at compile time" and "outside the
  fragment" are `.stuck`.
- **Fragment width.** No loops (`docs/loops.md` plans them), no `uintN`/`intN`
  for `N < 256`, no `address`/`bytes`/`string`, no external calls beyond
  `transfer` and the `net` ledger, no gas. These constructs do not occur
  rather than silently diverge.
- **`transfer` assumes its recipient.** It never reverts and is never the
  contract itself (`docs/solc-validation.md`).
- **`push` over a recycled slot.** `arr.push(v)` of a struct or array value
  lays it on fresh slots (`SVal.strip`), not over the recycled slot it lands
  on, so what a reference wrote into that slot's own arrays past their ends is
  dropped where solc keeps it. No test in the corpus reads it.
