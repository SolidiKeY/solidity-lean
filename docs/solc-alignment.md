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
| Narrow integers | `uint8` … `uint248`, `int8` … `int248`: an operation at a narrow type reverts outside its range, `unchecked` and `<<` wrap modulo `2^N`, an implicit narrowing is refused, a `uint` cast truncates (below) | `narrowTy?`, `narrowPost`, `narrowCapture`, `narrowWrapNode`, `castCapture` (`Syntax.lean`) | `Examples/Tactics/Checked.lean` |
| Division | `/` and `%` by zero revert (KeY agrees) | `applyBinOp` | |
| `assert` | a failing `assert` panics (`Panic(0x01)`), a halt distinct from `require`'s revert that neither modality accepts; KeY's "Violated" goal, an obligation under the box too | `assertOk`, `Modality.afterRun`, `Taclet.assertSimple` | `Examples/Tactics/Revert.lean` |
| Assignment order | right-hand side first, target resolved once | `Stmt.run` (`.assign`, `.opAssign`, `.incDec`) | `Semantics.lean` examples |
| Effects in an expression | captured before the statement in solc's order (table below) | `hoist`, `captureExpr` | `Semantics.lean` examples |
| Mapping-carrying copy | a storage copy of a type containing a mapping cannot be written | `Src.copy` (`mapFree`), `tyHasMapping` | |
| Arrays past their end | `pop`, `delete`, `push` and copies keep the slots past the length; an index is checked when the path is taken | `SVal.array`, `State.checkIndex`, `SVal.overlay` | `testDanglingReferenceSurvivesPush` and three more |
| Fixed-size arrays | `delete` resets in place, the length is the literal `n`, a literal index `≥ n` is a compile error | `SVal.array … fixed`, `MObj.array` | |
| `transfer` | books `net(a) - v` unless `a` is the contract itself, and nothing else; whether the world pays is the EVM's (a refused payment reverts the machine alone) | `transferAt`; `Evm.compile_correct` | `Semantics.lean` |
| `send` | `ok = a.send(v);` books as `transfer` does and sets `ok` true, or books nothing and sets `ok` false, never reverting; which, the transaction's oracle says | `sendAt`, `TxEnv.ext` | `Examples/Tactics/Net.lean` |
| Call arguments | all read, left to right, before the callee runs | `Arg.bindSeq`, `Arg.separatedFrom` | |
| `call{value:}` | `(bool ok, ) = a.call{value: v}("")` is imported as `bool ok = a.send(v)`, as solkey's `SolJSONParser.isValueCall` reads it; solc forwards all gas there, so the callee can re-enter and write storage, which `holds` ignores (the no-callback reading) and only `holdsC` covers (`Semantics/Callback.lean`). `send` and `transfer` forward the 2300-gas stipend, under which the no-callback reading is the EVM's | `Frontend/SolcJson.lean` (`valueCall?`) | |
| `try` | a call to an address with no code, and returned data that does not decode, revert in the caller and no `catch` catches them; KeY leaves both out (they are vacuous in its box rule) | `Stmt.run` (`.tryCall`), `bindData` | `Examples/Tactics/TryCatch.lean` |

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

## Narrow integer types

solc gives each operation the type of its operands (the wider, a literal
taking the other's; `a ** b`, `a << b`, `a >> b` the base's) and checks it
there: `uint8 a = 200; uint c = a + a;` reverts although `c` is a `uint256`.
The model keeps `PrimTy` at `bool | uint | int`, 256 bits, and carries the
width in the elaborator: a local, a parameter, a return variable or a state
variable declared at `uintN`/`intN` is a `uint`/`int` of `N` bits
(`LocalTy.val`, `FunDecl.widths`, `Contract.widths`), and every other value is
256 bits wide (`intTyOf`).  So nothing below the elaborator changed: the
interpreter, the calculus, the soundness proofs and the compiler see ordinary
programs, and the check is a statement the rules already run.

- **An operation that can leave its type** (`+ - * **`, `/` and unary `-` at
  `int`, `++`/`−−`, `op=`) is followed by `require` of
  `inTy(T, e)` on where its result lands: `x += 10;` at `uint8` is
  `x += 10; require(x <= 255);`, `y -= 50;` at `int8` is
  `y -= 50; require((-128 <= y) && (y <= 127));` (`narrowPost`).  The check
  follows the write, where solc's precedes it; a revert discards the write,
  so the runs agree.  At `uint` only the upper bound is written: the 256-bit
  check has reverted below `0`.  An operation inside an expression (an
  operand, a condition, an index, an argument) is captured with its check
  before the statement, as an `++` is (`narrowCapture`): the capture can
  only revert, so moving it changes no effect's order.
- **Implicit conversions** are solc's: a value may be written where a type at
  least as wide is expected, and a literal where it fits; `uint8 x = total;`
  and `uint8 x = 300;` are elaboration errors (`fitCheck`), as they are
  compile errors.  So a narrow variable only ever holds a value of its range.
- **Casts.**  `uintN(e)` of a `uint` keeps the low `N` bits (`e % 2^N`), a
  widening cast keeps the value; either is a capture at its type, so the
  operations after it are checked at the cast's width (`castCapture`).
- **`unchecked`** wraps `+ - * **` and `<<` modulo `2^N` (`(x +% 1) % 256`),
  and `~x` at `uint8` is `255 -% x` (`narrowWrapNode`).
- **Storage packing** is not observable here: a state variable is a value of
  its own in the interpreter and a slot of its own in the compiler, and it
  holds a value of its range; solc packs several narrow variables into one
  slot, which only an `sload` or inline assembly would see.
- **Comparisons** compare the values, which solc's conversion to the common
  type preserves: nothing to check.

What is not modelled, each an elaboration error unless said otherwise:

- a narrow type inside a type: an array's element, a mapping's key or value,
  a struct's member (`narrowNestedMsg`); and a modifier's narrow parameter;
- a cast between `uint` and `int`, and one narrowing an `int`;
- signed arithmetic in `unchecked` (as at `int256`: `+%` takes `uint` only);
  `-128 / -1` and `-(-128)` at `int8` revert inside `unchecked` too, where
  solc wraps them, as at `int256` already;
- a narrow operation under the right operand of `&&`/`||` or in a branch of
  `c ? a : b`: its capture would run where the program does not evaluate it;
- constant folding: arithmetic on literals alone written to a narrow variable
  (`uint8 z = 200 + 100;`), which solc refuses at compile time, is checked
  at run time instead and reverts;
- `type(uint8).max` and the other type members;
- a public function's ABI decoding, which reverts on an out-of-range
  argument: a specification's precondition (`Calculus/Spec.lean`) does not
  assume a narrow parameter's range, which is weaker, not unsound.

The printed program has `uint`/`int` where the source has `uint8`/`int8`
(`Stmt.declLocal` holds a `PrimTy`), and the checks are visible statements.

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
sending contract's balance does not cover the amount or the recipient
refuses it (its code reverts, or runs out of the 2300 gas). `transferAt`
does neither check: a negative amount is `.stuck` (unrepresentable in the
unsigned value field), and otherwise the payment is booked at the
recipient's end of the ledger, `net(addr) := net(addr) - amt`, unless the
recipient is the contract itself (`State.pay`; `this` is `address(this)`,
`TxEnv.selfAddress`), which books nothing, as solkey's
`\if(sadr = self) \then(net)` does; and nothing else. `State.selfBalance`
(`address(this).balance`) is the funds the transaction found, which a
`transfer` leaves; solkey's box rule books the debit unconditionally too
(`333cc7b353`), and the diamond has no rule here. The interpreter thus
assumes the world pays, and the compiler theorem says what that costs: in
code that pays, the machine may revert where the interpreter succeeds
(`Evm.compile_correct`'s third outcome), so what the interpreter proves
under the box holds of every run the machine completes (`Evm.compile_box`),
and there `net(a)` is what `a`'s account lost (`Evm.compile_net`), at every
address but the contract's own, whose entry stays `0`: without the `if` in
`State.pay`, a payment to itself would move that entry and the simulation
(`Evm.Sim.netSelf`) would fail.

The callback semantics (`Semantics/Callback.lean`) is a relation over this
one: after the debit `State.havoc` replaces storage, ledger and balance, so
the callee may move funds into or out of the contract.

## `send`

On the EVM `a.send(v)` is a value call with the 2300-gas stipend that returns
`false` instead of reverting when it fails (funds that do not cover `v`, a
recipient whose code reverts or runs out of gas). Treating it as a transfer
that always succeeds would prove `ok == true` after it, which is false on the
EVM. So the outcome is the transaction's, as a `try`'s is: `sendAt` looks the
call up in `TxEnv.ext` at `sendKey a v` (the address, empty calldata, the
amount as the one word). No entry, or `ok`, is a recipient that takes the
payment (an address with no code does): the payment is booked as `transfer`
books it (`State.pay`) and `ok` is `true`. Any other entry is a refusal: nothing
is booked and `ok` is `false`. A negative amount is `.stuck`, as for `transfer`.

The calculus reads none of the oracle: `sendNoCallbackBox` and
`sendNoCallbackDiamond` have a goal for each outcome, so a proof holds
whatever the table says, and the diamond's rule is sound (unlike a diamond
over `transfer`, a refusal is an outcome of the run, not a revert of the
machine). Two consequences of the table being fixed per transaction:

- two sends of one amount to one address read one entry, so a run where the
  first is taken and the second refused is not one `Stmt.run` makes. That
  costs completeness only: each send's rule still has both goals;
- the funds are not checked, as for `transfer`: a send refused for want of
  funds is one of the oracle's refusals, and a taken one is booked whatever
  `State.selfBalance` holds (which it does not debit).

A send is outside the compiled fragment (`Evm.wtStmt` has no case for it).
`(bool ok, ) = a.call{value: v}("")`, which solkey lowers to
`bool ok = a.send(v);` (its `SolJSONParser.isValueCall`), is not written in
`sol{}` on this branch: it needs tuple syntax. Under solc that call forwards
all the gas, so the callee may re-enter; the reading without callbacks
ignores that, as solkey's `noCallback` does.

## Calls

solc evaluates every argument of an internal call, left to right, before the
callee runs. `Stmt.run` binds them one after another (`Arg.bindSeq`), as
KeY's function-body expansion declares them. The two agree because a call is
*separated* (`Arg.separatedFrom`: no non-simple argument reads a parameter
bound before it) and the elaborator's parameters are fresh names. A callee's
locals are renamed fresh at each call, so they live in the caller's locals as
they would in a frame of their own.

### Returns and tuples

- **Return variables start at their type's default**, as solc zeroes them:
  `function zero() returns (uint r) {}` returns `0`
  (`Examples/Tactics/Calls.lean`, `namedReturnDefault`). KeyTaclets declares
  them with no value (`R ri;`), so solkey cannot prove it.
- **A discarded tuple component is evaluated** when it may revert or have an
  effect: `(uint x, ) = (1, arr[5]);` reverts, as in solc (pinned with `1 / total` in `Examples/Tactics/Calls.lean`). solkey's
  `ParserUtils.tupleAssignment` drops every component that is not a call.
- **A tuple assignment whose targets may alias is refused** (the same name
  twice, two targets that are not stack locals, a target that reads another),
  until the order of solc's writes is checked against KeY's left to right.

## Remaining deltas (documented, intentionally out of scope)

- **Error classification.** A failing `assert` (Panic 0x01) is `Halt.panic`,
  a halt of its own (the table above). Every other failure collapses into
  `Halt.revert` or `Halt.stuck`; solc distinguishes the other `Panic(uint256)`
  codes, `Error(string)` and empty revert data. Checked overflow (Panic
  0x11, at a narrow width too), an out-of-range index (0x32), an empty `pop`
  (0x31) and a zero divisor (0x12) are all `.revert`; "rejected at compile
  time" and "outside the fragment" are `.stuck`. The compiled code has no
  panic: there a failing `assert` reverts (`compile_correct`).
- **Fragment width.** Loops run (`Loop.run`, `docs/loops.md`) and are
  proved by unwinding to a bound or by an invariant, but the EVM compiler
  refuses them (`wtStmt`); `uintN`/`intN`
  for `N < 256` only as above, no `address`/`bytes`/`string`, no external calls beyond
  `transfer`, `send`, the `net` ledger and `try` (whose callee is not run), no gas. These constructs do not occur
  rather than silently diverge.
- **`transfer` assumes the world pays.** It never reverts for funds or a
  refusing recipient; the EVM may, which `Evm.compile_correct` states as the
  machine reverting alone (`docs/compiler-verification.md`).
- **`push` over a recycled slot.** `arr.push(v)` of a struct or array value
  lays it on fresh slots (`SVal.strip`), not over the recycled slot it lands
  on, so what a reference wrote into that slot's own arrays past their ends is
  dropped where solc keeps it. No test in the corpus reads it.
- **No bound on a dynamic array's length.** solc's `push` panics (0x41)
  on an array whose length is already `2^64` (`oldLen >= 2^64`), so a
  deployed contract holds lengths up to `2^64` and no longer; here `push`
  (`pushOn`) appends unchecked and `wt(storage)` (`storageWtB`) bounds
  words and keys, not lengths. The delta goes both ways for a diamond
  obligation. One that reads a length through checked arithmetic
  (`storagePushReadBack`: `values[values.length - 1]` after a `push`) is
  false in the model from a storage solc cannot reach, and stays underived
  (`divergent` in `tests/solkey/expected.tsv`).
  One that pushes with no bound on the length before it holds in the model
  where solc panics, from a length of exactly `2^64`:
  `storagePushLengthPositive`, `storagePopUnknownLength` and
  `arrayOfMappingsIndex` are derived (`TestSuite/Derived7.lean`,
  `TestSuite/Derived8.lean`) and true of solkey, whose `int` is unbounded,
  but not of solc from that storage (`docs/testsuite-proofs.md`). Closing
  it means a bound `≤ 2^64` on every length in `wt` and the 0x41 panic in
  `pushOn`, which would also make `storagePushReadBack` derivable.
