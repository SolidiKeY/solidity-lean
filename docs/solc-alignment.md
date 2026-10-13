# Aligning the executable semantics with solc

The interpreter, the typed run (`Stmt.run`, `Solidity/Semantics/Run.lean`)
over the typed state (there is no untyped state since W10.5.6), is a port
of KeY's state layer, and KeY's calculus is in several places more liberal than the
Solidity compiler it models. Where the two differ the interpreter follows
**solc** (the 0.8 line), and this document is the authority for where and
why. solkey `f2eb3d98eb` reads storage the same way in the array items
below. The EVM compiler's own deltas are in `docs/compiler-verification.md`;
the plan to test these claims against solc is `docs/solc-validation.md`.

## Where the interpreter follows solc, not KeY

| Topic | Behaviour | Lean anchor | Witness |
|---|---|---|---|
| Checked arithmetic | `uint` is `uint256`, `int` is `int256`; a result outside the range reverts (`Panic(0x11)`), at the result type of `+ - * **`, `++`/`−−`, and `op=` | `PrimTy.ofInt?`, `BinOp.evalT`, `OpLoc.storeT`, `OpLoc.bumpT` | `Evm/Examples.lean` (`**`) |
| Unary minus | at `int` only, range-checked there: `-x` at `uint` is refused by the elaborator and the spec reader (`UnOp.accepts`, since 2026-10-07; before, it was accepted and its result left `uint`'s range), as solc refuses it | `UnOp.accepts`, `UnOp.evalT` | |
| `**` | reverts on overflow (`2 ** 256`), `0 ** 0` is `1`, a negative exponent reverts (since 2026-10-07; it was `.stuck`): solc's exponent is unsigned, so never negative on the EVM.  In the typed run a negative exponent is unrepresentable (`BinOp.accepts .pow` is `uint`, an operand a `PrimTy.uint.Denote`, the environment a `TTx` of `uint`s); the revert survives in `BinOp.arithInt` | `BinOp.arithInt` | `Evm/Examples.lean` |
| Literals | a literal is in its type's range, `uint` below `2^256`, `int` in `[-2^255, 2^255)` (since 2026-10-07): one out of it is solc's compile error, and here no term (`Simple.lit` carries `PrimTy.inRange`); the elaborator refuses it (`litAt`), and the EVM fragment no longer checks it.  In a constant expression solc folds the literals exactly first: `2**256 - 1` written out as one literal minus `1` is the literal `2^256 - 1`, and so here (`check` folds `+ - *` and an exact `/` of two literals, `BinOp.foldLit?`; a result out of range is still refused) | `Simple.lit`, `PrimTy.inRange`, `litAt`, `BinOp.foldLit?` | `Typing/Constructibility.lean` (`SVal.fits`) |
| Mappings in memory | a memory local, a memory declaration and a memory path are at a type with no mapping (since 2026-10-07; solc rejects one): `MPath.var` and `declMem` carry `(Ty.ref R).mapFree`, and a member or element of a memory path inherits it (`MPath.mapFree`).  The typed heap holds no mapping object (`MObj`, `Semantics/Heap.lean`), so the run never allocates one, and the typed copies (`Heap.allocDefault`, `SVal.copyStToM`) take a `mapFree` type | `MPath.var`, `Stmt.declMem`, `memOk` | |
| `bool` mapping keys | a `mapping(bool => V)` keeps two slots, at `0` and `1`: solc hashes a key padded to a word (`keccak256(h(k) . p)`), and a `bool` pads to `0`/`1` (decisions 10 and 14, `docs/intrinsic.md`).  The typed run hashes an index at its key type (`PrimTy.key`, `SRef.atKey`: a `bool` as `0`/`1`, a number as itself), and a rule's term writes the hash: `m[b]` lowers to `at(m, b ? 1 : 0)` (`Tm.keyAt`, `Simple.keyLower`), as the solc frontend writes it (`Frontend/SolcJson.lean`, `boolKey`).  So `at` itself still reads a number, and the closer tells two numeric keys apart by their values.  The solkey corpus's `boolKeyed` store is still unported | `PrimTy.key`, `Tm.keyAt`, `Simple.keyLower` | `Typing/Constructibility.lean` (`bool_key_reachable`) |
| Storage pointer without a target | `T storage p;` binds `p` to no path (since 2026-10-07; it bound nothing, so a loop's next iteration saw the last one's binding and a read was `.stuck`): a read or a write through `p` reverts.  solc rejects such a read statically; KeY's `storageLocalDeclSkip` binds nothing (`docs/lean-key-rule-map.md`) | `SPath.resolveT` (`.alias` at `none`), `Rhs.unset` | `Examples/Tactics/StorageSuite.lean` (`unsetAliasWrite`, `unsetAliasRead`, `unsetAliasLoop`) |
| Memory local without an object | a memory local may be unset (decision 17', `docs/intrinsic.md`, since 2026-10-08): no statement leaves one so (`T memory m;` allocates a default object, as solc's zero-initialised memory does, and every other declaration binds an object), but the calculus's hidden binder ranges over it, as over an unset alias (above).  A read or a write through an unset memory local reverts, in the typed run (`MPath.mvalT`) and in the terms the calculus reads (`State.memRefT`, `Calculus/Lands.lean`; on the untyped state it was `Binding.unset` read as memory, `.stuck`).  solc has no such local | `LTy.TDenote`, `State.memRefT`, `MPath.mvalT`, `bindingRef` | `Calculus/Sound.lean` (`Stmt.sound`) |
| Block-scoped locals | in the type (since 2026-10-07, M2.2; since W8 the elaborator emits the scoped `Stmt C Γ Γ'` directly, so a local out of scope does not elaborate): the elaborator (`NCtx.find`, `elabProgS`) reads the branches of an `if` and a `try`, a loop's body and a call's body as scopes and a name as its newest declaration, so `{ bool x = true; } if (c) { uint x = 1; }` is accepted, as solc accepts it, and a branch's local is not read after it.  The run (`Stmt.run`, `TRun.ite`/`TRun.block`, `docs/intrinsic.md`) pops a scope's locals at its end, and the typing invariants are carried along it (`Typing/TypedRunInv.lean`); since W4 it is the only run of a statement, and the calculus reads it, so no local outlives its scope | `NCtx.find` (`Syntax/Elab.lean`), `elabProgS` (`Syntax/Splice.lean`), `TRun.ite`, `TRun.block` | `Examples/Tactics/Branch.lean`, `Syntax/Splice.lean` |
| Conditional of memory references | `T memory m = c ? a : b;` binds `m` to `a`'s or `b`'s object, as solc: the elaborator declares a fresh `mv` before the branches, bound to a branch that indexes nothing (a read that cannot revert on a set local), and rebinds it in each branch.  An unset memory local, which only a hidden binder holds (decision 17' of `docs/intrinsic.md`), reverts on that read where solc reads only the branch taken: when the index-free branch is such a local and is not taken, the program reverts where solc's does not (since W8).  When both branches index, `mv` is first bound to a fresh default object (`T memory mv;`), which nothing reaches: the heap has one object solc does not allocate (since 2026-10-07).  So when both branches index and `T`'s default is not well-formed (`defaultOkS`), the conditional is refused ("a conditional of two indexed memory …s, whose default is not well-formed"), where before 2026-10-07 each branch declared `mv` itself | `hoist`, `MPath.indexFree` | `Syntax/Splice.lean`, `Examples/Tactics/Branch.lean` |
| `unchecked { }`, shifts | `+ - * **` in `unchecked` wrap modulo `2^256` (`+%` …); `~`, `<<`, `>>` are solc's at `uint256` | `BinOp.arithInt`, `RawExpr.uncheck` | |
| Narrow integers | `uint8` … `uint248`, `int8` … `int248`: an operation at a narrow type reverts outside its range, `unchecked` and `<<` wrap modulo `2^N`, an implicit narrowing is refused, a `uint` cast truncates (below) | `narrowTy?` (`Syntax.lean`), `narrowPost`, `narrowCapture`, `narrowWrapNode`, `castCapture` (`Syntax/Elab.lean`) | `Examples/Tactics/Checked.lean` |
| Division | `/` and `%` by zero revert (KeY agrees) | `BinOp.arithInt` | |
| `assert` | a failing `assert` panics (`Panic(0x01)`), a halt distinct from `require`'s revert that neither modality accepts; KeY's "Violated" goal, an obligation under the box too | `TRun.assert`, `Modality.afterRunTR`, `Taclet.assertSimple` | `Examples/Tactics/Revert.lean` |
| Assignment order | right-hand side first, target resolved once | `Stmt.run` (`TRun.assign`, `TRun.opAssign`, `TRun.incDec`) | `Examples/Tools.lean` (`Prog.runT`) |
| Effects in an expression | captured before the statement in solc's order (table below) | `hoist`, `captureExpr` | `Examples/Tools.lean` (`Prog.runT`) |
| Repeated member names | a struct that declares two members of one name is refused ("Identifier already declared"): the elaborator refuses a type naming one (`refusedStructs`, `unknownStructMsg`, decision 16), so every struct of `structDef` has distinct member names and the typed (positional) and untyped (by name) copies agree | `structDef_nodup`, `SVal.overlay_erase` | `Syntax/Splice.lean` (`BadDup`) |
| Mapping-carrying copy | a storage copy of a type containing a mapping cannot be written | `Src.copy` (`mapFree`), `tyHasMapping` | |
| Arrays past their end | `pop`, `delete`, `push` and copies keep the slots past the length; an index is checked when the path is taken | `SVal.array`, `checkIndex`, `SVal.overlay` | `testDanglingReferenceSurvivesPush` and three more |
| Array lengths | a dynamic array holds fewer than `2^256` elements: its length is a `uint` (decision 13, `docs/intrinsic.md`).  The typed storage and heap carry the bound (`SVal.array`, `MObj`), so a typed length read is in range (`Storage.len`, `Heap.lenU`).  A push onto `2^256 - 1` elements exhausts the resources: the typed run halts with `exhausted` there (`Storage.full`, `TRun.push`; decision 15), and both modalities accept it (`Modality.onTHalt`), as KeY, which models no gas, reads every run (solkey's arrays are unbounded, so its diamond obligations with a push stay provable).  solc panics (`0x41`) on a storage array past `2^64` elements and its code runs out of gas long before; Lean's bound is `2^256`, and an exhausted run proves any modality.  A push below the bound ends (`Semantics/Ends.lean`).  Decision 13 said the push reverts: a typed revert needs the untyped push to revert too, and the untyped calculus's diamond obligations with a push (most of solkey's TestSuite is diamonds) could then not be discharged, since a storage with `2^256 - 1` elements is reachable | `SVal.array`, `MObj`, `Storage.full`, `lenU` | `Semantics/Ends.lean` |
| Fixed-size arrays | `delete` resets in place, the length is the literal `n`, a literal index `≥ n` is a compile error | `SVal.array … fixed`, `MObj.array` | |
| `transfer` | books `net(a) - v` unless `a` is the contract itself, and nothing else; whether the world pays is the EVM's (a refused payment reverts the machine alone) | `TRun.transfer`; `Evm.compile_correct` | `Semantics/Run.lean` |
| `send` | `ok = a.send(v);` books as `transfer` does and sets `ok` true, or books nothing and sets `ok` false, never reverting; which, the transaction's oracle says | `sendT`, `TxEnv.ext` | `Examples/Tactics/Net.lean` |
| Call arguments | all read, left to right, before the callee runs | `Args.evalT`, `CallRet.enterT` (`Semantics/Run.lean`) | |
| `call{value:}` | `(bool ok, ) = a.call{value: v}("")` is imported as `bool ok = a.send(v)`, as solkey's `SolJSONParser.isValueCall` reads it; solc forwards all gas there, so the callee can re-enter and write storage, which `holds` ignores (the no-callback reading) and only `holdsC` covers (`Semantics/Callback.lean`). `send` and `transfer` forward the 2300-gas stipend, under which the no-callback reading is the EVM's | `Frontend/SolcJson.lean` (`valueCall?`) | |
| `try` | a call to an address with no code, and returned data that does not decode, revert in the caller and no `catch` catches them; KeY leaves both out (they are vacuous in its box rule) | `Stmt.run` (`.tryCall`), `Binders.decodeT` | `Examples/Tactics/TryCatch.lean` |

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
local before its statement (`hoist`, `Syntax/Elab.lean`). An operand solc reads
*before* the effect is captured first (`captureExpr`):

| Form | solc reads | Elaborated |
|---|---|---|
| `x = i++ + i` | the right operand first: `1 + 1` | `uint se1 = i; uint se2; se2 = i++; x = se2 + se1;` |
| `a[++i] = ++i` | the right-hand side, then the target: `a[2] = 1` | `se1 = ++i; se2 = ++i; a[se2] = se1;` |
| `matrix[k][k++] = 77` | the base, then the index: `matrix[0][0]` | `uint[] storage sp1 = matrix[k]; se2 = k++; sp1[se2] = 77;` |
| `matrix[i++].push(i)` | the receiver, then the argument | `se1 = i++; matrix[se1].push(i);` |
| `persons[i++].age += i` | the right-hand side, then the target | `uint se1 = i; se2 = i++; persons[se2].age += se1;` |

A callee's parameters and locals, inlined under fresh names, are captured as
a caller's are: `return a++ + a;` reads the right `a` first
(`ElabScope.inlined`; before 2026-10-08 a fresh name was taken for a capture
holding its value, and `bumpRead(1)` of `Tactics/Calls.lean` was `1 + 2`).
A program's own fresh-shaped local (`se1`, `sp1`, `ie1`, `mv1`, `brk1`, …,
as `FreshNames.parse` reads it) is still taken for a written-out capture and
is not captured again: `uint se1 = 0; y = se1++ + se1;` reads the right
`se1` after the `++` (`1`, where solc gives `0`), by the convention of
written lines (proposed decision 30 of `docs/intrinsic.md`).

`Examples/Tools.lean` pins three of them (a block run typed,
`Prog.runT`, `Tools/Run.lean`). An effect under the right
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
  argument: a specification's precondition (`Calculus/SurfaceSpec.lean`) does not
  assume a narrow parameter's range, which is weaker, not unsound.

The printed program has `uint`/`int` where the source has `uint8`/`int8`
(`Stmt.declLocal` holds a `PrimTy`), and the checks are visible statements.

## Storage-to-storage copies of mapping-carrying types

solc ≥ 0.7 rejects an assignment that would copy a mapping (directly or
nested in a struct or array) into storage. `Src.copy` carries a `mapFree`
obligation, so the typed syntax cannot express it (solkey's
`ParserUtils.parseAssignmentMaybe`, at the type level); `tyHasMapping` guards
the storage-source read, which is `.undef` on such a type, the image of
"rejected at compile time" and deliberately not `.revert`. `delete` keeps a
mapping member in place, as solc does, and memory types contain no mappings.

The typed Theory (`Theory/Typed/Obs.lean`, what an equation reads) has
solkey's copying write `copyTo`, which keeps a mapping member of the old node
(`TVal.overlay`) though no program here writes such a copy, and its `delete`
keeps mapping entries and an array's slots past its end as the interpreter's
does (`TVal.delR`, read off the type); `Storage.obs_delete` and
`Storage.obs_write` prove the two agree on every read, literally.  The
untyped algebra that kept both of solkey's writes, the collapsing `save` and
the non-collapsing `copyTo`, was deleted at W10.4.

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
  (`Loc.resolveT`, `PTerm.at`), for a read, a write and an alias bind
  (`uint[] storage p = arr[i];` reverts out of range, as solkey's
  `storageIndexReadArrayBindLocalRoot` guard and solc's `Panic(0x32)` say).
  `SVal.find`/`SVal.save` then address the slot, past the end included, so
  an alias used later is not checked again. An index into a word or a struct
  is `.undef` (no typed path is one).
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
- **A copy into storage is a write over what is there** (`Storage.write`,
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
refuses it (its code reverts, or runs out of the 2300 gas). `TRun.transfer`
does neither check: a negative amount reverts (since 2026-10-07; it was
`.stuck`): it is unrepresentable in the unsigned value field, so never
negative on the EVM, and in the typed run it is unrepresentable too
(`TRun.transfer` takes a `Val C Γ .uint`, `msg.value` is a `TTx` field of
type `uint`); the revert survived only in the untyped `transferAt` (gone at
W10.5.1); otherwise the payment is booked at the
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
EVM. So the outcome is the transaction's, as a `try`'s is: `sendT` looks the
call up in `TxEnv.ext` at `sendKey a v` (the address, empty calldata, the
amount as the one word). No entry, or `ok`, is a recipient that takes the
payment (an address with no code does): the payment is booked as `transfer`
books it (`State.pay`) and `ok` is `true`. Any other entry is a refusal: nothing
is booked and `ok` is `false`. A negative amount reverts, as for `transfer`.

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

A send is outside the compiled fragment (`Evm.inFrag` refuses it).
`(bool ok, ) = a.call{value: v}("")`, which solkey lowers to
`bool ok = a.send(v);` (its `SolJSONParser.isValueCall`), is not written in
`sol{}` on this branch: it needs tuple syntax. Under solc that call forwards
all the gas, so the callee may re-enter; the reading without callbacks
ignores that, as solkey's `noCallback` does.

## Calls

solc evaluates every argument of an internal call, left to right, before the
callee runs. `Stmt.run` does the same: it evaluates the arguments in the
caller's context (`Args.evalT`) and runs the body in a frame of its own, its
returns on its parameters (`Stmt.call`, `Syntax/Scoped.lean`), which sees
no caller's local; KeY's function-body expansion declares the parameters one
after another, and the two agree because no argument can read a parameter.

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

## Constructors

A deployment (`Contract.deployT`, `Calculus/Deploy.lean`) runs the program
`constructor(args);` typed from the state `State.deploy C tx`
(`Calculus/Deploy.lean`): every root at its
default, no locals, an empty heap, `net` holding the deployer's payment.

- **A constructor that is not `payable` refuses value**, as solc's creation
  code reverts on a nonzero `CALLVALUE`: `Contract.deployT` reverts before it
  runs anything.  The obligation does not check it: solkey's unspecified
  one has no `msg.value` fact, and `Problem.deploy_of_valid_nil` takes
  `payable ∨ msg.value = 0` as a hypothesis; a specified one assumes
  `msg.value = 0` (`spec!{constructor}`).
- **`address(this).balance` is `msg.value`** (`selfBalance := msgValue`,
  solkey's update).  On the chain it is the value plus whatever the address
  held before the deployment (an address can be paid before its code is
  created, by `CREATE2`'s predictable address or a `selfdestruct`).  Lean
  follows solkey; a contract whose constructor asserts
  `address(this).balance == msg.value` is proved here and can fail there.
- **Initializers run first, outside the modifiers**: after the
  parameters are bound and before the constructor's modifiers and body
  (`elabCallRet`'s `ctor`), as solkey's `ExpandFunctionBody` prepends them.
  solc runs them in the creation code before the constructor function, so
  the order agrees; the parameters are bound first, but binding has no
  effect, and a parameter that shadows a root does not capture the
  initializer, which is prepended after the renaming.
- **Constants and immutables are storage** in `contract!` (a root with an
  initializer, as solkey's `SolJSONParser` reads them); solc inlines a
  `constant` and writes an `immutable` into the code.  They agree on every
  read once deployed, but a function's obligation starts from any
  well-typed storage, where the root holds any value: `assert(L == 5)` is
  unprovable there (`docs/solkey-feedback.md`, item 9).  The solc import
  keeps them a `Gap`.
- **A contract with initializers and no constructor** deploys by the
  implicit one (`constructor();` runs the initializers), as solc does, and
  has no obligation, as in solkey.
- **The unspecified obligation books the payment** (`Problem.ctor`): Lean
  states it with solkey's specified update (`Problem.deployUpd`), where
  solkey's unspecified problem writes `{storage := mtSt || net := mtSt}`
  (`docs/solkey-feedback.md`).

## Remaining deltas (documented, intentionally out of scope)

- **Error classification.** A failing `assert` (Panic 0x01) is `Halt.panic`,
  a halt of its own (the table above). Every other failure collapses into
  `Halt.revert` (the typed run's `THalt.revert`; the term model's ill-sorted
  value is `Halt.undef`, which no run reaches); solc distinguishes the other `Panic(uint256)`
  codes, `Error(string)` and empty revert data. Checked overflow (Panic
  0x11, at a narrow width too), an out-of-range index (0x32), an empty `pop`
  (0x31) and a zero divisor (0x12) are all `.revert`; "rejected at compile
  time" and "outside the fragment" are not programs (the elaborator refuses
  them) or `.undef` on an ill-sorted erased state, except an access through
  an unset storage pointer, a negative `**` exponent and a negative
  `transfer`/`send` amount, which revert (since 2026-10-07; the table above). The compiled code has no
  panic: there a failing `assert` reverts (`compile_correct`).
- **Block-scoped locals.** The locals check scopes them as solc does, and
  so does the run (`Semantics/Run.lean`), the only one since W4; a
  conditional of two indexed memory references allocates an object nothing
  reaches (the table above).
- **Fragment width.** Loops run (`TLoop.run`, `docs/loops.md`) and are
  proved by unwinding to a bound or by an invariant, but the EVM compiler
  refuses them (`Evm.inFrag`); `uintN`/`intN`
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
  deployed contract holds lengths up to `2^64` and no longer; here a length
  is bounded only by `2^256` (the push at it `exhausted`, "Array lengths"
  above) and `wt(storage)` (`storageWtB`) bounds words and keys, not
  lengths. A diamond obligation that reads a length through checked
  arithmetic after a push (`storagePushReadBack`: `values[values.length -
  1]` after a `push`) is valid in the model all the same, since the push at
  a full array is out of gas and the length after one is at least `1`; it
  is derived since W10.4 (the closer reads `len < len + 1`,
  `Facts.ltSucc`).
  One that pushes with no bound on the length before it holds in the model
  where solc panics, from a length of exactly `2^64`:
  `storagePushLengthPositive`, `storagePopUnknownLength` and
  `arrayOfMappingsIndex` are derived (`TestSuite/Derived7.lean`,
  `TestSuite/Derived8.lean`) and true of solkey, whose `int` is unbounded,
  but not of solc from that storage (`docs/testsuite-proofs.md`). Closing
  it means a bound `≤ 2^64` on every length in `wt` and the 0x41 panic in
  `Storage.push`.
