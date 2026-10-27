# Aligning the executable semantics with solc

The interpreter, the typed run (`Stmt.run`, `Solidity/Semantics/Run.lean`)
over the typed state, is a port of KeY's state layer, and KeY's calculus is in several places more liberal than the
Solidity compiler it models. Where the two differ the interpreter follows
**solc** (the 0.8 line), and this document is the authority for where and
why. solkey `f2eb3d98eb` reads storage the same way in the array items
below. The EVM compiler's own deltas are in `docs/compiler-verification.md`;
how these claims are tested against solc is `docs/solc-validation.md`.

## Where the interpreter follows solc, not KeY

| Topic | Behaviour | Lean anchor | Witness |
|---|---|---|---|
| Checked arithmetic | `uint` is `uint256`, `int` is `int256`; a result outside the range reverts (`Panic(0x11)`), at the result type of `+ - * **`, `++`/`−−`, and `op=` | `PrimTy.ofInt?`, `BinOp.evalT`, `OpLoc.storeT`, `OpLoc.bumpT` | `Evm/Examples.lean` (`**`) |
| Unary minus | at `int` only, range-checked there: `-x` at `uint` is refused by the elaborator and the spec reader (`UnOp.accepts`), as solc refuses it | `UnOp.accepts`, `UnOp.evalT` | |
| `**` | reverts on overflow (`2 ** 256`), `0 ** 0` is `1`, a negative exponent reverts: solc's exponent is unsigned, so never negative on the EVM.  In the typed run a negative exponent is unrepresentable (`BinOp.accepts .pow` is `uint`, an operand a `PrimTy.uint.Denote`, the environment a `TTx` of `uint`s); the revert survives in `BinOp.arithInt` | `BinOp.arithInt` | `Evm/Examples.lean` |
| Literals | a literal is in its type's range, `uint` below `2^256`, `int` in `[-2^255, 2^255)`: one out of it is solc's compile error, and here no term (`Simple.lit` carries `PrimTy.inRange`); the elaborator refuses it (`litAt`), and the EVM fragment no longer checks it.  In a constant expression solc folds the literals exactly first: `2**256 - 1` written out as one literal minus `1` is the literal `2^256 - 1`, and so here (`check` folds `+ - *` and an exact `/` of two literals, `BinOp.foldLit?`; a result out of range is still refused) | `Simple.lit`, `PrimTy.inRange`, `litAt`, `BinOp.foldLit?` | `Typing/Tight.lean` (`SVal.Fits`) |
| Mappings in memory | a memory local, a memory declaration and a memory path are at a type with no mapping (solc rejects one): `MPath.var` and `declMem` carry `(Ty.ref R).mapFree`, and a member or element of a memory path inherits it (`MPath.mapFree`).  The typed heap holds no mapping object (`MObj`, `Semantics/Heap.lean`), so the run never allocates one, and the typed copies (`Heap.allocDefault`, `SVal.copyStToM`) take a `mapFree` type | `MPath.var`, `Stmt.declMem`, `memOk` | |
| `bool` mapping keys | a `mapping(bool => V)` keeps two slots, at `0` and `1`: solc hashes a key padded to a word (`keccak256(h(k) . p)`), and a `bool` pads to `0`/`1` (decisions 10 and 14, `docs/intrinsic.md`).  The typed run hashes an index at its key type (`PrimTy.key`: a `bool` as `0`/`1`, a number as itself), so the closer tells two keys apart by their words | `PrimTy.key` | `Typing/Constructibility.lean` (`bool_key_reachable`) |
| Storage pointer without a target | `T storage p;` binds `p` to no path: a read or a write through `p` reverts.  solc rejects such a read statically; KeY's `storageLocalDeclSkip` binds nothing (`docs/lean-key-rule-map.md`) | `SPath.resolveT` (`.alias` at `none`), `Rhs.unset` | `Examples/Tactics/StorageSuite.lean` (`unsetAliasWrite`, `unsetAliasRead`, `unsetAliasLoop`) |
| Memory local without an object | a memory local may be unset (decision 17', `docs/intrinsic.md`): no statement leaves one so (`T memory m;` allocates a default object, as solc's zero-initialised memory does, and every other declaration binds an object), but the calculus's hidden binder ranges over it, as over an unset alias (above).  A read or a write through an unset memory local reverts, in the typed run (`MPath.mvalT`) and in the terms the calculus reads (`Calculus/Lands.lean`).  solc has no such local | `LTy.TDenote`, `MPath.mvalT` | `Calculus/Sound.lean` (`Stmt.sound`) |
| Block-scoped locals | in the type (the elaborator emits the scoped `Stmt C Γ Γ'`, so a local out of scope does not elaborate): the elaborator (`NCtx.find`, `elabProgS`) reads the branches of an `if` and a `try`, a loop's body and a call's body as scopes and a name as its newest declaration, so `{ bool x = true; } if (c) { uint x = 1; }` is accepted, as solc accepts it, and a branch's local is not read after it.  The run (`Stmt.run`, `TRun.ite`/`TRun.block`) pops a scope's locals at its end, and the typing invariants are carried along it (`Typing/TypedRunInv.lean`), so no local outlives its scope | `NCtx.find` (`Syntax/Elab.lean`), `elabProgS` (`Syntax/Splice.lean`), `TRun.ite`, `TRun.block` | `Examples/Tactics/Branch.lean`, `Syntax/Splice.lean` |
| Conditional of memory references | `T memory m = c ? a : b;` binds `m` to `a`'s or `b`'s object, as solc: the elaborator declares a fresh `mv` before the branches, bound to a branch that indexes nothing (a read that cannot revert on a set local), and rebinds it in each branch.  An unset memory local, which only a hidden binder holds (decision 17' of `docs/intrinsic.md`), reverts on that read where solc reads only the branch taken: when the index-free branch is such a local and is not taken, the program reverts where solc's does not.  When both branches index, `mv` is first bound to a fresh default object (`T memory mv;`), which nothing reaches: the heap has one object solc does not allocate.  So when both branches index and `T`'s default is not well-formed (`defaultOkS`), the conditional is refused ("a conditional of two indexed memory …s, whose default is not well-formed") | `hoist`, `MPath.indexFree` | `Syntax/Splice.lean`, `Examples/Tactics/Branch.lean` |
| `checked { }` | Lean only (KeY Java's `arithmeticSemanticsCheckingOF`): each checked operation is preceded by an `assert` of its range, so an overflow is a panic, which neither modality accepts, where outside the block it is a revert (solc's `Panic(0x11)` is read as a revert, solkey's `outOfBounds` reading); `**` and division by zero stay reverts (`docs/options.md`, O2) | `Prog.checkOF`, `Stmt.guard` (`Syntax/Checked.lean`), `narrowCheck` | `Examples/Tactics/CheckedBlock.lean` |
| `ignoringOverflow { }` | Lean only (KeY Java's `arithmeticSemanticsIgnoringOF`, read soundly): each checked operation is preceded by `if (range) {} else { assume(false); }`, so an overflowing run is assumed away under either modality, where outside the block it reverts; not solc (`docs/options.md`, O5) | `Prog.ignoreOF`, `Stmt.assumeFalse`, `LeanTaclet.assumeFalse` | `Examples/Tactics/CheckedBlock.lean` |
| `unchecked { }`, shifts | `+ - * **` in `unchecked` wrap modulo `2^256` (`+%` …); `~`, `<<`, `>>` are solc's at `uint256` | `BinOp.arithInt`, `RawExpr.uncheck` | |
| Narrow integers | `uint8` … `uint248`, `int8` … `int248`: an operation at a narrow type reverts outside its range, `unchecked` and `<<` wrap modulo `2^N`, an implicit narrowing is refused, a `uint` cast truncates (below) | `narrowTy?` (`Syntax.lean`), `narrowPost`, `narrowCapture`, `narrowWrapNode`, `castCapture` (`Syntax/Elab.lean`) | `Examples/Tactics/Checked.lean` |
| Byte types | Lean only (solkey gives `string` an opaque `int` and skips `bytes`): `bytesN` is a `uint` of `8N` bits holding its bytes big-endian, so `==`, `<`, `& \| ^ ~ << >>` are the narrow integer ones; a conversion between sizes keeps the left bytes or pads on the right, as an implicit widening does; `b[i]` reads byte `i` from the left and reverts past `N` (solc's `Panic(0x32)`, read as a revert as an array's is); a literal is left-aligned. `bytes` and `string` are a `bytes1[]` in storage and memory, `bytes(s)`/`string(b)` the identity, a literal a fresh memory array | `bytesPure`, `hoist` (`Syntax/Elab.lean`), `valueRows?` (`Syntax.lean`) | `Examples/Tactics/Bytes.lean`, `tests/solc/Bytes.sol` |
| `calldata` and slices | calldata roots are read-only model memory inputs; ordinary aliases must originate at admitted calldata parameters/aliases, and writes or writable escape through ordinary shared aliases are refused. `b[i:j]` is a stable finite base/offset/length descriptor with relative bounds checks. Whole-slice uses with primitive elements allocate a fresh dynamic memory copy for internal calls/returns, hashes/ABI consumers and existing storage copying; readonly indexing, length and decoding use the descriptor directly. Reference/nominal elements and external reference arguments remain unsupported | `RawStmt.sliceViews`, `calldataCheck`, `#sliceCopy` (`Syntax/Elab/Context.lean`, `Syntax/Elab/Arms.lean`), `Frontend/Import.lean` | `Examples/Tactics/SliceCopies.lean`, `Examples/Tactics/SliceCopiesImport.lean`; [calldata-slice-copies.md](calldata-slice-copies.md) |
| Hashing and the ABI | Lean only (solkey has neither): `keccak256`, `sha256`, `ripemd160` Keccak-256, SHA-256 and RIPEMD-160 of the bytes (`keccakBytes`, `sha256Bytes`, `ripemd160Bytes`; collision resistance not assumed), `ecrecover(h, v, r, s)` of the precompile's four words: `0` where `v` is not `27`/`28` or `r`, `s` lie outside `[1, n)`, as solc returns, else computed secp256k1 recovery (`ecrecoverKey`), accepting high `s` and returning zero on curve-recovery failure. The implementation uses checked curve points and bounded arithmetic; conformance vectors do not establish a general external-precompile equivalence theorem; `abi.encode`/`abi.encodePacked`/`bytes.concat`/`string.concat` a fresh memory `bytes` of solc's layout, `abi.decode` its inverse at value types, reverting on a word out of range; `mapping(string => V)` keyed by the hash | `Val.hash`, `Op2.hash`, `HashKind`, `LeanTaclet.hashAssignment`; `abiEncode`, `abiDecodeAt`, `hashKeyRows` (`Syntax/Elab.lean`, `Syntax.lean`) | `Examples/Tactics/Hashing.lean`, `tests/solc/Hashing.sol` |
| Division | `/` and `%` by zero revert (KeY agrees) | `BinOp.arithInt` | |
| `assert` | a failing `assert` panics (`Panic(0x01)`), a halt distinct from `require`'s revert that neither modality accepts; KeY's "Violated" goal, an obligation under the box too | `TRun.assert`, `Modality.afterRunTR`, `Taclet.assertSimple` | `Examples/Tactics/Revert.lean` |
| Panic data | in the callee a self-call `try` runs, a failing `assert` reverts with `Panic(0x01)`'s data and a failing check in `checked { }` with `Panic(0x11)`'s, so the `try` binds solc's code; elsewhere they panic as above (no `try` reads their data) | `elabStmt1` (`assert`), `OFMode.guardStmt` | `Examples/Tactics/RevertData.lean` (`Panics`), `tests/solc/RevertData.sol` (`panicData`) |
| Assignment order | right-hand side first, target resolved once | `Stmt.run` (`TRun.assign`, `TRun.opAssign`, `TRun.incDec`) | `Examples/Tools.lean` (`Prog.runT`) |
| Effects in an expression | captured before the statement in solc's order (table below) | `hoist`, `captureExpr` | `Examples/Tools.lean` (`Prog.runT`) |
| Repeated member names | a struct that declares two members of one name is refused ("Identifier already declared"): the elaborator refuses a type naming one (`refusedStructs`, `unknownStructMsg`, decision 16), so every struct of `structDef` has distinct member names | `structDef_nodup` | `Syntax/Splice.lean` (`BadDup`) |
| Mapping-carrying copy | a storage copy of a type containing a mapping cannot be written | `Src.copy` (`mapFree`), `tyHasMapping` | |
| Arrays past their end | `pop`, `delete`, `push` and copies keep the slots past the length; an index is checked when the path is taken | `SVal.array`, `checkIndex`, `SVal.overlay` | `testDanglingReferenceSurvivesPush` and three more |
| Array lengths | a dynamic array holds fewer than `2^256` elements: its length is a `uint` (decision 13, `docs/intrinsic.md`).  The typed storage and heap carry the bound (`SVal.array`, `MObj`), so a typed length read is in range (`Storage.len`, `Heap.lenU`).  A push onto `2^256 - 1` elements exhausts the resources: the typed run halts with `exhausted` there (`Storage.full`, `TRun.push`; decision 15), and both modalities accept it (`Modality.onTHalt`), as KeY, which models no gas, reads every run (solkey's arrays are unbounded, so its diamond obligations with a push stay provable).  solc panics (`0x41`) on a storage array past `2^64` elements and its code runs out of gas long before; Lean's bound is `2^256`, and an exhausted run proves any modality.  A push below the bound ends (`Semantics/Ends.lean`).  A reverting push would make the diamond obligations with a push (most of solkey's TestSuite) undischargeable, since a storage with `2^256 - 1` elements is reachable | `SVal.array`, `MObj`, `Storage.full`, `lenU` | `Semantics/Ends.lean` |
| Recursion depth | a recursive call (`Stmt.callRec`) runs its body unrolled to `recDepth` (1024) nested frames, the bottom one `exhausted` (`recUnroll`, `Prog.recBase`): the EVM's stack holds 1024 words and every internal call's frame at least its return address, so a deeper recursion overflows the stack and halts, which both modalities accept as they accept exhaustion (decision 15).  KeY inlines a recursive callee without end and proves it by contract; the run here is the EVM's below the bound and a halt above it, never a wrong state (the EVM may overflow before the bound: a sound over-approximation); a diamond over a recursive call is therefore no termination claim (`docs/kernel-port.md`, "Recursion") | `recUnroll`, `recDepth`, `Stmt.run_callRec` | `Examples/Tactics/Recursion.lean` |
| Fixed-size arrays | `delete` resets in place, the length is the literal `n`, a literal index `≥ n` is a compile error | `SVal.array … fixed`, `MObj.array` | |
| `transfer` | books `net(a) - v` unless `a` is the contract itself, and nothing else; whether the world pays is the EVM's (a refused payment reverts the machine alone) | `TRun.transfer`; `Evm.compile_correct` | `Semantics/Run.lean` |
| `send` | `ok = a.send(v);` books as `transfer` does and sets `ok` true, or books nothing and sets `ok` false, never reverting; which, the transaction's oracle says | `TRun.send`, `TTx.ext` | `Examples/Tactics/Net.lean` |
| Call arguments | supported positional calls read arguments left to right before the callee runs; storage parameters alias, memory parameters alias memory, and storage-to-memory arguments copy at their evaluation point before later effects. Primitive slice arguments materialize fresh snapshots; admitted ordinary calldata aliases retain read-only restrictions | `Args.evalT`, `hoistCallArgs`, `CallRet.enterT` (`Semantics/Run.lean`, `Syntax/Elab/Stmt.lean`) | External reference arguments and general writable whole-calldata copying remain unsupported; this order claim does not extend to named event arguments or binary/addmod operands. |
| `call{value:}` | `(bool ok, ) = a.call{value: v}("")` is a send with all the gas (`Stmt.send`'s `full`), where solkey's `SolJSONParser.isValueCall` reads `bool ok = a.send(v)`: solc forwards all gas there, so the callee can re-enter and write storage, under `transferSemantics:noCallback` too (`ValidT .noCallback`, `Stmt.forksIn`); `holds` ignores it (every callee keeping the state). `send` and `transfer` forward the 2300-gas stipend, under which the no-callback reading is the EVM's | `Frontend/SolcJson.lean` (`valueCall?`), `Semantics/Callback.lean` | `Examples/Tactics/Callback.lean` (`withdrawCall_noCallback`) |
| Struct constructors | `S(a, b)` and `S({x: a, y: b})` build a fresh memory struct with declared member types. Legacy allocates the enclosing struct before evaluating/writing its fields; viaIR evaluates and captures every field, including implicit storage-to-memory copies, before allocating the enclosing struct. Named fields retain their compiler-specific evaluation order separately from their destination member positions. The struct must be the table's (`Semantics.structDef`) | `call` (`Frontend/SolcJson/Body.lean`), `hoistWith` (`Syntax/Elab/Arms.lean`), `RawExpr.orderNamed` | `tests/solc/StructLiterals.sol`, `Examples/Tactics/AggregateSlices.lean` |
| Event operands | unqualified direct positional emits resolve the exact `EventDefinition`, validate arity, evaluate operands in source order and abstract the log. Named argument lists and qualified event names are refused. Pinned compiler/EVM traces differ for named events: legacy uses parameter order, viaIR source order | `stmt1` (`Frontend/SolcJson/Body.lean`), `RawStmt.eval`, `eagerArgsWith` | `Examples/Tactics/CallExceptions.lean`; [feature-work/calls-exceptions.md](feature-work/calls-exceptions.md). Event support remains partial. |
| Enum conversions | `E(x)` asserts that `x` names a member (solc's Panic `0x21`), then is `x`; an enum is a `uint` | `enumCapture` (`Syntax/Elab.lean`) | `Examples/Tactics/SolcOpen.lean` |
| A call's ABI | a function's obligation assumes what its dispatcher checks before the body: `msg.value == 0` where it is not `payable` and the body reads `msg.value`, a narrow integer or an enum parameter in its range (solc's decoder reverts otherwise); the specified obligation assumes the first already. **Chain fact:** `msg.value < 2^128` where the function is `payable` and its body reads `msg.value` (`etherBound`, `Calculus/SurfaceSpec.lean`; the specified obligation too): no transaction carries more than the ether supply, below `2^128` wei, so `5 + msg.value + msg.value` does not overflow. Every plain imported source obligation also assumes the EVM environment fact `address(this) < 2^160`, including constructors; the core transaction field remains a 256-bit word. Explicit self addresses outside that domain are rejected. See [source-inputs.md](source-inputs.md). | `Problem.callPre` (`Frontend/Problems.lean`) | solkey's `SolcPaymentsOpen`, `SolcTypesOpen` |
| External calls | `r.f(a);` outside a `try` is `try r.f(a) { } catch { revert(); }`: a failed call reverts the caller, as a call to an address with no code does; `receive` and `fallback` are imported with no obligation of their own | `SolcJson.lean` (`isExternalMember`, `tagOf`) | |
| `try` | a call to an address with no code, and returned data that does not decode, revert in the caller and no `catch` catches them; KeY leaves both out (they are vacuous in its box rule). **Modelling assumption:** address `0` has no code, so a call to it reverts in the caller whatever the transaction's table says (`TRun.tryCall`'s first test; on the EVM `0` holds no contract on any chain this targets). A callee that is a function of the contract declared before the caller runs, in a frame of its own (`msg.sender` the contract, `msg.value` `0`), when the receiver is `address(this)`: its writes are seen on success and undone on failure, a revert going to the `Error` clause when its data decodes as `Error(string)`, to `Panic` when it decodes as `Panic(uint256)`, to the catch-all otherwise, a panic to `Panic` (`docs/options.md` O8); a named reason or data is bound from the callee's revert (`Stmt.catchData`, `docs/semantic-gaps.md`, "Revert data"). A value call `(bool ok, ) = r.call{value: v}("")` to `address(this)` runs the contract's `receive` so (`msg.value` `v`; a payment to oneself moves no ether), written by the elaborator as a self-call `try` behind `r == address(this)` (`elabValueCall`), `ok` false on any failure. The callee has all the gas, so it may call back under either `transferSemantics` (`ValidT`, `docs/options.md`); `holds` reads it as keeping the state, as solkey's `tryCallNoCallbackBox` does | `Stmt.run` (`.tryCall`), `Binders.decodeT`, `ExecS.tryOk` | `Examples/Tactics/TryCatch.lean` (`selfCall_noCallback`) |

## Evaluation order

The default below models legacy codegen. `Contract.evalOrder := .viaIR`
selects source-order binary expressions and `addmod`/`mulmod` arguments;
[options.md](options.md#o9-expression-evaluation-order) gives the configuration
and its limits. This choice is retained by the named contract, including when
its callees are inlined or its source is imported.

Native `addmod(a,b,k)` and `mulmod(a,b,k)` retain all three unsigned
operands and compute the intermediate sum/product as an unbounded integer,
then reduce modulo `k`; they do not perform checked `uint256` addition or
multiplication first. This follows Solidity's
[builtin arithmetic specification](https://docs.soliditylang.org/en/v0.8.17/units-and-global-variables.html#mathematical-and-cryptographic-functions).
A statically literal zero modulus is rejected, including when another
argument has effects. Dynamic zero follows the interpreter's existing
arithmetic-failure abstraction: `THalt.revert`. Solc's checked builtin
raises Panic 0x12, while the raw EVM ADDMOD/MULMOD opcode returns zero; the
model does not claim their halt classifications are identical.

The frontend uses the legacy right-to-left argument order described below,
captures a modulus read before a later argument changes it, and preserves
an ordinary declared function named `addmod` or `mulmod`. The modulus is
captured and checked before the other operands' effect prefixes: a zero
modulus suppresses an operand's failing helper, matching the legacy
compiler's guard order. Kernel-checked
execution and derivation regressions are in
`Examples/Tactics/ModularArithmetic.lean`. The native operations are
explicitly outside `Evm.valIn`; this change extends the interpreter and
proof calculus, not the verified EVM compiler.

solc compiles `lhs = rhs` by evaluating the right-hand side first, in both
the legacy and the via-IR pipeline, and resolves an increment, decrement or
compound-assignment target once. `Stmt.run` does the same: `.assign` and
`.opAssign` evaluate the source before resolving the target, and `.incDec`
reads and writes through one resolved location. KeY's calculus agrees only
where the right-hand side is complex (`a[++i] = ++i` leaves `a[2] == 1`);
solkey's rule for a simple right-hand side bound the index first, so
`a[i++] = i` proved `a[0] == 1` where solc writes `0` (fixed in solkey since).

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
(`ElabScope.inlined`).
In a written derivation, a program's own fresh-shaped local (`se1`, `sp1`, `ie1`, `mv1`, `brk1`, …,
as `FreshNames.parse` reads it) is still taken for a written-out capture and
is not captured again: `uint se1 = 0; y = se1++ + se1;` reads the right
`se1` after the `++` (`1`, where solc gives `0`), by the convention of
written lines (proposed decision 30 of `docs/intrinsic.md`).

Imported Solidity source has no such convention. `solc_import` supplies the
names of its roots, parameters and raw statements to the elaborator
(`ElabScope.mutableFreshNames`), so source locals such as `se2` remain mutable.
Generated temporaries start beyond those names' fresh indices; source
provenance survives an inlined call. A fresh-shaped state-variable read is
captured in both modes, since a root is never a generated local capture.
`Examples/Tactics/PushSuffixSource.lean` checks the correct result and rejects
the former wrong result for source locals, parameters, state variables and
ordinary binary arithmetic.

`Examples/Tools.lean` pins three of them (a block run typed,
`Prog.runT`, `Tools/Run.lean`). An effect under the right
operand of `&&`/`||`, or in a branch of a conditional, would run where solc
does not run it, so it is an elaboration error.

**Binary operators follow the legacy pipeline by default.** solc's legacy
generator evaluates the right operand first (`ExpressionCompiler.cpp`); the IR
generator the left first, so `++a + a` at `a = 1` is `3` in legacy and `4`
via IR, neither guaranteed (`docs/ir-breaking-changes.rst` in solc). A proof
about `x = i++ + i` holds for the schedule its contract selects (O9).

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
- **Casts.**  A cast keeps the low bits of its operand's 256-bit word, as
  solc's conversions do: `uintN(e)` of a `uint` is `e % 2^N`, of an `int`
  `uint(e) % 2^N` (`uint(i)`, `UnOp.toUint`, the two's complement word), and
  `intN(e)` reads the low `N` bits signed, `int(((w +% 2^(N-1)) % 2^N) -%
  2^(N-1))` of the word `w` (`int(u)`, `UnOp.toInt`, `signedAt`): so
  `int8(uint8(200))` is `-56`, `uint8(int8(-100))` is `156`,
  `int8(int(255))` is `-1`.  A widening cast within a sign keeps the value.
  Either is a capture at its type, so the operations after it are checked at
  the cast's width (`castCapture`).  On the machine the conversions are no
  code: the word is the same (`toInt_simT`, `toUint_simT`).
- **`unchecked`** wraps `+ - * **` and `<<` modulo `2^N` (`(x +% 1) % 256`),
  and `~x` at `uint8` is `255 -% x` (`narrowWrapNode`).  At `int` and
  `intN`, `+ - *` wrap on the operands' words, read back as a cast:
  `x + 1` at `int8` is `int8(uint(x) +% 1)`, so `127 + 1` is `-128`.
- **Signed `unchecked`** wraps unary `-`, `/` and `**` too: `-x` is
  `int8(0 -% uint(x))`, so `-(-128)` is `-128`; `x / y` at `int8` is the
  quotient at `int` read back (`-128 / -1` is `-128`), and at `int256` the
  quotient by `1` where `y` is `-1`, negated on the words
  (`type(int).min / -1` is `type(int).min`); `x ** k` is the words' power,
  `int8(uint(x) **% k)`.  Checked, each reverts as solc panics (`0x11`).
- **Short circuits and conditionals.**  A narrow operation under the right
  operand of `&&`/`||` or in a branch of `c ? a : b` is checked only where
  solc evaluates it: `bool se = a; if (se) { se = b; }`, and
  `uint se; if (c) { se = a; } else { se = b; }` (`hoist`).
- **Literal conditionals.**  `c ? 63 : 255` has solc's type: the smallest
  type holding both literals (`uint8`, `mobileTy`), and a literal beside a
  value its own smallest type (`c ? x : 300` is a `uint16` at `uint8 x`).  So
  `(t ? 63 : 255) + (f ? 63 : 255)` is a `uint8` addition, and reverts.
- **`type(T).max`, `type(T).min`** are values of `T`: `type(uint8).max` is
  `uint8(255)`, so `type(uint8).max + 1` overflows at `uint8`;
  `type(int8).min` is `int8(-128)`; an enum's are its first and last member
  (`typeBoundExpr`, `enumLit?`).
- **Narrow positions inside a type.**  An array's element, a mapping's value
  or key may be narrow (`uint8[] small; mapping(uint8 => int16) m;`): the
  variable's `Ty` has `uint`/`int` there, and `Contract.widths` keeps each
  position's width under its path (`small[]`, a key `m{}`, a value `m[]`;
  `expandStateTyW`).  A struct's narrow member is the struct table's
  (`Semantics.structWidths`, beside `structDef`: `struct Packed { uint8 a;
  int16 b; uint c; uint8[] xs; }` keeps `a`, `b` and `xs[]`), in storage, in
  memory, as an element.  A storage alias, a memory local, a reference
  parameter or return carry the narrow positions of their declared type
  beside it (`uint8[] memory m` is `[]` at 8 bits: `LocalTy.shape`,
  `elabTyW`, `FunDecl.widths` keyed `xs[]`).  A read through indices and
  members has its position's type (`widthPath?`, `intTyOf`), so a write is
  checked or wrapped at it as a narrow variable's is, and a pushed value, a
  key and a member's value must fit (`fitCheck`).  A reference type carries
  no width, so a place with a narrow position below it is used whole only
  where its narrow positions are checked against the target's
  (`shapeCheck`): a reference local's initializer (`uint8[] storage s =
  small;`, `uint8[] memory m = small;`, `new uint8[](n)`), a reference
  assignment, a reference argument; another shape (`uint[] storage s =
  small;`) is refused, as solc refuses it.  A conditional of references
  in such a place has each branch checked (`narrowWholeAt?`, its branches of
  one shape, as solc requires), and a struct constructor's argument,
  positional or named, its member's (the member write it is written as);
  any other whole use (an operator's operand, a tuple) is refused
  (`narrowWholeUse?`).  A reference argument's shape is checked as written,
  before a capture names it.
- **Push arithmetic on a narrow element** (`small.push() += v;` at
  `uint8[]`): `v` fits the element, and the appended slot is checked after
  the write, `require(small[small.length - 1] <= 255)` (`pushedSlot`), as a
  variable's write is; so `signed.push() -= x` at `int8` with `x == -128`
  reverts.  Inside `unchecked` it wraps at the element's width: the slot
  starts at `0`, so the statement pushes `0 op r` wrapped (`push() -= 1` at
  `uint8[]` pushes `255`, `signed.push() -= x` with `x == -128` pushes
  `-128`), `r` evaluated once, before the push (`elabStmtP`).
- **A modifier's narrow parameter** is a local of its type, its argument
  fitting it (`ModApp.widths`, `wrapMods`); a reference parameter is a
  local at its location (`ModApp.locs`: a storage alias, or a memory local
  bound as `T memory y = a;` binds it), its narrow positions checked against
  its argument's (`rawTyW`).
- **Storage packing** is not observable here: a state variable is a value of
  its own in the interpreter and a slot of its own in the compiler, and it
  holds a value of its range; solc packs several narrow variables into one
  slot, which only an `sload` or inline assembly would see.
- **Comparisons** compare the values, which solc's conversion to the common
  type preserves: nothing to check.

What is not modelled, each an elaboration error unless said otherwise:

- a place with a narrow position below it used whole other than where its
  shape is checked (a tuple of references is refused whatever its types,
  `elabTuple`); a narrow type in a position not listed above (a
  struct not in the table's widths, `narrowNestedMsg`);
- a cast of arithmetic on literals alone to a narrow `int`
  (`int8(100 + 100)`): write the literal;
- constant folding: arithmetic on literals alone written to a narrow variable
  (`uint8 z = 200 + 100;`), which solc refuses at compile time, is checked
  at run time instead and reverts;
- type members other than `type(T).max` and `type(T).min`;
- a public function's ABI decoding, which reverts on an out-of-range
  argument: a specification's precondition (`Calculus/SurfaceSpec.lean`) does not
  assume a narrow parameter's range, which is weaker, not unsound.  The
  plain obligation does (`Problem.callPre`): a narrow or enum parameter in
  its range, and each element of a memory array of one,
  `∀ uint i; i < xs.length → lo <= xs[i] ∧ xs[i] <= hi`
  (`SolcFun.elemRanges`), which `sol_leaf` instantiates at the literal
  indices the leaf reads (`allLeftHide`, `Calculus/AllLeft.lean`;
  `NarrowNested.abiElementInRange`).

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
`Storage.obs_write` prove the two agree on every read, literally.

## Arrays past their end

solc never shrinks an array's storage. `pop()` clears the last element and
decrements the length, `delete arr` clears every element and sets the length
to `0`, and the slots past the new length keep what the clearing left, which
is not always nothing: a mapping nested in an element lives at hashed slots
no clearing reaches, and a reference taken before the `pop` still points
there. `SVal.array elems shadow fixed` is that run: `elems` the live
elements, `shadow` the slots past the end.

- **A path is checked where the program takes it.** `Storage.checkIndex` bounds
  an index against the live length once, when the path is resolved
  (`Loc.resolveT`, `PTerm.at`), for a read, a write and an alias bind
  (`uint[] storage p = arr[i];` reverts out of range, as solkey's
  `storageIndexReadArrayBindLocalRoot` guard and solc's `Panic(0x32)` say).
  `SVal.find`/`SVal.save` then address the slot, past the end included, so
  an alias used later is not checked again. An index into a word or a struct
  is `.undef` (no typed path is one).
- **A memory push resolves its receiver once.** In
  `cube[cube[0].length].push(row)`, with both initial cube rows empty, the
  target is `cube[0]`: a typed `Src.copyMem` keeps the copy inside one
  `Stmt.push`.
  `TRun.push` resolves the receiver, snapshots the typed memory value and
  appends it with the new length. The solc 0.8.34 IR computes a single target
  slot and passes it to `array_push_from_*`; `Examples/Tactics/MemoryPush.lean`
  checks the successful source and the old expansion's concrete reversion.
- **A write through a reference to a popped element writes the slot.**
  `Token storage r = tokens[0]; tokens.pop(); r.value = 5;` writes the
  cleared slot. A subsequent zero-argument `push()` of a struct or array
  saves only the length (`storagePushLengthSave`, `pushSlot`) and exposes
  the slot as it is, as solc does, so the model reads `5` from
  `tokens[0].value` (`reused_slot_retains_value`,
  `Examples/Tactics/CleanTail.lean`). Nothing then tells what a recycled
  slot of the starting storage holds; `ValidTail .clean` assumes its tails
  clean (`docs/options.md`, O6). A primitive slot past the end holds its
  default on every reachable storage, so a primitive push starts there; a `pop()`
  clears the element into the shadow (`storagePopSave`), but keeps a mapping
  element as it is (`storagePopSaveMappingElement`). These dangling executions
  are compiler-specific/undefined; the old resurrection specifications are
  migration cases to reclassify, not portable Solidity guarantees.
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

`Calculus/Decide.lean` reads the live storage only (`SVal.findLive`) and is bridged to the program's checked paths; an alias
through an index is outside its fragment once the storage was written after
the bind.

## `transfer`

`TRun.transfer` evaluates its captured operands, checks `State.canPay`
(available balance and the `sendKey` response in `TTx.ext`), and reverts on
refusal. A successful payment to another address debits `selfBalance` and
`net(addr)` by the amount; a self-payment moves neither and still requires
sufficient funds. No table entry or an `ok` response accepts the payment;
other responses refuse it.

`Evm.Sim` relates the spendable balance and the payment response to the
machine, so typed and compiled transfers agree on both success and refusal.
`Sim.init` requires the supplied typed balance to equal `bal self`.
The symbolic box update records a hypothetical successful payment; a
refused runtime transfer satisfies the box by reverting.

The callback reading may then replace storage, ledger and balance, subject
to the stated invariant. These semantics do not model the stipend's gas.

## `send`

`TRun.send` uses the same funds and oracle checks. Success debits the balance
and ledger and returns true; refusal returns false with both unchanged.
A send is outside the compiled fragment. The calculus proves a branch for
each outcome, independently of the oracle.

`(bool ok, ) = a.call{value: v}("")` carries all the gas (`Stmt.send`'s
`full` flag), so its callee may re-enter even under `ValidT .noCallback`.
The plain `holds` reading ignores callbacks, as solkey's `noCallback` does.

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

A deployment (`Contract.deployT`, `Semantics/Deploy.lean`) runs the program
`constructor(args);` typed from the state `State.deploy C tx`
(`Semantics/Deploy.lean`): every root at its
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
  initializer; solkey's `SolJSONParser` now inlines constants, and only
  immutables remain its storage roots); solc inlines a
  `constant` and writes an `immutable` into the code.  They agree on every
  read once deployed, but a function's obligation starts from any
  well-typed storage, where the root holds any value: `assert(L == 5)` is
  unprovable there (`docs/solkey-feedback.md`, item 9).  The solc import
  inlines a `constant`, and an `immutable` nothing writes: its compile-time
  initializer, or its type's default (`writtenIds`, `defaultLiteral`).  An
  `immutable` the constructor writes is a storage root with its
  initializer, so the constructor's obligation reads what it wrote, and a
  function's reads any value (true of the deployed code, never refuted).
- **Base constructors run in solc's legacy order**: every initializer, most
  base first; then the base constructors' arguments, derived to base; then
  the constructor bodies, base to derived (`readContract`'s
  `compositeBody`, one constructor member, each argument a local named as
  its parameter).  This is the creation code of solc 0.8.33's legacy
  pipeline (`ContractCompiler::appendInitAndConstructorCode`: a constructor
  evaluates the next base constructor's arguments and runs it before its
  own body, after `initializeStateVariables` ran for the whole hierarchy),
  read off `solc --asm`.  The via-IR pipeline interleaves instead (each
  contract's initializers just before its body; Solidity docs, "Solidity
  IR-based Codegen Changes", order of state variable initialization), and
  that page's description of the legacy order puts the arguments before
  the initializers, which the emitted code does not:
  `tests/solc/Inheritance.sol`'s `CtorLeaf` passes an initialized `late`
  on and asserts it.  A base constructor's virtual calls dispatch to the
  most-derived contract.  Arguments come from the first contract in the C3
  order giving them, in its constructor's header (`B(a)`) or its
  inheritance specifier (`is B(5)`) ("Arguments for Base Constructors").
  A constructor's modifiers wrap its own body alone, after the base
  constructors ran (`appendBaseConstructor` precedes
  `appendModifierOrFunctionCode`), and a `return` in a base constructor
  ends its body alone: such a body is a member of its own,
  `solcCtorBody<id>(params)`, carrying the modifiers, which the composite
  calls in its turn (`bodyMember?`; `tests/solc/InheritanceCtors.sol`).
- **A base's `private` variable** of a name a later contract declares
  again is a storage root of its own, renamed by its declaration
  (`x_PrivateRoot`, `stateRenames`), and every identifier reads it by its
  declaration's identity; refused where a specification names it, since a
  clause reads a variable by name (`tests/solc/InheritanceGaps.sol`).
- **`super.f`** in a function of contract `D` names the first contract after
  `D` in the most-derived contract's C3 order that implements `f`
  (Solidity docs, "Inheritance": `super` is the next base in the final
  inheritance graph); every base version is its own member, so the call is
  static.
- **A contract with initializers and no constructor** deploys by the
  implicit one (`constructor();` runs the initializers), as solc does, and
  has no obligation, as in solkey.
- **The unspecified obligation books the payment** (`Problem.ctor`): Lean
  states it with solkey's specified update (`Problem.deployUpd`), where
  solkey's unspecified problem writes `{storage := mtSt || net := mtSt}`
  (`docs/solkey-feedback.md`).

## Specification integer negation

SolKey's `SpecCompiler.visitUnary` compiles mathematical negation with
`neg`. Lean represents ledger negation with its existing typed integer
subtraction from zero. A ledger operand supplies the integer context for
negating an unsigned Solidity value, including a typed unsigned constant
and a value under `\old`. Negative literals also take the ledger integer
sort in this context. Either operand order works.
Unsigned negation without a ledger context and signed/ledger mixtures
retain their refusal boundaries. Primitive arithmetic nested inside the
negation stays checked: negating `amount + 1` does not bypass overflow of
that unsigned addition. This changes specification compilation, not
Solidity statement evaluation or the calculus's signature.

## Specification frames and entry premises

Frozen SolKey `048a74de51` accepts but ignores `assignable` clauses
(`KeyNatspec.java`, `SolidityProblemSynthesizer.java`). Lean enforces its
existing storage frames as a stronger extension. Ledger locations and
array-length permissions do not yet have frame semantics; source functions
with ledger locations are explicitly refused. `selfBalance` is separate from
the `net` ledger. See [solkey-migration.md](solkey-migration.md).

The pinned specified-obligation synthesizer assumes `msg.sender != this`.
Lean does not currently impose this condition, so its specified obligations
also cover entry states in which the two addresses coincide. This is a
stronger obligation, not an additional assumption available to its proofs.

## Remaining deltas (documented, intentionally out of scope)

- **Error classification.** A failing `assert` (Panic 0x01) is `THalt.panic`,
  a halt of its own (the table above). Every other failure collapses into
  `THalt.revert`; solc distinguishes the other `Panic(uint256)`
  codes, `Error(string)` and empty revert data. Checked overflow (Panic
  0x11, at a narrow width too), an out-of-range index (0x32), an empty `pop`
  (0x31) and a zero divisor (0x12) are all `.revert`; "rejected at compile
  time" and "outside the fragment" are not programs (the elaborator refuses
  them); an access through an unset storage pointer reverts (the table
  above). The compiled code has no panic: there a failing `assert` reverts
  (`compile_correct`).
- **Gas** is not modelled; resource exhaustion is `exhausted`, which both
  modalities accept. The EVM compiler's fragment is narrower than the run's
  (`Evm.inFrag`, `docs/compiler-verification.md`).
- **Via-IR modifiers.** Via IR, a modifier's parameters are re-initialised
  at each `_;` (solc's `docs/ir-breaking-changes.rst`); the elaborator
  follows legacy (`wrapMods` runs the body again in the same locals), so
  with several `_;`, or one in a loop, a via-IR contract differs: upstream
  `modifiers/function_modifier_loop_viair.sol` and
  `function_modifier_multi_invocation_viair.sol`
  ([solidity-upstream-tests.md](solidity-upstream-tests.md)). `delete` of a
  storage struct via IR also zeroes padding, visible only to a low-level read.
- **`push` over a recycled slot.** `arr.push(v)` of a struct or array value
  lays it on fresh slots (`SVal.strip`), not over the recycled slot it lands
  on, so what a reference wrote into that slot's own arrays past their ends is
  dropped where solc keeps it. No test in the corpus reads it.
- **No bound on a dynamic array's length.** solc's `push` panics (0x41)
  on an array whose length is already `2^64` (`oldLen >= 2^64`), so a
  deployed contract holds lengths up to `2^64` and no longer; here a length
  is bounded only by `2^256` (the push at it `exhausted`, "Array lengths"
  above) and `wt(storage)` (`Storage.wtB`) bounds words and keys, not
  lengths. A diamond obligation that reads a length through checked
  arithmetic after a push (`storagePushReadBack`: `values[values.length -
  1]` after a `push`) is valid in the model all the same, since the push at
  a full array is out of gas and the length after one is at least `1` (the
  closer reads `len < len + 1`, `Facts.ltSucc`).
  One that pushes with no bound on the length before it holds in the model
  where solc panics, from a length of exactly `2^64`:
  `storagePushLengthPositive`, `storagePopUnknownLength` and
  `arrayOfMappingsIndex` are derived (`TestSuite/Derived7.lean`,
  `TestSuite/Derived8.lean`) and true of solkey, whose `int` is unbounded,
  but not of solc from that storage (`docs/testsuite-proofs.md`). Closing
  it means a bound `≤ 2^64` on every length in `wt` and the 0x41 panic in
  `Storage.push`.

## Error arguments and self-call panic payloads

The elaborator evaluates custom-error arguments
for both values of `require`'s condition, and for `revert E(...)` before
reverting. It finishes each operand before starting a later operand's calls
or injected guards. A string reason likewise cannot run before a residual
failing condition. Ignored event operands use the same eager path.

In a self-call frame, invalid enum conversions and unset internal function
values emit the exact literal `Panic(0x21)` and `Panic(0x51)` bytes. Ordinary
assertion/revert classification is retained. Internal-function arguments are
captured once at their formal types before dispatch, including failing fields
and reads changed by later operands. These are local captures, so the
existing soundness proofs apply; the catch-transport lemmas
(`Semantics/RevertMemory.lean`) keep the exact byte list and the caller's
state, heap rollback included.

See [feature-work/calls-exceptions.md](feature-work/calls-exceptions.md);
its EVM reference checks are evidence about the pinned compilers, not a
frontend-equivalence proof.

## Modifier placeholder frames

Legacy reuses the function's parameter and return slots across repeated
modifier placeholders. ViaIR (`EvalOrder.modifierFrames`) gives each
placeholder invocation separate slots: parameters are copied, incoming return
slots are passed to each invocation, and the latest result is copied out.
Modifier results initialize before argument evaluation; argument changes to
named returns affect the incoming slots, not a skipped invocation's result.
Memory/storage referents remain shared through reference parameter aliases.
The elaborator retains and checks all recorded source-shape markers on copies.
Memory return aliases are supported; viaIR modifier functions returning storage
aliases are explicitly refused because unset incoming bindings cannot safely
be copied by a source-level alias read.

The two upstream viaIR return mismatches and distinct legacy controls are
recorded in [solidity-upstream-tests.md](solidity-upstream-tests.md#group-01-viair-modifier-return-slots-2026-10-26).
This lowering uses existing typed statements and sound rules. Runtime/EVM
agreement and the fixed-program proof controls do not constitute a universal
compiler-correctness theorem.
