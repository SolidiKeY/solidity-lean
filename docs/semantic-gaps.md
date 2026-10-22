# Semantic gaps

What of Solidity's semantics the model leaves open, and what is out of
scope. The goal is that nothing of the language's semantics stays open
without a stated reason. A program that uses a gap is refused by the
elaborator or the solc import (an `unsupported` row); a claim the model
cannot prove is `pending` with a reason (`scripts/test-solidity.test.mjs`
pins them). `docs/solc-alignment.md` is where the model follows solc over
KeY; this file is the work list.

## Out of scope: the EVM inside Solidity

The model is Solidity's semantics, not the machine's. These are left out on
purpose, and a program using them is refused:

- inline assembly (`assembly { … }`, Yul), `address.code`, `extcodesize`,
  `gasleft()`, gas stipends beyond `transfer`/`send`'s `noCallback`
  reading, `selfdestruct`, `create2` salts;
- raw calldata and returndata (`msg.data`, `msg.sig`, low-level
  `call(data)` with arbitrary bytes), and expectations on them;
- block and transaction fields other than those the model reads
  (`block.timestamp`; not `block.number`, `tx.origin`, `block.basefee`, …);
- storage layout (slot numbers, packing): `Evm/` compiles a fragment and
  proves it against the model, it does not expose slots to programs.

A fact about the chain that a proof needs is stated as an assumption where
the proof uses it (address `0` has no code, `docs/solc-alignment.md`; see
"Chain facts" below), never derived from a machine model.

Events are evaluated for their arguments' effects and reverts, and the log
is dropped: a log is output of the machine, not state a later call reads,
so it is out of scope with the rest of the EVM above.

## Chain facts, as premises

Functional correctness is proved of a deployed contract called by a
transaction, so what every such call guarantees is a premise of the
obligation (`Problem.callPre`, `Frontend/Problems.lean`), not something to
prove: a non-payable function's `msg.value == 0`, a payable one's
`msg.value < 2^128` where its body reads `msg.value` (the total ether supply
is below `2^128` wei, so no transaction carries more; `etherBound`, also in
the specified obligation, `Calculus/SurfaceSpec.lean`), a parameter in its
ABI range, `address(this)` at a harness address when the test pins one
(`--self-address`). Bounds that hold of every reachable state belong in the
contract's invariant.

## Open

| Gap | Kind | Status |
|---|---|---|
| recursion (`functionsRecursiveUnbounded`) | semantics, calculus | closed: `Stmt.callRec`, unrolled to the EVM's 1024 frames, proved by contract over the frames (`docs/kernel-port.md`, "Recursion"); the runner proves a recursive call by its callee's `/// @custom:key` contract, else `true`/`true` (`rec_auto`, `tests/solc/Recursion.sol`); several returns to a tuple's targets; a storage return by contract (its body rebinds the alias to a path, within `view`: `Stmt.within`'s `rebind`/`declStorage`, `Examples/Tactics/Recursion.lean`'s `pickNoPanic`), an `ensures` that reads the returned alias read in the Theory (`sol_close_alias`, `pickLen`); a memory return that allocates by contract over a grown heap (`Stmt.withinM`, `Fml.grow`, `useRecContractM`, `buildLen`, lane `open-memret`); a reference return's source `ensures` (`recSpecContract`, `pickAuto`, `buildAuto`); under the callback reading (O7) by `rec_auto_c` (`Calculus/RecursionCallback.lean`), storage and memory returns included (`pickPayNoPanic`, `buildPayLen`), an `if` on a condition that is not a local included (`ProvesC.capture`, `docs/options.md` O3); a memory return whose body writes its own objects (`Stmt.withinW`, `Calculus/RunFrameOwn.lean`, `mkAge`); open: such writes under the callback reading, a memory parameter, a length past an element write in the closer (`docs/kernel-port.md` "Recursion", "What is left") |
| a `catch` goal when the callee cannot fail (`tryCatchExactReturn`) | calculus | closed: each self-call `catch` goal assumes `fails(call)`, the walks prove the callee's diamond instead (`notLeft`; `docs/options.md` O8) |
| a value call to `this` runs `receive` (`callRunsReceive`) | semantics | closed: a self-call `try` of `receive` behind `r == address(this)` (`elabValueCall`, O8); `callKeepsStorageUnsound` stays pending, false on the EVM |
| `msg.value` bounded by the ether supply (`msgValueArith`) | chain fact | closed: `msg.value < 2^128` (`Problem.callPre`) |
| literal types in `c ? 63 : 255` (`ternaryLiteralOverflow`, false on the EVM) | elaborator | closed: solc's mobile type (`mobileTy`); the run reverts (`SolcOpen.ternaryLiteralOverflow` refutes the diamond), the row stays `pending` |
| narrow types inside types (`uint8[]`, `mapping(uint8 => …)`, struct members) | semantics | closed: a state variable's narrow element, key and value (`expandStateTyW`), a struct's narrow member (`structWidths`), a storage alias's, a memory local's and a reference parameter's narrow positions (`LocalTy.shape`, `shapeCheck`), a modifier's narrow parameter (`Checked.lean` §2, `tests/solc/NarrowNested.sol`, `docs/solc-alignment.md`) |
| signed `**` in `unchecked`; `-128 / -1`, `-(-128)` wrap in `unchecked` | semantics | closed: on the words (`narrowWrapNode`, `Examples/Tactics/SignedCasts.lean`), at `int256` too |
| `type(T).max`/`min` in `sol{}` (the import folds them) | elaborator | closed: a value of `T` (`typeBoundExpr`), an enum's members |
| a narrow operation under `&&`/`||` or a ternary branch | elaborator | closed: a conditional capture (`hoist`, `Examples/Tactics/Checked.lean`) |
| `super` calls; base constructor arguments | semantics | closed in the solc import (`readContract`, `Frontend/SolcJson.lean`): `super.f` names the next implementation after its declaration's contract in the most-derived C3 order; the base constructors compose into one constructor in solc's legacy order (`docs/solc-alignment.md`, "Constructors"); a base's contract clauses are inherited; a constructor's modifiers wrap its own body after its bases, and a base's `return` ends its own body (`solcCtorBody<id>`, `tests/solc/InheritanceCtors.sol`); `super` in a modifier's arguments or body names the next implementation after the contract writing it (`SuperMod*`; `super.m` as a modifier name solc refuses); a base's private variable of a later one's name is its own root (`stateRenames`), refused only where a specification names it |
| `bytes`, `string`, `bytesN` (values, storage, memory, `.length`, indexing, `push`, literals, conversions) | semantics: types the model lacks | closed by the elaborator's reading ("Bytes and strings" below; `Examples/Tactics/Bytes.lean`, `tests/solc/Bytes.sol`); a byte-string key and the `concat`s since "Hashing and the ABI"; a byte type as a struct member (lane `open-left2`: the struct spells it, `StructEnc`); `calldata` parameters and locals, read only (lane `open-small`, `calldataCheck`); calldata slices `b[i:j]` as views, reads, `.length` and `abi.decode` loop-free (lane `open-abi2`, `RawStmt.sliceViews`; `tests/solc/Calldata.sol`, `Examples/Tactics/Bytes.lean` §6); a slice handed on, hashed or copied stays refused |
| `keccak256`, `abi.encode`, `abi.encodePacked`, `abi.decode`, `string.concat`, `bytes.concat`, `mapping(string => …)`/`mapping(bytes => …)` | semantics: builtins | closed ("Hashing and the ABI" below; `Examples/Tactics/Hashing.lean`, `tests/solc/Hashing.sol`): `keccak256` an uninterpreted function of the bytes (collision resistance not assumed), the ABI's byte layouts lowered by the elaborator, a byte-string key hashed; `abi.encode` of arrays and structs of values, `abi.decode` of `bytes`/`string`, `abi.encodeWithSelector`/`encodeWithSignature`/`encodeCall` (a selector folded by Keccak-256 at elaboration), an `address`/enum packed at 20 bytes/one (lane `open-left2`); `sha256`, `ripemd160` computed and `ecrecover` an address uninterpreted where the signature is well formed, `abi.decode` of `T[]`, `T[k]` and structs of values (lane `open-small`); a locally built byte string's hash evaluated (`keccakAt`) and a symbolic word's packed bytes read back (`hornerU?`; lane `open-closer`); nested types, head and tail recursively (lane `open-abi2`, `AbiTy`: `uint[][]`, `bytes[]`, a struct with a `uint[]`/`bytes`/struct member, run in `Codec3`; a static nested struct proved, `encodeStaticNested`); open: the closer under `⟨⟩` on a hash of a byte string built in the function, runner proofs over a nested encoding (its loops have no invariant) |
| function types (internal function values, `function (uint) returns (uint) f = g;`) | semantics | closed by the elaborator's reading ("Function types" below; `Examples/Tactics/FunctionTypes.lean`, `tests/solc/FunctionTypes.sol`); external function types (an address and a selector), a call through a value that is not a name (`s.f(x)`, `fs[i](x)`, `choose(b)(x)`), a dispatch that recurses (lane `open-left2`); open: reference parameters in a function type, a value of an external function this contract does not declare (`I(a).g` of an interface) |
| revert data: `require(c, "msg")`'s reason, custom errors' arguments, `catch Error(string memory r)` binding `r` | semantics, calculus | closed for a self-call's literal reasons and, in lane `open-alloc`, for another contract's data and data known in part ("Revert data" below; `Examples/Tactics/RevertData.lean`, `tests/solc/RevertData.sol`): the reason reaches `catch Error(string memory r)` / `catch (bytes memory d)` in the run and in the calculus (`catchDataBox`), another contract's as any bytes (`Fml.allocAll`), a custom error of a symbolic argument by its pattern (`Pat`); open: a reason not literal (refused by `sol{}`), a fresh object's bytes read by the closer past its heartbeats (about 400k of 200k, "Revert data", lane `open-closer`), the callback reading's leaves on the bound array |
| recursion under the callback reading (`ValidT`): no contract rule over `ExecS` | calculus | closed: a recursion that does not call back is read without callbacks (`sol_no_callback`, `ProvesC.recValid`), one that does by a contract over the callback runs (`RecContractC`, `ProvesC.recContract`; a storage return's alias bound, `holdsC_callStorage_k`; a memory return over a grown heap, `RecContractCM`, `ProvesC.recContractM`, `ExecP.frameM`), by induction over the frames; `rec_auto_c`, the runner (`docs/kernel-port.md`, "Recursion") |
| a capture whose rest calls back under the callback reading (`if (nse)` with a branch that calls back, a loop unwound whose body does, a payment's non-simple operand) | calculus | closed: `ProvesC.capture`, the side condition on the capture alone (`Stmt.CapturesAs`), and `ProvesC.loopExit` under the box (`docs/options.md` O3) |
| a loop by its invariant and a call returning a value or a reference, while something calls back (`ValidT`) | calculus | closed (`docs/options.md` O3): a call forks where its body does (`Stmt.forksIn`), and one whose callee calls back is inlined under callbacks whatever it returns (`ProvesC.callVal`, `callStorage`, `callMem`); a loop by its invariant under the box (`ProvesC.invBox`, the body's frame read over its callback runs, `ExecP.frame`); `tests/solc/CallbackCalls.sol`.  Not open but refused: a diamond over a loop whose body calls back never holds, the loop's callback runs including a divergence (`ExecS.loopDiverge`, `holdsC_diamond_loop`), whatever its bound, invariant or variant |
| a loop body containing a `try` (no frame: `whileClose`) | calculus | closed: a `try` is within `nonpayable` when its clauses and a self-call's callee are, writing what its clauses write of the caller's locals (`Stmt.within`, `Stmt.writesAt`; `Stmt.run_frame`, `ExecS.frame` with the callee's havoc under callbacks), so the invariant rules apply, with or without callbacks (`tests/solc/CallbackCalls.sol`, `loopOfTries`); a `catch` that binds the data allocates and stays without a frame |
| clean array tails as part of a contract's invariant (`ValidTail .clean`, O6) in the runner | obligation | closed: a contract every function of which exposes nothing (`Prog.exposesNone`: no array of references shrunk while a storage alias may be held, no recursive call) keeps clean tails from its deployment on (`ReachableBy.cleanTail`, `Typing/CleanTailRun.lean`), and the runner states its plain obligations under the premise (`reading: clean`, `docs/solidity-testing.md`); elsewhere `.solc` |
| closer: nonlinear arithmetic (`ensures \result == n * (n + 1) / 2`) | closer limit, not a semantic gap | closed (lane `open-closer`): `sol_close`'s last alternative adds solkey's `multiply_2_inEq0` of the literal bounds of the atoms of a leaf's products (`sol_close_nonlin`, `Calculus/CloseNonlin.lean`), only where a product of two non-literal integers is left; `tests/solc/Recursion.sol`'s `sum` and `sumThree`, `Examples/Tactics/Recursion.lean` (`triSpec`) |
| closer: quantifier instances at non-literal indices | closer limit, not a semantic gap | closed for a local of the premise's scope (lane `open-abi2`): `allLeftHide` offers the literals and the locals the leaf indexes with (`InstLit.loc`, a position counted from the outermost, `Calculus/AllLeft.lean`), a conjunction of premises split around its `∀`s (`Fml.instRest`); `NarrowNested.abiElementAtParameter` (`xs[i]` at a parameter `i`).  Open: a loop counter, a local pushed after the premise, is not a term of the premise's scope; an invariant states its element's range instead |
| the four `SolcLoopsOpen` functions | search and closer limits, not semantic gaps | open: `pushNoArgs2dLoop` is false under `.solc` tails and holds under `ValidTail .clean` (O6), which the runner now states (the contract exposes nothing, `reading: clean`), but its 43 unrolled pushes run past the search's heartbeats; the others are closer cost (exposed recycled slots, unshared memory terms); `docs/loops.md`, "Open loops lane" (remeasured in lane `open-closer`: 55 s, 57 s, 58 s, 38 s, all four still timeouts) |
| a quotient `x / k` of a parameter left open (constructors and functions alike) | closer | closed: `sol_close`'s arithmetic reads a quotient of a nonnegative dividend as `div` (`Int.tdiv_eq_ediv_of_nonneg`, solkey's `sdiv_axiom`; `Calculus/Close.lean`, `tests/solc/CtorDivision.sol`) |
| narrow leftovers: push arithmetic on a narrow element, whole uses in a conditional of references or a struct constructor's argument, a modifier's reference parameter | elaborator | closed: the appended slot checked (`pushedSlot`), the branches and members shape-checked (`narrowWholeAt?`), a modifier's reference parameter a local at its location (`ModApp.locs`, `rawTyW`); `tests/solc/NarrowNested.sol`, `tests/solc/Modifiers.sol`, `Examples/Tactics/Checked.lean`.  A tuple of references stays refused whatever its types (`elabTuple`) |
| a struct the struct table does not list (a contract's own, or the table's name with other members) | semantics, solc import | closed: a contract's own struct is the table's struct whose name spells its members ("Struct table" below; `contract!{ struct S { … } }`, `Examples/Tactics/OwnStructs.lean`, `tests/solc/OwnStructs.sol`); a struct recursive through an array stays refused, a library's struct its caller cannot see stays a row |
| a public function's memory array of narrow elements: ABI decoding reverts on one out of range | chain fact | closed: the obligation assumes each element in range (`Problem.callPre`, `SolcFun.elemRanges`), and `sol_leaf` instantiates the quantified premise at the literal indices the leaf reads (`allLeftHide`, `Calculus/AllLeft.lean`; `NarrowNested.abiElementInRange`).  A parameter index is offered too (`InstLit.loc`, lane `open-abi2`, `abiElementAtParameter`); a loop counter is not (row above) |
| push arithmetic inside `unchecked` (`small.push() -= 1`, `small.push()--`) | elaborator | closed: the appended slot starts at `0`, so the statement pushes `0 op r` wrapped at the element's width (`r` for `+=`, `0` for `*=`, `r`'s negation modulo `2^N` for `-=`, a signed minimum itself; a literal folded), `r` evaluated once before the push (`elabStmtP`, `Syntax/Elab.lean`; `tests/solc/NarrowNested.sol`) |
| struct constructor calls in the solc import (`S(1, 2)`, `S({a: 1, b: 2})`) | frontend | closed: printed as written (`structConstructorCall`, `Frontend/SolcJson.lean`), which `sol{}` lowers to a fresh memory struct's member writes, narrow members checked (`tests/solc/StructLiterals.sol`); a contract's own struct by its spelled name (below) |
| the narrow shape error names a capture (`mv1`) | elaborator | closed: a reference argument's shape is checked as written, before `hoistCallArgs` captures it (`Examples/Tactics/Checked.lean`) |

## Struct table

**The gap.** Structs are one global, closed table (`Semantics.structDef :
Name → List (Name × Ty)`, `AST.lean`), so a contract can only use a struct
the table already lists under that name with those members; the solc import
refuses any other ("struct `…` is not in the struct table", `readStructs`).
A Lean definition cannot be extended by a later file, so the table cannot
simply grow per contract.

**What reads the table.** `structDef` is read by ~44 modules, nearly all
through a `Ty`-indexed family that has no contract in scope: typed storage
(`SVal`/`SFields`, `Semantics/Storage.lean`: `SVal.struct : SFields (structDef
s) → SVal (.struct s)`), its paths (`Path.field`), defaults (`SVal.dflt`,
fuelled by `rankBound`, terminating by `structDef_rank_lt`), the heap
(`MObj`, `MVal`, `Semantics/Heap.lean`), the memory theory and leaves
(`Theory/Typed/Mem.lean`, `Theory/Typed/Leaves.lean`), `tyHasMapping`
(well-founded on `tyRank`), the structural certificates `Ty.mapFree`
(`mapFreeStructs`) and `Ty.defaultOkS`/`Ty.okDeep` (`defaultOkStructs`),
nodup (`structDef_nodup`, used by `Typing/Fits.lean`,
`Typing/Constructibility.lean`, `Leaves`), the EVM layout (`Evm/Layout.lean`,
rank), and the elaborator (`elabTy`, struct constructors, `structWidths`).
Only the last has `C`.

**Three designs.**

1. *A table per contract* (`C.structs`, as asked first). Every family above
   would take the table as a parameter (`SVal Σ T`, `MObj Σ H R`, `Path Σ T U`,
   `tyRank Σ`, …), and every generic lemma a certificate
   (`Σ.rankOk`, `Σ.nodup`, the `mapFree`/`defaultOk` lists) as a hypothesis,
   checked by `decide` once per `contract!`.  It touches every signature of
   the storage, heap, theory and soundness layers (hundreds of declarations,
   80 files with struct patterns), and the kernel then carries `Σ` in every
   indexed term.  The certificate checks are cheap; the rewrite is not, and
   its risk to checking time (larger indices in every `SVal` cast the
   kernel compares) is real.
2. *Structural types* (`RefTy.struct (name) (fields)`): a struct type carries
   its members, so no table exists; termination is structural, `structRank`
   goes, `mapFree`/`okDeep` become structural.  Nodup is no longer
   automatic (a `Ty` value could repeat a member), so the nodup lemmas need a
   well-formedness hypothesis.  537 struct patterns in 80 files change arity;
   type terms grow (each `Person` carries its members), which every `decide`
   on types and every index comparison pays.
3. *Self-describing names in the one table* (chosen, below): a contract's own
   struct is the table's struct whose *name* spells its members,
   `Pair{a:uint;b:bool}`.  The table gets one more arm, which decodes such a
   name and returns its members only if they pass the table's certificates
   (rank below the struct's, distinct members, the `mapFree`/`okDeep`
   claims); otherwise `[]`, as an unknown name already is.  It is design 2
   with the members kept in the name, so `Ty` and every family, pattern and
   lemma stay as they are; only the certificates' proofs gain an arm, proved
   once and generically from the filter.

**Design 3 in detail.**

- *Encoding* (`structEnc`, `AST.lean`): `S{f₁:T₁;…;fₙ:Tₙ}`, each `Tᵢ` in
  Solidity spelling without spaces, `uint`/`int`/`bool`, a narrow `uint8`
  as written (its width is read back by `structWidths`), a table struct by
  its name, a contract struct by its own encoding, `T[]`, `T[n]`,
  `mapping(K=>V)`.  Two contracts declaring the same members under the same
  name share the type; a struct whose name and members are the global
  table's keeps the plain name, so every existing contract, fixture and
  pin elaborates unchanged.
- *Decoder*: a structural parser over `String.data` with fuel the name's
  length, so the kernel reduces `structDef` on an encoded name (`SVal.dflt`
  and the closers do).
- *Termination*: an encoded name's `structRank` is `min (4 + #'{' + #'[') 16`
  (a nested struct's encoding is a substring with fewer braces, a fixed
  array adds a bracket), and the table returns the members only if their
  `fieldsRank` is below it, so `structDef_rank_lt` holds of the new arm by
  the filter.  `rankBound` (the fuel of the defaults, which must not read a
  name) is the cap, 16 instead of 4: it is fuel, consumed only as deep as
  the type goes.
- *Certificates*: `Ty.mapFree (.struct s)` is `s ∈ mapFreeStructs` or, for
  an encoded name, its members' `mapFree` computed with fuel; the filter
  admits the members only if that claim holds of them, so
  `mapFree_structDef` holds of every name.  `okDeep`/`defaultOkS` admit an
  encoded name, and the filter admits members only if they are `okDeep` and
  distinct, so `struct_okDeep` and `structDef_nodup` hold generically.
- *Elaboration*: `contract!{ struct S { T f; … } … }` declares `S`; the macro
  encodes it (resolving the contract's other structs and enums) and
  `Contract.structs` maps `S` to its encoding for the typed elaborator
  (`elabTy`, struct constructors).  The macro refuses a struct the table's
  filter would empty (a repeated member, `solc`'s own error, or one past the
  rank cap), so a declared struct never silently has no members.
  `Ty.toStr` prints the name before `{`.
- *solc import*: a visible struct that is not the table's under its name is
  printed as a `struct` member of the contract instead of refused.

**Cost.** Known names never reach the new arm, so their kernel reductions
are the same match; `Ty.mapFree` of a listed struct short-circuits.  An
encoded name costs a parse per `structDef` unfolding, linear in the name.
The default fuel grows from 5 to 17 and is consumed only as deep as the type.

**Implemented** (branch `open-structs`).  `AST.lean`: `StructEnc`
(decoder, `widths`), `encRank`/`structRankCap`, `structMapFree`,
`structOk`/`Ty.okDeep` (moved from `Typing/Values.lean`), `encFieldsOk`,
`structDefEnc` and the table's last arm; the certificates are proved once,
generically, through `structDef_rec` (the table's rows by `decide`, a
spelled one from `structDefEnc_ok`), with `propext` only (`all_mem` stands in
for `List.all_eq_true`, which uses `funext`).  `Syntax.lean`:
`Contract.structs`, `Contract.structName?`/`structFields`, `TyEnv` (enums
and structs for `expandMemberTy`), `spellTy`, `expandStructs`.
`Syntax/Elab.lean`: `elabTy`, the struct constructors.
`Frontend/SolcJson.lean`: `readStructs` keeps a struct the table's only when
its members and widths (and its nested structs) are, else names it its own
(`S_<id>` when two visible structs share a name), `ownStructMembers` prints
the `struct` members, and a struct constructor call is printed
(`structConstructorCall`, positional or named).

**Byte and function types as members** (lane `open-left2`).  A member's type
is spelled as written: `bytesN`, `bytes`, `string`, `address` and a function
type (`function(uint)returns(uint)`, `spellFnTy`).  The decoder reads a
`bytesN` as a `uint`, `bytes`/`string` as a `uint[]`, a function type as a
`uint` (`StructEnc.fnRest`), a byte string's mapping key as a `uint` (its
hash); `StructEnc.widths` gives each the rows a local of its type has
(`valueRowsOf`: `h#bytes ↦ 32`, `b[]`/`b[]#bytes`, `name#string`,
`f#function(…)`, `a#address`), so `structWidths` carries them and a member is
read and written as a local of its type (`Examples/Tactics/Bytes.lean` §4,
`tests/solc/Bytes.sol`).  A table struct carries no `address` marker:
`expandStructs` and the solc import compare widths without it, so a
contract's struct of the table's name and members keeps the table's name.
The solc import reads the byte types in a struct check (`tyOf`,
`narrowShape`).  A struct literal's byte-string argument at a `bytesN`
member stays a literal, aligned by the member's write.

**Left out.** A struct recursive through an array stays refused (no finite
rank); structs keep the table's structural identity, so two contracts'
same-named, same-membered structs are one type (solc's are distinct, but no
program can tell them apart in one contract).  A member named like a Lean
keyword (`from`) does not print, as before.  A library's struct that the
calling contract cannot see stays a row (`HiddenStructCaller`).

## Bytes and strings (lane `open-bytes`)

**What solkey does.** Nothing to follow: solkey's `SolidityInfo` gives
`string` KeY's `int` sort (an opaque value) and skips `bytes`/`bytesN`
("not yet supported"); no `.key` file has a `bytes` or `string` sort or
taclet.  The model follows solc (`docs/solc-alignment.md`).

**Design: a representation, not a type.**  A new `PrimTy` (or a byte-string
sort) would change every `PrimTy` match (33 files), `PrimTy.Denote`, the
typed storage and heap, the Theory, the closer and the EVM simulation, and
re-check all of them; nothing in a proof needs a byte to be other than a
small number.  So the types are read as the narrow integers already are
(`narrowTy?`): by the elaborator, onto types the model has.

- `bytesN` is a `uint` of `8N` bits holding the bytes read big-endian: the
  value `uintN(b)` solc's conversion gives (`bytes2 b = "ab"` is `0x6162`).
  On that reading solc's operations are the integer ones: `==`, `<` …
  (lexicographic on bytes is numeric big-endian), `& | ^`, `~` (`2^8N - 1
  -% b`, `narrowWrapNode`), `<<` (modulo `2^8N`, as a narrow `<<` already
  wraps), `>>`; `uintM(b)`/`bytesN(u)` at `M = 8N` are the identity.  What
  differs from `uint8N` is rewritten before the statement is elaborated
  (`bytesPure`, `Syntax/Elab.lean`): `bytesM(b)` of a `bytesN` keeps the
  left bytes (`b >> 8(N-M)`) or pads on the right (`uint8M(b) << 8(M-N)`),
  as does an implicit widening (an assignment, an argument, an operand of
  another size); `b.length` is `N`; `b[i]` is `uint8((b >> 8((N-1) -% i)) %
  256)`, divided by `i < N ? 1 : 0` so an index out of range reverts as an
  array's does (`Storage.checkIndex`: the model reads solc's
  `Panic(0x32)` as a revert, the solkey reading); a string or `hex"…"`
  literal at `bytesN` is its bytes left-aligned (`"a"` at `bytes2` is
  `0x6100`).  Which positions are `bytes` the width tables say, by a
  marker row beside the width: `k#bytes ↦ N` (`Contract.widths`,
  `FunDecl.widths`, a reference local's shape; a value local's is its own
  shape entry), so a `bytes4[]`, a `mapping(bytes32 => …)` and a parameter
  carry it as a `uint8[]` carries its width.
- `bytes` and `string` are `bytes1[]`: a `uint[]` whose elements are 8 bits
  wide (the narrow-element machinery checks pushes and writes), in storage
  and memory alike, `string` the same as `bytes` (solc's packing is storage
  layout, out of scope above).  So `.length`, `b[i]`, `.push(x)`, `.pop()`,
  `delete`, copies between storage and memory, parameters and returns are
  the array ones.  `bytes(s)` and `string(b)` are the identity.  A literal
  at `bytes`/`string` is a fresh memory array of its bytes (`new
  bytes(n)` and its writes); assigned to storage it is copied as a memory
  array is.  `==` on them is not solc's (it needs `keccak256`, a gap above).
  The model is more lenient than solc in what it accepts (`s[i]` and
  `s.length` on a `string`, a `bytes`/`bytes1[]` mix, a hex number of the
  wrong size at `bytesN`): solc refuses those programs before the import,
  and a `sol{}` program that uses them gets the array reading.

**What changes.** No low module: `AST.lean`, `Semantics/`, `Calculus/`,
`Theory/`, `Evm/` and their proofs are untouched, so nothing re-proves and
no kernel term grows.  `Syntax.lean` (the type names, the `hex"…"` and
string literal expressions, the width rows), `Syntax/Elab.lean` (the
markers, `bytesPure`, the literal lowering) and the solc import
(`Frontend/SolcJson.lean`: the elementary types, literals, ABI ranges of a
`bytesN` parameter and a `bytes` parameter's elements) change; everything
above `Syntax.lean` rebuilds once (the usual cost of an elaborator change),
and the elaboration of a program with no bytes pays one more pass over its
expressions that finds no marker.  The EVM compiler (`Evm/`) compiles the
`uint` it is given: a `bytesN` is right-aligned in its slot there, not
solc's left-aligned layout, which is storage layout, out of scope; its
theorems are unchanged.

**Left open, with the reason.**
- `mapping(string => V)`, `mapping(bytes => V)`: landed with the hash
  ("Hashing and the ABI"): the key is `keccak256` of the bytes.
- Revert data (`require(c, "msg")`, `revert("msg")`, `catch Error(string
  memory r)` binding `r`): landed for a self-call's literal reasons
  ("Revert data" below).
- `bytes.concat`, `string.concat`, `abi.*`, `keccak256`: landed
  ("Hashing and the ABI").
- `bytesN`/`bytes` in an external call's signature (`ExtKey`, ABI words: a
  `bytesN` word is left-aligned there).
- `calldata` (lane `open-small`): closed.  A `calldata` parameter (`uint[]
  calldata xs`, `bytes`, `string`, a struct) and a `calldata` local are
  memory ones the body does not write (`calldataCheck`, `Syntax/Elab.lean`;
  the import prints them `memory`, `Frontend/Import.lean`): solc refuses a
  write to calldata, and copies calldata where it is bound to memory (`T
  memory m = xs;`, an argument to a `memory` parameter, a `memory` return),
  which the model's memory binding would share.  So, before the body is
  elaborated, a write through a calldata name or a memory name bound to one
  is refused, as is returning one as `memory` and handing one to a callee's
  `memory` parameter the callee writes: what is left only reads the object,
  where sharing and copying agree.  An array parameter's elements are in
  their ABI range as a memory one's (`elemRanges`).  Slices `b[i:j]` are
  views (lane `open-abi2`), below.  Tests: `tests/solc/Calldata.sol`,
  `Examples/Tactics/Bytes.lean` §5–6.
- Calldata slices `b[i:j]` (lane `open-abi2`): a view of the caller's data,
  as solc reads it, not a copy (a copy is a loop with no invariant, so no
  obligation over it would be proved).  `RawStmt.sliceViews`
  (`Syntax/Elab.lean`, applied by the `contract!` and `sol_raw!` macros to a
  body with a slice, outside `hoist`) rewrites the body: a view is its base
  and its start and end in it, after solc's checks `i <= j <= length` (a
  revert); a bound that is not a literal or the base's length a local
  assigned once.  `t[k]` is `b[o + k]` after `require(o + k < f)` where
  every evaluation of the statement reads it (a checked subtraction that
  underflows past the view where only a branch does: solc's `Panic(0x32)`
  and the model's revert are one outcome), `t.length` is `f - o`, and
  `abi.decode(t, …)` decodes the view in place (`#sliceV`, `ByteSrc`).  A
  slice of a slice adds the offsets.  So reads, lengths and decodings are
  loop-free and proved (`sliceRead`, `sliceOfSlice`, `slicePast`,
  `sliceLength`, `decodeShortView`).  A slice handed to a function,
  hashed, copied, indexed by an expression with an effect, or whose base
  is assigned while it is open is refused (`sliceRefusedName`, reported by
  `calldataCheck`).  The closer is the cost: a read beside a second guard
  on the same length (`require(k + 1 < xs.length)` with the view's own
  check) is past its heartbeats, so `sliceRead` reads `xs[1 + k]`.
- A byte type as a struct member: closed ("Struct table", "Byte and function
  types as members").

**Status.** (updated as slices land)
- Slice 1, `bytesN` in `sol{}`: landed.  `bytesTy?`, `valueRows?`, the
  literal grammar (`"…"`, `hex"…"`, `RawExpr.bytesLit`) in `Syntax.lean`;
  the markers (`shapeUnder` keeps `#` rows, a value local's shape entry,
  `declTyName` for inlined parameters), `bytesOf?`, `bytesPure`,
  `bytesStmt` in `Syntax/Elab.lean`; `Examples/Tactics/Bytes.lean` §1–2.
- Slice 2, `bytes`/`string` in memory and storage: landed (a literal is
  lowered in `hoist`, `exprShape` knows its shape); §3 of the examples.
- Slice 3, the solc import: string and hex literals printed (`"…"` quoted,
  else `hex"…"` from `hexValue`), the elementary types accepted, a `bytesN`
  parameter's ABI range and a `bytes` parameter's elements' ranges
  (`paramRanges`, `elemRanges`), a value parameter's marker
  (`Frontend/Import.lean`, `paramCtx`); `scripts/solc-ast.mjs` keeps a hex
  literal's `hexValue` (a number's stays noise, so no fixture changes);
  `tests/solc/Bytes.sol`, its 12 functions proved.
- A closer limit met on the way, not a byte one: a storage array copied to a
  memory local (`string memory c = name;`) and the copy's length read.
  Closed in lane `open-k2`: the length of a copy of `sfind(s, p)` is
  `len(s, p)` (`lenAtN`, `LTm.sfindLen?`, `SVal.copyStToM_array_len`; Lean
  only), so `tests/solc/Bytes.sol`'s `copyLength` (diamond) and
  `copyLengthSymbolic` are proved.  An element of such a copy
  (`bytes(c)[2]`) is still not read back: `copyFieldRd?` reads a struct
  member of a copy of storage, not an array element.
- The examples on memory close with `sol_decide`, not `sol_close`.
- Checked (2026-10-20): `lean_build` of the default targets; the solc suite
  (`node --test scripts/test-solidity.test.mjs`) fails 6 tests that fail
  alike on `c23bb098`, before this lane (`PushReceiver`, `PushSources`,
  `MemoryPush`, `StorageReturns`, `PushBindings`, the TestSuite's row count
  617 against the pinned 551); `OmittedTypes.readsString` moved from
  `unsupported` to `pending` (the copy above).

## Hashing and the ABI (lane `open-hash`)

**What solkey does.** Nothing to follow: no `.key` file has a hash or an
ABI symbol, and solkey's `docs/limitations.md` lists `keccak256`, `abi.*`
among what it refuses (`No KeYSolidityType for bytes32`).  The model
follows solc.

**`keccak256` is Keccak-256 of the bytes** (lane `open-k2`).  It is
`keccakBytes : List Int → uint` (`Semantics/Heap.lean`), defined from
`Keccak.keccak256Nat` (`Keccak.lean`, the hash the elaborator folds
selectors with, written so that the kernel evaluates it: lanes as `Nat`s,
structural recursion only), applied to a memory array's elements
(`Heap.keccak`, `MObj.words`).  It is `@[irreducible]`: the closers and
`simp` read a hash as an atom, a function of its bytes, and never start
computing one; a proof that wants the hash of literal bytes evaluates it in
the kernel (`decide +kernel`, under a second for one block:
`Examples/Tactics/Hashing.lean`, `keccakAbc`).  `#run` computes the real
hash, so `bytes4(keccak256("f(uint256)"))` is `this.f.selector` (`Sel`; the
elaborator reads `keccak256(…)` as a `bytes32`, `bytesOf?`, so `bytes4(…)`
keeps its high bytes).  In the
syntax it is `Val.hash .keccak` (`Syntax/Scoped.lean`), in the signature the
binary symbol `Op2.hash .keccak : mem × ident R → val uint` (`Signature.lean`),
read in the Theory as the typed evaluation (the memory island, as `size`
is: `Op2.denote`), its rule the Lean-only `LeanTaclet.hashAssignment`
(`v = hash(mpath)` is `{ v := hash(memory, mpath) }`), sound by
`sound_setLocal` and `Val.lower_evalT`; the EVM compiler leaves it out of
its fragment (`valIn`).  The elaborator lowers `keccak256(b)`
(`Syntax/Elab.lean`, `hoist`): `b` a memory `bytes`/`string` (a storage one
copied first), the hash into a fresh `bytes32`.

*Collision resistance is not assumed.*  It cannot be stated as injectivity
(a function from all byte strings into `2^256` values has collisions, so
`∀ a b, keccak a = keccak b → a = b` is false and would make every claim
vacuous).  A proof that needs two particular symbolic inputs to hash apart
takes `keccakBytes a ≠ keccakBytes b` as a premise, for those two; two
literal inputs it may hash by evaluation instead.  So the closers prove what
holds for every function of the bytes: two different strings may land on
one slot of a string-keyed mapping, as two colliding strings would in solc.
Soundness does not rest on the hash being Keccak (an argument for every
function of the bytes holds for this one); the real function only adds the
facts evaluation gives.

**The closers.**  `keccak256(memory, b)` is total (`Op2.total`): an
identity that names no object hashes `0`, which no program reads.
`sol_decide` reads a hash as an atom compared by its terms; `sol_close` by
its object (`Grown.keccakId`, carried past local, storage and ledger updates:
`CloseS.Landed.keccakId_eq`, `withStorage_keccakId`, …).  So one byte string
hashed twice is one value, and a string parameter's hash is the same before
and after storage writes (`tests/solc/Hashing.sol`, `hashParameter`,
`stringKey`).  Under `⟨⟩`, a hash of a byte string the function built (a
literal, an encoding) is read off the memory (lane `open-closer`):
`sol_decide`'s memory pass reads the object's length (`lenAtN`) and each of
its bytes (`memReadN`) down the writes, and where all are literals (at most
`keccakMaxBytes`, 64) the hash is `keccakBytes` of them, which the kernel
evaluates (`keccakAt`, `keccakAt_eval`, `Calculus/MemRead.lean`, Lean only;
`orElse` the symbol where the memory does not return).  So the hash returns
under the diamond, two allocations of the same literal bytes hash equal, and
a hash compares with its literal value (`tests/solc/Hashing.sol`,
`equalStringsHashEqual` now under `⟨⟩`, `literalHash`,
`twoAllocationsHashEqual`; `Examples/Tactics/Hashing.lean`,
`hashTwiceDiamond`, `abcHash`, `twoAllocations`).  A byte string with a
symbolic byte or length keeps its hash an atom.  The clause is at every hashing builtin (`Op2.hash k`, `HashKind.apply`):
`sha256` and `ripemd160` of a literal string built here close under `⟨⟩`
too (`sha256Literal`, `ripemd160Literal`; `sha256AbcDiamond`,
`ripemd160TwiceDiamond`).

**`mapping(string => V)`, `mapping(bytes => V)`** is a `mapping(uint => V)`
with the marker row `{}#hash` (`hashKeyRows`, `Syntax.lean`); `m[s]` is read
`m[keccak256(bytes(s))]` before the statement (`bytesPure`).  solc's slot is
`keccak256(s . p)`, storage layout, out of scope; the model keys by the
hash of the bytes, the same up to the hash.

**The ABI** (`abiEncode`, `abiDecodeAt`, `Syntax/Elab.lean`) is Solidity's
semantics, computed into a fresh memory `bytes` with the array writes the
model has (`new bytes(n)`, then each byte; a byte string's bytes copied by a
loop):
- `abi.encode(v₁, …)`: a 32-byte head per argument; a value type its word
  big-endian (`uintN`/`address`/enum right-aligned, `intN` sign-extended,
  `bool` `0`/`1`, `bytesN` left-aligned); a `bytes`/`string` its offset in
  the head, its length and its bytes, padded to 32, in the tail.
- `abi.encodePacked(…)`, `bytes.concat(…)`, `string.concat(…)`: each value
  at its own width, a byte string's bytes bare.  An `address` packs at 20
  bytes and an enum at one: both are `uint`s to the model, told apart by a
  marker row beside the width (`addressRows`, `enumRows`: `a#address ↦ 20`,
  `e#enum ↦ 1`, which `sameShape` ignores), read before the arguments are
  captured (`abiMarks`, `markOf?`); `msg.sender` and `address(this)` are
  addresses, an enum's member and conversion enums (the solc import prints
  a member packed as `E(n)`).
- An array of values and a struct of values (lane `open-left2`): `abi.encode`
  writes a `T[]` as an offset in the head and its length and elements' words
  in the tail (a loop over the elements), a `T[n]` and a struct of value
  members as their words in the head; `abi.encodePacked` writes an array's
  elements each in a word, with no length, and refuses a struct, as solc
  does.  An element's kind is read off the array's rows (`AbiKind.ofValue`).
- `abi.encodeWithSelector(s, …)`, `abi.encodeWithSignature(sig, …)`,
  `abi.encodeCall(g, (…))`: the selector's four bytes, then `abi.encode(…)`
  of the rest (`abiEncode`'s `sel`).  A selector is folded at elaboration as
  solc folds it, the first four bytes of the Keccak-256 of the canonical
  signature (`Keccak.lean`, checked against solc's `evm.methodIdentifiers`):
  a literal signature's, and `g`'s for a function of the contract, its
  signature read off its parameters' markers (`fnSignature?`: `address`,
  `bytesN`, `string`/`bytes`, an enum `uint8`, a struct as its members'
  tuple, a function type `function`).  A signature that is not a literal is
  hashed at run time: the first four bytes of its `keccak256`, the same
  function, so the two agree (`#run`; a proof evaluates a literal's hash).
- `abi.decode(d, (T, …))` of value types: `d` at least `32·n` bytes, each
  word read back; a word out of `T`'s range reverts as solc's decoder does
  (a high byte not `0`, or not the sign's, a `bool` above `1`).  A `bytes`
  or a `string` (lane `open-left2`, `abiDecodeBytes`): the offset its head
  word holds, the length there, the bytes after it copied into a fresh
  memory `bytes`, an offset or a length past the data reverting.
A value is read at its static type (`AbiKind`, `abiKind`).

**Costs.**  `Val`, `Op2` and the Lean rules have one constructor more:
every `casesOn` over them one arm more, and the `#replay_toStep`/
`#replay_ruleExists` plans grew with it (`storageIndexWriteCaptureAllNonSimpleIndex`
1800 → 1922 goals).  An encoding is a statement per byte: symbolic proofs
over 32-byte words are slow (`abi.decode` of two words took minutes and
the closer's bounds), so `Examples/Tactics/Hashing.lean` runs the decoder
(`#run`) and proves the layouts of small encodings.

**Left open.**
- `abi.decode` of arrays and structs: closed (lane `open-small`).  `sol{}`
  writes `T[]` where a type stands in an expression (`solArrTyExpr`,
  `RawExpr.name "uint[]"`), `T[k]` and a struct by name as before, and a
  tuple declaration's reference components without a location (the import
  prints them so, `abiTyText`); `abiDecodeWith` (`Syntax/Elab.lean`, outside
  `hoist`'s `mutual` block) reads a struct of values and a `T[k]` off their
  words in the head (`AbiKind.headWords`: a component sits at the word its
  predecessors leave, `abiDecodeHeads`), a member or an element each, a word
  out of its type's range reverting (`abiDecodeAt`), and a `T[]` off its
  offset, its length there and its elements' words after it, read by a loop
  into `new T[](length)`, an offset or a length past the data reverting as
  solc's decoder does.  Tests: `tests/solc/Hashing.sol` (`decodeStruct`,
  `decodeFixed`, `decodeTuple`, proved), `Examples/Tactics/Hashing.lean`
  (`Codec2`: an array, a struct, a `T[k]`, a tuple, a bad `bool`, a bad
  length, run).  An array decoded is a loop with no invariant: the runner
  proves no obligation over it (as for an array encoded).
- Nested types: closed (lane `open-abi2`, below).
- An array encoded or a byte string decoded is a loop over its elements:
  the runner proves no such obligation (no invariant), so they are run
  (`Codec2`, `Examples/Tactics/Hashing.lean`).  `abi.encodePacked` of a
  symbolic word writes its bytes as `(a >> 8k) % 256`; the closer reads a
  byte back (lane `open-closer`: `x >> 0` as `x`, `(t % m) % n` and
  `((t % 2^m) >> j) % 2^w` narrowed, `bitsShr`/`bitsMod`; a `uint`'s shift
  and remainder by a positive literal return, `Facts.arithOk`) and
  reassembles bytes read by Horner's rule, `r * 256 + b`, to the word modulo
  their width (`hornerU?`, Lean only: KeY has no byte layout;
  `tests/solc/Hashing.sol`, `packedAddressBytes`, `packedWordReassembled`
  for a `uint64`).  An `address`'s twenty bytes reassembled are past the
  closer's bounds (`Seq.closeSize`, 24000 nodes: each `r` repeats the reads
  of the twenty-write memory), eight are within them.
- `abi.encodeCall` of a function this contract does not declare (an
  interface's): its signature is not known to `sol{}`.
- `sha256`, `ripemd160`, `ecrecover`: closed (lane `open-small`, below).

**Nested types** (lane `open-abi2`).  `abi.encode` and `abi.decode` of an
array of references (`uint[][]`, `bytes[]`, `S[]`), of a struct with a
reference member (a `uint[]`, a `bytes`, a struct) and of a fixed array of
either follow the ABI specification's `enc`, head and tail recursively: a
dynamic component is an offset in its tuple's head, from the tuple's
start, and its encoding in the tail; a static one its words in the head;
an array its length and then the tuple of its elements.  `AbiTy`
(`Syntax/Elab.lean`) is the type read off a place's `Ty` and its rows
(`AbiTy.of`), or off the type written in `abi.decode` (`abiTyExpr?`,
`T[][]` in `sol{}`: `solArrTyExpr2`); the writer computes the size first
(`abiSizeGen`), allocates, and writes (`abiTupleWriteGen`, a loop per
sequence), the reader allocates each reference and checks each word it
reads within the data (`abiReadGen`, `abiWordAt`), an offset or a length
past it reverting.  Both are functions outside `hoist`'s `mutual` block,
`abiEncode` handing over where an argument is not flat
(`abiEncodeNested?`), `abiDecodeWith` where `decodeKind?` has no kind
(`abiDecodeTy?`); the flat cases stay the flat encoder's.  A decoded
calldata slice is read in place (`ByteSrc`).  Tests:
`Examples/Tactics/Hashing.lean` (`Codec3`: `[[1, 2], [3]]`, a struct with
a `uint[]` and a `bytes` member, a `bytes[]`, their round trips, a tuple
with a nested array, a bad length, run against solc's bytes; a static
nested struct proved, `staticNested`), `tests/solc/Hashing.sol`
(`encodeStaticNested` proved; `encodeNested`, `encodeDynStruct`,
`decodeNested`, `decodeDynStruct` elaborate, and the walk unrolls their
loops past its budget, no invariant).  `abi.encodePacked` of a nested type
stays refused, as solc refuses it.

**`sha256`, `ripemd160`, `ecrecover`** (lane `open-small`).  One symbol for
every hash: `Val.hash k`, `Op2.hash k` and the rule `hashAssignment`, the kind
`k : HashKind` (`AST.lean`) a parameter, not a constructor each, so no fold
grows an arm; `keccak256` is `k = .keccak`.  `HashKind.apply`
(`Semantics/Heap.lean`) is the function of the bytes: `sha256` SHA-256 and
`ripemd160` RIPEMD-160 (`Hashes.lean`, written as `Keccak.lean` is, over
`Nat`s with structural recursion only, checked against the standard
vectors; `sha256Bytes`, `ripemd160Bytes` `@[irreducible]`, evaluated in the
kernel by `decide +kernel` and by `#run`), `ripemd160`'s value a `bytes20`
(below `2^160`).  `ecrecover(h, v, r, s)` is lowered to `abi.encode(h, v, r,
s)`, the precompile's 128 bytes, then the hash `.ecrecover` into an
`address` (`hoistHashWith`, `Syntax/Elab.lean`): `ecrecoverBytes` is `0`
where the precompile fails (`v` not `27` or `28`, `r` or `s` outside
`[1, n)` for secp256k1's order `n`), as solc returns the zero address, and
otherwise `ecrecoverKey h v r s mod 2^160`, an `opaque` function: no proof
unfolds it, so what is proved holds of every recovery function (no axiom);
`#run` evaluates it to `0`.  Assumed: nothing about which address a valid
signature recovers to (it may be `0`, as the point at infinity is on the
EVM).  Tests: `tests/solc/Hashing.sol` (`sha256Parameter`,
`ripemd160Parameter`, `recoverSigner`), `Examples/Tactics/Hashing.lean`
(`sha256Abc`, `ripemd160Abc`, `recoverBadV`, the runs, `sha256Twice`).
Cost: `Val`, `Op2` and the Lean rules keep their constructor counts; every
match on `keccak` gained the kind (`.hash _ b _`).  The lowering is a
function outside `hoist`'s `mutual` block, handed the recursive calls.
(Lane `open-refret` split that block: its large arms, `hoist`,
`abiEncode`, `elabCallRet`, `hoistStmt`, `elabStmtP` and `elabStmt1`, are
defined before it, each over the record of the block's functions
(`ElabRec`, tied by `elabRec`); the block went from about 190k heartbeats,
most of them its compilation as one unit, to under 55k, and the largest arm,
`elabCallRetWith`, takes under 90k on its own.)

**Lane `open-left2` checked** (2026-10-21): `tests/solc/Hashing.sol`'s
`encodeWithSignature`, `encodeWithSelector`, `encodeCall`, `packedEnum`,
`encodeStruct` proved; `Codec2` runs (`Examples/Tactics/Hashing.lean`).

**Checked** (2026-10-21): `lean_build` of the default targets;
`node --test --test-name-pattern="hash|bytes|solc/open"
scripts/test-solidity.test.mjs` passes (4 tests); `tests/solc/Hashing.sol`'s
seven functions proved, `decodeRoundtrip` (one `bool` word) in 30 s, the
others in 1–3 s.

## Function types (lane `open-fntypes`)

**What solkey does.** Nothing to follow: solkey's `SolidityInfo` has no
function type.  The model follows solc (`docs/solc-alignment.md`).

**Design: a tag and a dispatch, by the elaborator.**  The internal
functions a contract can name are finite and known at elaboration, so a
value of an internal function type is a `uint`, the *tag* of a function: its
position in `Contract.funs`, from `1`; `0`, the default, is unassigned.  As
for `bytesN`, no low module changes (`AST.lean`, `Semantics/`, `Calculus/`,
`Theory/`, `Evm/` and their proofs are untouched): the type is a spelling
read by the elaborator onto `uint`.

- `function (uint) pure returns (uint)` is a `sol_ty` (`solFnTy`,
  `Syntax.lean`) spelled `function(uint)returns(uint)` (`fnTyStr`; the
  mutability dropped, `external` kept); a position of that type carries a
  marker row beside its width, `k#function(uint)returns(uint) ↦ 0`
  (`valueRows?`), in `Contract.widths`, `FunDecl.widths` and a value local's
  shape entry, as a `bytesN` carries `k#bytes`.
- A function named as a value is its tag (`fnTag`, in `synth`).  So
  assignment, a parameter, a return, storage, a ternary, `delete` (the tag
  `0`) and `==`/`!=` (the same function, the same tag) are the `uint` ones.
- A call `h(a)` through a name of a function type (a local, a parameter, a
  state variable: `fnTyOf?`) is a dispatch over the contract's functions of
  `h`'s signature (`FunDecl.sigTy?`, compared after `canonFnTy`: `uint256`,
  `address` and an enum are `uint`): `if (h == 1) { r = g₁(a); } else if …
  else { revert(); }` (`fnDispatch`, `Syntax/Elab.lean`), each branch an
  ordinary inlined call, the arguments that are not pure captured first.
  Calling an unassigned value is solc's `Panic(0x51)`; the model reads it as
  a revert, as it reads an index out of range's `Panic(0x32)`, so a box
  obligation holds over it and a diamond does not.
- **Which functions a dispatch lists.**  Calls are inlined, and a function
  may call only those declared before it, so the dispatch inside a function
  lists the functions of the signature declared before it.  One declared
  after it that the contract names as a value somewhere (`fnTaken`) could be
  reached, and is refused ("declare the functions of type … first").  One
  that the contract never names as a value could only get a tag from a
  `sol{ … }` program outside the contract: `fnTag` refuses that value when a
  function declared before it calls through a value (`fnReachable`), so a
  dispatch never leaves out a reachable function.  The solc import orders
  the members so: a function after those it names as values, and a function
  that calls through a value after every function named as a value
  (`callsOf`, `Frontend/SolcJson.lean`).
- A struct member of a function type is its tag, a `uint` with its marker:
  the struct spells the type (`spellTy`, "Struct table"), so `hold.f(x)`
  dispatches as a local of the type does.
- The solc import prints a `FunctionTypeName` (`tyText`) and a function
  named as a value by its (renamed) name.

**What changes.** `Syntax.lean` (the type's grammar and spelling,
`fnParts?`, `canonFnTy`, the marker rows), `Syntax/Elab.lean` (`fnTag`,
`fnTyOf?`, `fnDispatch`, a callee's local renamed in a call's head too:
`RawExpr.rename`), `Frontend/SolcJson.lean`.  The elaboration of a program
with no function value pays one lookup per call of a name that is not a
function.

**Closed in lane `open-left2`.**
- *A call through a value that is not a name* (`s.f(x)`, `fs[i](x)`,
  `choose(b)(x)`): `sol{}` writes it `#callValue(callee, args…)`
  (`callValueName`; `choose(b)(x)` by its own grammar rule, `solCallCall`),
  and the elaborator evaluates the callee first into a fresh local of its
  function type (`fnTyOfExpr`: a struct member's or an element's marker, a
  call's return's), then calls that local as a name (`callValue`).  A
  struct's member now keeps its type's marker (the struct spells it,
  "Struct table").  The import prints such a callee as an operand
  (`isValueCallee`), a call's value parenthesised.
- *External function types*: a value is an address and a selector, packed
  as the ABI's `bytes24` packs them, `address * 2^32 + selector`, a `uint`
  (`fnPure`).  `this.g` and `r.g` for a function `g` of the contract are
  `r * 2^32 + selector(g)`, the selector folded by Keccak-256 as solc folds
  it (`fnSelector?`, "Hashing and the ABI"); `h.address` is `h / 2^32`,
  `h.selector` `h - h / 2^32 * 2^32`, `this.g.selector` the literal.  A call
  `h(a)` is an external call to `h.address` (`Stmt.tryCall`, every failure
  reverting the caller as a call outside a `try` does), dispatched on the
  selector over the contract's functions of `h`'s type (`extDispatch`), so
  that a call to `this` of one declared before the caller runs it (O8);
  any other selector is a call the model names `#selector`, the selector its
  first argument, whose response the world picks as for any external call.
  `r.g(a)` in an expression (`this.g(a)` too) is such an external call
  (`extCallStmt`).  The model's checks: `Examples/Tactics/FunctionTypes.lean`
  §3 runs them (`viaThis(3)` is `6` through the self-call) and pins the
  signature of a function of every marked type against solc's selector.
  The closer reads `(address(this) * 2^32 + s) / 2^32` back to
  `address(this)` (`Facts.cancelDiv`, Lean only: `(a * k + c) / k` is `a` at
  `uint` for literals `0 ≤ c < k` where the sum returns), so
  `ExternalFunctionTypes.externalValue` is proved, under the box (lane
  `open-k2`; the call through `h` is a `try`, which has no diamond rule: it
  was pending under the default diamond before the quotient was read).
- *A dispatch that recurses*: a call through a value is a call of each
  function it may reach (`FunDecl.valueCallees`: the functions of the
  callee's type a value may name, every function named as a value where the
  type is not known), so a function that reaches itself through a value is
  recursive (`isRecursiveC`, `recPartnersC`), its calls and the dispatch's
  candidates among its partners `Stmt.callRec`'s ("Recursion",
  `docs/kernel-port.md`).  As every dispatch of a type lists every function
  of it named as a value, one recursive such function makes every dispatch
  of the type recursive (`tests/solc/FunctionTypes.sol` keeps it in a
  contract of its own).

**Left open, with the reason.**
- A value of an external function the contract does not declare (`I(a).g`
  of an interface): its signature, hence its selector, is unknown to
  `sol{}`; the import prints the member as written, which elaborates only
  for the contract's own functions.
- Reference parameters or returns in a function type (`function (uint[]
  memory)`): refused (`fnCompTy?`, the import's `tyText`).
- A closer limit met on the way, not a function-type one: a stored value
  chosen by a flag and called at a symbolic argument
  (`op(x)` after `if (b) op = double; else op = triple;`) times out in the
  runner's search; at a literal argument it is proved (`storedByFlag`).


## Revert data (lane `open-revert`)

**What solkey does.** Nothing to follow: solkey's `try` rule
(`tryCallNoCallbackBox`) binds no data in its `catch` goals, and a revert
is a halt with no payload.  The model follows solc.

**Solidity's semantics.**  A revert returns data: `require(c)` and
`revert()` none; `require(c, "m")` and `revert("m")`
`abi.encodeWithSelector(0x08c379a0, "m")` (`Error(string)`); a panic
`Panic(uint256)` (`0x4e487b71`) and its code; `revert E(a, b)` `E`'s
selector and `abi.encode(a, b)`.  `catch Error(string memory r)` runs when
the data has `Error`'s selector and decodes, `r` the decoded string;
`catch Panic(uint c)` likewise; `catch (bytes memory d)` with the raw data;
`catch { }` with nothing.

**Design.**
- *The run.*  `THalt` gains `revertWith (d : List UInt8)`: a revert with
  data; `revert` is the empty one (`THalt.ofData` keeps `revertWith []` out).
  A new statement `Stmt.revertData parts` reverts with its data, the parts
  literal bytes, a custom error's selector (`errorSelector`, uninterpreted
  per signature) or an ABI word of a value; its rules are `revert`'s
  (`revertDataBox`: `true`, `revertDataDiamond`: `false`, Lean only).  The
  modalities read no data: a box accepts every revert, a diamond none.
  `ExtResult.error` and `.other` carry the reason and the data an external
  callee returns.
- *Where data is computed.*  Neither modality reads a top-level revert's
  data, so the elaborator emits `Stmt.revertData` only where a `try` can
  read it: in the callee a self-call `try` runs (`trySelfBody`, the
  elaborator's `selfFrame`), and its calls.  Elsewhere `require(c, "m")`,
  `revert("m")`, `revert E(a)` stay `require(c)`/`revert()` as before, so
  no other proof changes shape.
- *Dispatch.*  A self-call whose callee reverts goes to `catch Error` when
  its data decodes as `Error(string)`, to `catch Panic` when it decodes as
  `Panic(uint256)` (the code bound), to the catch-all otherwise (empty data
  included); the transaction's table no longer chooses (it did, before:
  the model kept no data).  An external call's outcome is the table's.
- *Binding.*  `Stmt.tryCall`'s shape does not change.  A named `Error`
  reason or catch-all data is bound by a new block statement
  `Stmt.catchData call … kind x body` that the elaborator writes as the
  clause's body: it reads the data the call would revert with, from the
  state the `try` started in (the callee's run again, deterministic, for a
  self-call; the table's entry otherwise), allocates it as a memory
  `bytes`/`string` (decoded for `Error`), binds `x` and runs `body`, its
  locals popped.  Since the clause runs from that same state, the binding is
  the data of the very call that failed.
- *The calculus.*  `catchDataBox` (Lean only): for a self-call, the data a
  callee can revert with is read off its body when every `revertData` in
  it is literal (`Prog.revertDatas`, an over-approximation, sound by
  `Prog.run_dataIn`, an induction over the run as `Semantics/NoPanic.lean`'s);
  one goal per possible datum, `require(a == address(this));` and the
  string literal's allocation in front of `body`; and the other receiver's
  goal is the clause for every fresh `bytes` of any contents (`Fml.allocAll`,
  lane `open-alloc`, below; it was `false` before).  Under the box
  only (`catchDataDiamond` is `false`), and without callbacks: with a
  callee that may call back, the `ProvesC` rule is `false`.
- *Panic codes.*  `THalt.panic` keeps no code: the model panics on a failed
  `assert` (`0x01`) and on an overflow inside `checked { … }` (solc's
  `0x11`, read as an assertion, `docs/options.md` O2); division by zero
  (`0x12`), an enum out of range (`0x21`), an index out of range (`0x32`),
  a too-large allocation (`0x41`) and an unset function value (`0x51`)
  revert in the model (the solkey reading).  A self-call's `Panic` clause
  binds the table's code, `1` without one, as before; its rule's goal is
  behind the codes its callee's data carries (`Prog.panicCodes`,
  `docs/options.md` O8, "The `Panic` goal per code").

**Expected cost.**  Two `Stmt` constructors (every statement fold, the
rule table, the soundness dispatch, the callback reading, the printers and
quoters gain an arm, as `assumeFalse` did), one `THalt` constructor (every
case split over a halt: few, most proofs are generic in the halt), the
self-call `try` dispatch in `TRun.tryCall` and its soundness
(`Premise.sound_trySelfBox`, `holdsC_trySelfCb`).  No proof over an
existing program changes shape: data is computed only in self-call
callees.

**Status.** (updated as slices land)
- Slice 1, the run and the calculus: landed.  `THalt.revertWith`,
  `ExtResult.error`/`.other` payloads, `Semantics/RevertData.lean` (the
  `Error`/`Panic` encodings and decoders, `customSelector`),
  `Stmt.revertData`, `Stmt.catchData` (`TRun.catchBytes`,
  `TRun.litBytesT`), the self-call dispatch on the data (`TRun.tryCall`),
  the rules `revertDataBox`/`revertDataDiamond`/`catchDataBox`/
  `catchDataDiamond` (`catchDataStep`, `Stmt.revertDatas`), sound by
  `sound_revertData` and `Premise.sound_catchDataBox`
  (`Calculus/SoundCatch.lean`, from `Prog.run_dataS`,
  `Calculus/DataIn.lean`); every run lemma, typing invariant, callback
  reading (`ExecS.catchDataHalt`/`catchDataBody`, the self-call `try`
  constructors now read the callee's data) and the EVM proof carry the two
  statements.  `stmt_sim` stays within its 11000 heartbeats: the statements
  outside the fragment are ruled out by one lemma (`stmt_sim_outside`).
- Slice 2, the elaborator: landed.  `require(c, "m")` and `revert("m")`
  are `RawStmt.requireMsg`/`revertMsg`: `require(c)`/`revert()` as before,
  but in a self-call's callee (`ElabScope.selfFrame`) `if (c) { } else {
  revert(d); }` with `d` `Error(m)`'s encoding (`RevertBytes.lean`, below the
  syntax so the elaborator writes it).  `catch Error(string memory r)` and
  `catch (bytes memory d)` with a name: the macro writes a marker
  declaration first (`catch$reason`, `catch$data`), which the `try`'s
  elaboration turns into `Stmt.catchData` (`RawStmt.catchBinder?`,
  `Blk.toCatchData`); a missing `Error` or `Panic` clause is the catch-all's
  block, its binder with it (raw data).
- Slice 3, the calculus's goals as the walks read them: one goal per raw
  datum the callee lists (`catchLit` decodes it), so the list is literal
  after `List.map`/`++` are flattened, which the walks do for
  `catchDataBox` only (`ProofTree.flattenLemmas`), leaving every other
  printed walk as it was.
- Examples: `Examples/Tactics/RevertData.lean` (`boomReason`: the reason of
  `require(false, "boom")` bound to `r`, its four bytes proved; two reasons;
  raw data; the run on a concrete state), `tests/solc/RevertData.sol`
  (three functions proved).

**Custom errors** (lane `open-k2`): landed.  `error E(uint8 a, address b);`
is kept as a declaration of its parameters (`Contract.errors`, a `FunDecl`
with no body, its width rows the markers a signature is read from).
`revert E(a, b)` and `require(c, E(a))` are `RawStmt.revertErr`/
`requireErr`: as before where no `try` reads the data (`revert();`,
`RawStmt.requireWith`), and in a self-call's callee `Stmt.revertData` with
`E`'s selector folded as solc folds it (`errorSignature?`, the canonical
signature off the markers, `revertErrParts`; `customSelector` is the
Keccak-256 one, `RevertBytes.lean`), then each argument's ABI word, a
literal's folded to its bytes so that `Stmt.revertDatas` reads the datum.
The solc import prints the `ErrorDefinition`s, the contract's and the
file's (`errorMembers`), and a `RevertStatement` as `revert E(…)`.  Tests:
`tests/solc/RevertData.sol` `customSelector` (`F()`'s four bytes) and
`customData` (`E(7)`: the selector `0x002ff067` and the word, 36 bytes, read
through `catch (bytes memory d)`), `Examples/Tactics/RevertData.lean`
(`customData`, the run of `require(x > 3, E(x))`).

**Lane `open-alloc`: any bytes, and data known in part.**

- *The binder.*  `Fml.allocAll x R φ` (`Calculus/Fml.lean`, Lean only):
  `φ` for every fresh memory object `x : R` of any contents, read in the
  state the heap grown by it (`holds σ (allocAll x R φ) ↔ ∀ o : MObj σ.H R,
  holds ((σ.alloc o).1.push (some (σ.alloc o).2)) φ`; `holdsC` alike).  The
  hidden binder at a memory type (`Fml.bind`) ranges over the references
  of the heap the state has, so it could not say this; `allocAll` grows the
  heap itself, so no heap-extension invariance is asked of any formula.
  Printed `∀ fresh bytes x; φ`, refused when written (`dl{}` reads it as
  `{ havoc }`: a rule's goal, not a formula to write).
- *The sequent.*  `Hyps.allocAll` and the rule `Proves.allocIntro`
  (KeY's `allRight` over a fresh object), sound by the context's wrapping
  as `allIntro` is; the walk (`Seq.runK`), the tree, `sol_derive?` take it
  (`allocRight`).  The premise `Premise.allocBranches bs x A P gs`: the
  blocks `bs` (`branches`' goals) and, for each `(Q, h)` of `gs`,
  `Fml.allocGoal`: after the `require`s `Q`, `P` for every fresh `x` of
  which `h` holds (`⟨ Q ⟩ ∀ fresh x. h → ⟨ P ⟩ …`); `Proves.allocBranches`.
- *The rule.*  `catchDataStep` under the box: a self-call whose callee's
  data are known gives a goal per literal datum (as before), one per datum
  known in part (`Pat`: each byte known or not; a custom error's argument
  is 32 unknown bytes, `RevPart.pat?`), the clause for every fresh `bytes`
  of the pattern's length and known bytes (`Pat.fml`, a raw clause; an
  `Error` clause assumes nothing), behind `require(a == address(this))`,
  and the any-bytes goal behind `require(a != 0); require(a !=
  address(this));`.  Another contract's call, or a callee whose data are not
  known (a recursive call, a selector not folded, a panic's code), gives
  the any-bytes goal behind `require(a != 0);` alone.
- *The analysis.*  `Stmt.revertDatas raw : Option DSet`: literal data and
  patterns (`DSet.Mem`, `Pat.Matches`), sound by `Prog.run_dataS` as
  before (`TRun.revertData_dataS_pat`).
- *Soundness.*  The run allocates a datum as `litBytes` does (`new
  bytes(n)`, a write per byte); `TRun.litBytesT_alloc`
  (`Semantics/AllocBytes.lean`) shows it ends in the state `allocAll` reads
  at the object of the bytes, so the any-bytes goal and the pattern goals
  give the clause (`catch_alloc_sound`, `Pat.fml_holds`).  A datum of
  `2^256` bytes or more is bound by no clause: `CatchKind.decode` returns
  none there (no transaction carries it), the clause not reached.
- *The closers.*  `sol_decide` reads `allocAll` as `false` at a goal and
  `true` at a premise (`Fml.toLS`): a goal behind `require(a != address(this))`
  with `a` the contract closes, as before.  `sol_close` reads it
  semantically (`CloseS.holds_allocAll`): the object `o` a variable, its
  length `lenU o.1.length` (`CloseS.alloc_lenId`), its words `o.1[i]?`
  (`CloseS.alloc_readId_index`), every other read the state's
  (`CloseS.locV_alloc`, `alloc_storage`, …).
- *Tests.*  `tests/solc/RevertData.sol`: `externalReason` (another
  contract's reason, its length branched on), `externalData` (raw data),
  `customSymbolic` (`require(x > 3, E(x))`'s data known in part, its
  length); `Examples/Tactics/RevertData.lean`: `externalReason`,
  `symbolicCustom`, the rule pinned.
- *Cost.*  `Fml`, `Hyps` and `Premise` have one constructor more: every
  fold gained an arm (about 60 sites, mostly the `anon` arm copied).
  Checking times did not move beyond noise: opened in the language server
  before and after, `Examples/Tactics/TryCatch.lean` 9 s / 6 s,
  `Examples/Tactics/Decide.lean` 15 s / 15 s; the build's slow modules
  (`Memory`, `CallbackStrategy`, `Recursion`) within run-to-run noise.
  `Examples/Tactics/RevertData.lean` went from 30 s to 47 s for its new
  examples (`symbolicCustom` walks three clauses × four goals).  Checked
  (2026-10-21): `lean_build` of the default targets; `node --test
  --test-name-pattern="revert|self|solc/open"` passes (4 tests).

**Left open, with the reason.**
- A reason that is not a literal (`revert(string.concat("x", s))`, a
  rethrown `catch (bytes memory d) { revert(d); }` in a self-call's
  callee).  Re-examined in lane `open-memret`, not implemented; what it
  takes, layer by layer:
  1. *Syntax.* `sol{}` refuses a reason that is not a literal ("a string
     literal", `Syntax.lean`'s `solRequireMsg`), and `RevPart` (`Syntax/Scoped.lean`) has
     literal bytes, a selector and a word only.  A `RevPart.mem (x : Idx Γ
     (.mem .bytes))` — the bytes of a memory local at the revert — is one
     constructor of `Stmt`'s data, so every fold over `Stmt` gains an arm
     (`Stmt.within*`, `writesAt`, the printers, `Stmt.run`'s halt).
  2. *Run.* The halted run would carry those bytes, read off the callee's
     heap as it halts; the heap itself is discarded, so the data must be
     copied out as values (`THalt.revertWith` carries bytes already).
  3. *Calculus.* The `try`'s rule (`catchDataBox`, `Calculus/Blocks.lean`)
     enumerates the callee's data statically (`Stmt.revertDatas`, a `Pat`
     per `revert`); a computed datum has no pattern, so the clause would
     bind it as any bytes (`Fml.allocAll`), the any-bytes goal of today.
     To prove facts about it the caller's goal needs a term for what the
     callee halts with, and no formula reads a halt's data: `[·]` and `⟨·⟩`
     read normal outcomes only.  The reading needed is a third modality,
     `[s]ʳ(d. φ)`: every run of `s` that reverts does so with data `d`
     such that `φ`, `φ` read in the state the callee reverts in (its
     memory, so `d`'s bytes are `string.concat("x", s)`'s); the `try`'s
     rule then splits the callee into `[body] success` and
     `[body]ʳ(d. clause)`.  This is a new `Fml` constructor with a rule for
     every statement (solkey has no taclet to transcribe: KeY's Solidity
     calculus reads no revert data) and a soundness case for each; the
     `{grow}` reading of this lane (`Fml.grow`) carries the heap the
     callee leaves, but a revert leaves none.
  The cost is the obstacle: `Fml.grow` added one constructor and about
  forty fold arms (`Derived15`'s near-limit replay re-checked under it); a
  revert modality is that plus a rule per statement, so it is its own lane.
- A fresh object's bytes read in the clause cost `sol_close` past its
  heartbeats when the premises read bytes too (`symbolicCustom` reads the
  length); `sol_decide` does not read `allocAll` (it would need an atom of
  an object's contents in `LTm`/`AEnv`).  Measured (lane `open-closer`,
  2026-10-21): `symbolicCustom` with `d[3] == 0x67` added to its clause
  closes by `sol_close` leaf by leaf, 5k, 85k and 43k heartbeats on each of
  its three clause goals (nine leaves, about 400k in all) against one
  declaration's 200k; the runner reports the same obligation (`customSymbolicByte`)
  as a timeout at `whnf` after 15 s.  The atom is not added: `LTm` and
  `AEnv` are the reflective closer's language, so an object-contents atom
  is a constructor more in every fold and soundness proof of `Calculus/`
  (`toLS`, `elimF`, `memRes`, `close`), and the leaves' cost in the
  kernel-checked closer (`Derived15`'s near-limit replay among them) would
  have to be measured anew; out of this lane's reach.
- The callback reading: an `allocAll` goal whose rest may call back has
  no `ProvesC` rule (`Calculus/Callback.lean` gives none); where nothing
  calls back the walk goes on by `ProvesC.plain`.
- `Panic` data (lane `open-small`): in the callee a self-call `try` runs, a
  failed `assert` reverts with `Panic(0x01)`'s data and a failed check in
  `checked { … }` with `Panic(0x11)`'s (`elabStmt1`'s `assert`,
  `OFMode.guardStmt` with `self`), solc's codes; the `try` dispatches on the
  data, so `catch Panic(uint c)` binds the code in the run, and the data are
  literal to `Stmt.revertDatas`, so a raw `catch (bytes memory d)` gets them
  (`tests/solc/RevertData.sol` `panicData`, `Examples/Tactics/RevertData.lean`
  `Panics`).  A callee that still may panic (an `assert` written in a
  program not elaborated as a self-call's callee) lists `Pat.panic`, the
  selector then a word of unknown bytes (`CatchKind.datas`, sound by
  `Pat.matches_panic`), where it had only the any-bytes goal.  Closed
  (lane `open-refret`): the rule's `Panic` goal is behind the codes the
  callee's data carries (`trySelfStep`, `CodeBinder.guard`:
  `require(a != address(this) || c == 1);`), sound over `Prog.run_dataS`
  and with callbacks (`holdsC_trySelfCb`, a callee that pays nobody), so
  `catch Panic(uint c)` proves `c == 1` (`RevertData.lean`'s `assertCode`,
  `overflowCode`); `docs/options.md` O8.  The other
  codes (`0x12` division, `0x21` enum, `0x32` index, `0x41` allocation,
  `0x51` function value) and an overflow outside `checked { … }` are reverts
  in the model, with no data (the solkey reading).
- A raw datum always includes the empty one (an evaluator's revert), so a
  `catch (bytes memory d)` goal holds for `d` empty too.
- The callback reading (`ValidT`): `catchData` forks when its callee or
  body may call back (`ExecS.catchDataBody` binds any data then); its leaves
  do not close a memory array's length (a limit of the callback closer, met
  by any memory program), so the solc test's callees are `pure`.
- Error data larger than the closer's bounds: `Error("boom")`'s 100 raw
  bytes written as literals pass `sol_decide`'s bounds (`boomData` is the
  empty case).

**Costs.**  `Stmt` has two constructors more, `THalt` one: every statement
fold, run lemma, typing invariant and callback lemma gained an arm, and
`stmt_sim` stays within its pinned 11000 heartbeats only because the
statements outside the EVM fragment are now ruled out by one lemma.  The
self-call `try`'s callee is copied once more per named clause (`catchData`
carries it); the rule's goals add one literal allocation (a statement per
byte of the decoded reason).  Programs with no named clause and no
self-call reason elaborate as before.

**Checked** (2026-10-21): `lean_build` of the default targets;
`node --test --test-name-pattern="revert|self|callbacks|solc/open"
scripts/test-solidity.test.mjs` passes (5 tests, 271 s); `tests/solc/RevertData.sol`'s
three functions proved (4 s); `Examples/Tactics/RevertData.lean`'s proofs by
`sol_symex; sol_decide`.  A named `catch` reason the clause does not read
binds nothing, so no existing program changes.

**Lane `open-k2` checked** (2026-10-21): `lean_build` of the default
targets; `node --test --test-name-pattern="hash|revert|function types|bytes|self|solc/open"
scripts/test-solidity.test.mjs` passes (7 tests).  Landed: Keccak-256 as
`keccakBytes` ("Hashing and the ABI"), custom error data and the import's
`RevertStatement` ("Revert data"), `catch Error` past a custom error of
symbolic data, `Facts.cancelDiv` ("Function types"), a storage array copy's
length ("Bytes and strings").

**Lane `open-closer` checked** (2026-10-21): `lean_build` of the default
targets; `node --test --test-name-pattern="recursion|hash|revert|bytes|solc/open"
scripts/test-solidity.test.mjs` passes (6 tests, 680 s).  Landed: products
of bounded integers by solkey's `multiply_2_inEq0` (`sol_close_nonlin`,
`Recursion.sol`'s `sum`, `sumThree`); a symbolic word's packed bytes read
back and reassembled (`hornerU?`, `Facts.arithOk` on `uint` shifts,
remainders and products, `Facts.modSmall`; "Hashing and the ABI"); a
locally built byte string's hash evaluated under `⟨⟩` (`keccakAt`).  Left
open with their numbers: a fresh object's bytes ("Revert data"), the four
`SolcLoopsOpen` functions (`docs/loops.md`).  `TestSuite/Derived15`'s
`invariantVariantSkipsBreakIteration` replay: 200045 heartbeats (in units
of `maxHeartbeats`) before and after, its 205000 override unchanged.

**Lane `open-small` checked** (2026-10-21): `lean_build` of the default
targets; `node --test --test-name-pattern="calldata|hash|revert|loop|callbacks|solc/open"
scripts/test-solidity.test.mjs` passes (7 tests).  Landed: a `try`'s loop
frame ("Open"), `sha256`/`ripemd160`/`ecrecover` and `abi.decode` of arrays
and structs ("Hashing and the ABI"), `calldata` ("Bytes and strings"),
`Panic` data in self-call callees ("Revert data").
