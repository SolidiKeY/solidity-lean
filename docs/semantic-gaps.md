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
| recursion (`functionsRecursiveUnbounded`) | semantics, calculus | closed: `Stmt.callRec`, unrolled to the EVM's 1024 frames, proved by contract over the frames (`docs/kernel-port.md`, "Recursion"); the runner proves a recursive call by its callee's `/// @custom:key` contract, else `true`/`true` (`rec_auto`, `tests/solc/Recursion.sol`); several returns to a tuple's targets; a reference return runs but has no contract; under the callback reading (O7) not tried |
| a `catch` goal when the callee cannot fail (`tryCatchExactReturn`) | calculus | closed: each self-call `catch` goal assumes `fails(call)`, the walks prove the callee's diamond instead (`notLeft`; `docs/options.md` O8) |
| a value call to `this` runs `receive` (`callRunsReceive`) | semantics | closed: a self-call `try` of `receive` behind `r == address(this)` (`elabValueCall`, O8); `callKeepsStorageUnsound` stays pending, false on the EVM |
| `msg.value` bounded by the ether supply (`msgValueArith`) | chain fact | closed: `msg.value < 2^128` (`Problem.callPre`) |
| literal types in `c ? 63 : 255` (`ternaryLiteralOverflow`, false on the EVM) | elaborator | closed: solc's mobile type (`mobileTy`); the run reverts (`SolcOpen.ternaryLiteralOverflow` refutes the diamond), the row stays `pending` |
| narrow types inside types (`uint8[]`, `mapping(uint8 => …)`, struct members) | semantics | closed: a state variable's narrow element, key and value (`expandStateTyW`), a struct's narrow member (`structWidths`), a storage alias's, a memory local's and a reference parameter's narrow positions (`LocalTy.shape`, `shapeCheck`), a modifier's narrow parameter (`Checked.lean` §2, `tests/solc/NarrowNested.sol`, `docs/solc-alignment.md`) |
| signed `**` in `unchecked`; `-128 / -1`, `-(-128)` wrap in `unchecked` | semantics | closed: on the words (`narrowWrapNode`, `Examples/Tactics/SignedCasts.lean`), at `int256` too |
| `type(T).max`/`min` in `sol{}` (the import folds them) | elaborator | closed: a value of `T` (`typeBoundExpr`), an enum's members |
| a narrow operation under `&&`/`||` or a ternary branch | elaborator | closed: a conditional capture (`hoist`, `Examples/Tactics/Checked.lean`) |
| `super` calls; base constructor arguments | semantics | closed in the solc import (`readContract`, `Frontend/SolcJson.lean`): `super.f` names the next implementation after its declaration's contract in the most-derived C3 order; the base constructors compose into one constructor in solc's legacy order (`docs/solc-alignment.md`, "Constructors"); a base's contract clauses are inherited; a constructor's modifiers wrap its own body after its bases, and a base's `return` ends its own body (`solcCtorBody<id>`, `tests/solc/InheritanceCtors.sol`); `super` in a modifier's arguments or body names the next implementation after the contract writing it (`SuperMod*`; `super.m` as a modifier name solc refuses); a base's private variable of a later one's name is its own root (`stateRenames`), refused only where a specification names it |
| `bytes`, `string`, `bytesN` (values, storage, memory, `.length`, indexing, `push`, literals, conversions) | semantics: types the model lacks | open |
| `keccak256`, `abi.encode`, `abi.encodePacked`, `abi.decode` | semantics: builtins | open |
| function types (internal function values, `function (uint) returns (uint) f = g;`) | semantics | open |
| revert data: `require(c, "msg")`'s reason, custom errors' arguments, `catch Error(string memory r)` binding `r` | semantics: needs `string`/`bytes` | open (the branch is chosen, the data dropped) |
| recursion under the callback reading (`ValidT`): no contract rule over `ExecS` | calculus | open (`docs/kernel-port.md`, "Recursion") |
| clean array tails as part of a contract's invariant (`ValidTail .clean`, O6) in the runner | obligation | open: an option the runner does not offer |
| closer: nonlinear arithmetic (`ensures \result == n * (n + 1) / 2`), quantifier instances at non-literal indices | closer limits, not semantic gaps | open |
| the four `SolcLoopsOpen` functions | search and closer limits, not semantic gaps | open: `pushNoArgs2dLoop` is false under the default `.solc` tails and holds under `ValidTail .clean` (O6); the others are closer cost (exposed recycled slots, unshared memory terms); `docs/loops.md`, "Open loops lane" |
| a quotient `x / k` of a parameter left open (constructors and functions alike) | closer | closed: `sol_close`'s arithmetic reads a quotient of a nonnegative dividend as `div` (`Int.tdiv_eq_ediv_of_nonneg`, solkey's `sdiv_axiom`; `Calculus/Close.lean`, `tests/solc/CtorDivision.sol`) |
| narrow leftovers: push arithmetic on a narrow element, whole uses in a conditional of references or a struct constructor's argument, a modifier's reference parameter | elaborator | closed: the appended slot checked (`pushedSlot`), the branches and members shape-checked (`narrowWholeAt?`), a modifier's reference parameter a local at its location (`ModApp.locs`, `rawTyW`); `tests/solc/NarrowNested.sol`, `tests/solc/Modifiers.sol`, `Examples/Tactics/Checked.lean`.  A tuple of references stays refused whatever its types (`elabTuple`) |
| a struct the struct table does not list (a contract's own, or the table's name with other members) | semantics, solc import | closed: a contract's own struct is the table's struct whose name spells its members ("Struct table" below; `contract!{ struct S { … } }`, `Examples/Tactics/OwnStructs.lean`, `tests/solc/OwnStructs.sol`); a struct recursive through an array stays refused, a library's struct its caller cannot see stays a row |
| a public function's memory array of narrow elements: ABI decoding reverts on one out of range | chain fact | closed: the obligation assumes each element in range (`Problem.callPre`, `SolcFun.elemRanges`), and `sol_leaf` instantiates the quantified premise at the literal indices the leaf reads (`allLeftHide`, `Calculus/AllLeft.lean`; `NarrowNested.abiElementInRange`).  An index that is not a literal (a parameter, a loop counter) is not offered |
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

**Left out.** A struct recursive through an array stays refused (no finite
rank); structs keep the table's structural identity, so two contracts'
same-named, same-membered structs are one type (solc's are distinct, but no
program can tell them apart in one contract).  A member named like a Lean
keyword (`from`) does not print, as before.  A library's struct that the
calling contract cannot see stays a row (`HiddenStructCaller`).
