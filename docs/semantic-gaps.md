# Semantic gaps

What of Solidity's semantics the model leaves open, and the design of the
types the elaborator reads onto the model's own (structs, bytes, hashes and
the ABI, function types, revert data). A program that uses a gap is refused
by the elaborator or the solc import (an `unsupported` row); a claim the model
cannot prove is `pending` with a reason (`scripts/test-solidity.test.mjs`
pins them).

Per-feature status against the pinned language is the
[feature inventory](solidity-feature-inventory.md); what is deliberately out
of scope (assembly, gas, raw calldata, logs, block fields other than
`block.timestamp`, storage layout) is [solidity-scope.md](solidity-scope.md),
"What is deliberately outside this profile". Where the run follows solc over
KeY is `docs/solc-alignment.md`.

## Chain facts, as premises

Functional correctness is proved of a deployed contract called by a
transaction, so what every such call guarantees is a premise of the
obligation (`Problem.callPre`, `Frontend/Problems.lean`), not something to
prove: a non-payable function's `msg.value == 0`, a payable one's
`msg.value < 2^128` where its body reads `msg.value` (the total ether supply
is below `2^128` wei; `etherBound`, also in the specified obligation,
`Calculus/SurfaceSpec.lean`), a parameter and each element of a memory array
parameter in its ABI range (`SolcFun.elemRanges`), `address(this) < 2^160`
([source-inputs.md](source-inputs.md)), `address(this)` at a harness address
when the test pins one (`--self-address`). Address `0` has no code
(`docs/solc-alignment.md`, `try`). Bounds that hold of every reachable state
belong in the contract's invariant. A fact about the chain is stated where a
proof uses it, never derived from a machine model.

## Open

- **Revert data in formulas.** No formula reads the data a run halts with:
  a computed or rethrown reason is bound as any byte string (`Fml.allocAll`).
  Reading it needs a third modality over revert outcomes, with no solkey
  taclet to follow ("Revert data", "Left open").
- **Callbacks.** A diamond over a loop whose body calls back never holds
  (`holdsC_diamond_loop`, `docs/options.md` O3): refused, not open. An
  `allocAll` goal whose rest calls back has no `ProvesC` rule; the callback
  closer does not close a memory array's length.
- **Recursion** (`docs/kernel-port.md`, "Recursion"): a memory return whose
  body writes its own objects under the callback reading, a memory
  parameter, a length past an element write in the closer.
- **Closer and search cost.** `SolcLoopsOpen`'s `pushNoArgs2dLoop` (holds
  under `ValidTail .clean`, O6, but its 43 unrolled pushes exceed the search
  budget) and `multiArrayFillByPushLoops` (recycled-slot handling;
  `docs/loops.md`). An array's length after an element write under `{grow}`;
  a fresh object's bytes under `allocAll` (about 400k heartbeats against a
  declaration's 200k, "Revert data"); quantified memory reads at loop
  counters (`Calculus/CloseAll.lean` covers numeric locals and typed
  projections only); an `address`'s 20 bytes reassembled (past
  `Seq.closeSize`; eight bytes are within it); a stored function value
  chosen by a flag and called at a symbolic argument (times out; at a
  literal it is proved, `storedByFlag`).
- **Loops without invariants.** An array encoded, a byte string or an array
  decoded and every nested ABI encoding are loops the runner has no
  invariant for, so it proves no obligation over them; they are run.
- **Nonlinear arithmetic** is instance-based (`Calculus/CloseNonlin.lean`,
  `Examples/Tactics/Nonlinear.lean`), not a decision procedure.
- **Function types**: reference parameters or returns (`fnCompTy?`); a value
  of an external function this contract does not declare (`I(a).g`), and
  `abi.encodeCall` of one: its signature is unknown to `sol{}`.
- **Bytes**: `bytesN`/`bytes` in an external call's signature (`ExtKey`); an
  element of a memory copy of a storage array (`bytes(c)[2]`) is not read
  back (`copyFieldRd?` reads struct members only).
- **Calldata slices**: reference-element and nominal-element materialization
  ([calldata-slice-copies.md](calldata-slice-copies.md)).
- **Structs**: one recursive through an array (no finite rank;
  [feature-work/recursive-types.md](feature-work/recursive-types.md) has the
  checked foundation); a library's struct its caller cannot see
  (`HiddenStructCaller`).
- **Tuples**: several nonlocal targets and reference-return tuples
  (`elabTuple`, [feature-work/aggregates.md](feature-work/aggregates.md)).
- **Panic data**: the allocation code `0x41` is never emitted; outside a
  self-call's callee every panic is a revert with no data.
- **`ecrecover`**: no general proof of the curve arithmetic or of equivalence
  to the precompile ([feature-work/abi-hashes.md](feature-work/abi-hashes.md)).

## Closed

Each has focused fixtures in `tests/solc/` and `Examples/Tactics/`.

- Recursion: `Stmt.callRec`, unrolled to 1024 frames, proved by contract
  (`rec_auto`, `rec_auto_c`; `docs/kernel-port.md`, "Recursion").
- Self-call `catch` goals assume `fails(call)` (`notLeft`, O8); a value call
  to `this` runs `receive` (`elabValueCall`); `callKeepsStorageUnsound` stays
  pending, false on the EVM.
- Literal types in `c ? 63 : 255` (`mobileTy`); narrow types inside types
  (`expandStateTyW`, `structWidths`, `shapeCheck`); signed wrap in
  `unchecked`; `type(T).max`/`min` (`typeBoundExpr`); narrow operations under
  `&&`/`||` and ternaries (`hoist`); push arithmetic on narrow elements
  (`pushedSlot`, `elabStmtP`): `docs/solc-alignment.md`, "Narrow integer
  types".
- `super` and base constructors (`readContract`; `docs/solc-alignment.md`,
  "Constructors").
- Bytes, strings, hashes, the ABI, function types, revert data, structs not
  in the table: the sections below.
- Callbacks: recursion (`ProvesC.recContract`, `RecContractCM`), captures
  (`ProvesC.capture`), calls returning values or references
  (`ProvesC.callVal`), loop invariants (`ProvesC.invBox`): O3.
- A `try` in a loop body has a frame (`Stmt.within`, `Stmt.run_frame`).
- Clean tails as a contract invariant in the runner (`Prog.exposesNone`,
  `ReachableBy.cleanTail`; O6, [solidity-testing.md](solidity-testing.md)).
- A quotient of a nonnegative dividend is `div` (`Int.tdiv_eq_ediv_of_nonneg`,
  solkey's `sdiv_axiom`).
- `binomialFaithfulRowsSmall` and `binomialRowsNine` (`sol_prove (chunk :=
  128)`; `docs/loops.md`, [assurance.md](assurance.md) M13).

## Struct table

Structs are one global, closed table (`Semantics.structDef : Name → List
(Name × Ty)`, `AST.lean`), read by ~44 modules through `Ty`-indexed families
with no contract in scope (typed storage and heap, paths, defaults fuelled by
`rankBound`, the Theory, `tyHasMapping`, the certificates `Ty.mapFree` and
`Ty.okDeep`, `structDef_nodup`, the EVM layout). A Lean definition cannot be
extended by a later file, so the table cannot grow per contract.

**Design: self-describing names.** A contract's own struct is the table's
struct whose *name* spells its members, `Pair{a:uint;b:bool}`. The table's
last arm decodes such a name and returns its members only if they pass the
table's certificates (rank below the struct's, distinct members, `mapFree`,
`okDeep`); otherwise `[]`, as for an unknown name. So `Ty` and every family,
pattern and lemma stay as they are. Rejected: a table per contract (every
family takes `Σ` and every lemma a certificate: hundreds of declarations in
80 files, and `Σ` in every kernel index), and structural types
(`RefTy.struct name fields`: 537 struct patterns change arity, type terms
grow in every `decide`, nodup needs a hypothesis).

- *Encoding* (`StructEnc`, `AST.lean`): `S{f₁:T₁;…;fₙ:Tₙ}`, each `Tᵢ` in
  Solidity spelling without spaces, a narrow type as written (its width read
  back by `structWidths`), a table struct by its name, a contract struct by
  its own encoding, `T[]`, `T[n]`, `mapping(K=>V)`. Same name and members in
  two contracts is one type; a struct matching the global table keeps the
  plain name, so existing contracts elaborate unchanged.
- *Decoder*: structural over `String.data`, fuel the name's length, so the
  kernel reduces `structDef` on an encoded name.
- *Termination*: an encoded name's rank is `min (4 + #'{' + #'[') 16`
  (`encRank`, `structRankCap`); the arm admits members only if their rank is
  below it, so `structDef_rank_lt` holds by the filter. `rankBound` is 16.
- *Certificates* are proved once, generically, through `structDef_rec`
  (`structDefEnc_ok`), with `propext` only.
- *Elaboration*: `contract!{ struct S { T f; … } … }` encodes `S`
  (`Contract.structs`, `expandStructs`, `spellTy`); the macro refuses a struct
  the filter would empty (a repeated member, past the rank cap).
- *solc import*: `readStructs` keeps the table's name only when members and
  widths agree, else prints the struct as a contract member (`S_<id>` when two
  visible structs share a name).

**Cost.** Known names never reach the new arm. An encoded name costs a parse
per `structDef` unfolding, linear in the name; the default fuel is 17, consumed
only as deep as the type.

**Byte and function types as members.** A member's type is spelled as written
(`bytesN`, `bytes`, `string`, `address`, `function(uint)returns(uint)`,
`spellFnTy`). The decoder reads a `bytesN` as `uint`, `bytes`/`string` as
`uint[]`, a function type as `uint` (`StructEnc.fnRest`); `StructEnc.widths`
gives each the marker rows a local of its type has (`valueRowsOf`), so a
member is read and written as a local of its type. A table struct carries no
`address` marker: widths are compared without it.

**Left out.** Structs keep the table's structural identity (two contracts'
same-named, same-membered structs are one type; no program in one contract
can tell). A member named like a Lean keyword (`from`) does not print.

## Bytes and strings

solkey gives `string` an opaque `int` and skips `bytes`/`bytesN`; the model
follows solc.

**Design: a representation, not a type.** A new `PrimTy` would change every
`PrimTy` match (33 files), the typed storage and heap, the Theory, the closer
and the EVM simulation; no proof needs a byte to be other than a small
number. So the types are read as the narrow integers are, by the elaborator,
onto types the model has. No low module changed (`AST.lean`, `Semantics/`,
`Calculus/`, `Theory/`, `Evm/`); a program with no bytes pays one pass that
finds no marker.

- `bytesN` is a `uint` of `8N` bits holding the bytes big-endian (`uintN(b)`;
  `bytes2 b = "ab"` is `0x6162`). solc's operations are then the integer ones
  (`==`, `<`, `& | ^`, `~` as `2^8N - 1 -% b`, `<<` modulo `2^8N`, `>>`).
  What differs is rewritten before the statement (`bytesPure`):
  `bytesM(b)` keeps the left bytes or pads on the right, as an implicit
  widening does; `b.length` is `N`; `b[i]` is
  `uint8((b >> 8((N-1) -% i)) % 256)`, divided by `i < N ? 1 : 0` so an
  index out of range reverts as an array's does; a literal at `bytesN` is
  left-aligned. A marker row beside the width says which positions are bytes
  (`k#bytes ↦ N`, `valueRows?`).
- `bytes` and `string` are `bytes1[]`: a `uint[]` of 8-bit elements in
  storage and memory alike (solc's packing is layout, out of scope).
  `.length`, `b[i]`, `push`, `pop`, `delete`, copies, parameters and returns
  are the array ones; `bytes(s)`/`string(b)` the identity; a literal a fresh
  memory array. The model accepts more than solc (`s[i]` on a `string`, a
  `bytes`/`bytes1[]` mix); solc refuses those before the import.
- The EVM compiler right-aligns a `bytesN` in its slot, not solc's layout;
  its theorems are unchanged.
- **`calldata`** parameters and locals are memory ones the body does not
  write (`calldataCheck`; the import keeps the location, `Frontend/Import.lean`):
  a write through a calldata name or a memory name bound to one is refused, as
  is returning one as `memory` or passing one to a callee's `memory` parameter
  the callee writes. What is left only reads, where sharing and copying agree.
  Slices `b[i:j]` are views (`RawStmt.sliceViews`) with primitive copies where
  a whole value is needed: [calldata-slice-copies.md](calldata-slice-copies.md).
- A storage array copied to memory keeps its length: `len` of a copy of
  `sfind(s, p)` is `len(s, p)` (`lenAtN`, `LTm.sfindLen?`,
  `SVal.copyStToM_array_len`; Lean only).
- Inline arrays and reference tuples:
  [feature-work/aggregates.md](feature-work/aggregates.md).

## Hashing and the ABI

No `.key` file has a hash or an ABI symbol; the model follows solc.

**`keccak256` is Keccak-256 of the bytes**: `keccakBytes : List Int → uint`
(`Semantics/Heap.lean`) from `Keccak.keccak256Nat` (`Keccak.lean`, written so
the kernel evaluates it: `Nat` lanes, structural recursion), applied to a
memory array's elements (`HashKind.apply`, `MObj.words`). It is
`@[irreducible]`: closers and `simp` read a hash as an atom; a proof that
wants a literal's hash evaluates it (`decide +kernel`, under a second per
block, `keccakAbc`). `#run` computes it, so
`bytes4(keccak256("f(uint256)"))` is `this.f.selector`. In the syntax it is
`Val.hash .keccak`, in the signature `Op2.hash .keccak : mem × ident R → val
uint`, its rule the Lean-only `LeanTaclet.hashAssignment`, sound by
`sound_setLocal` and `Val.lower_evalT`; the EVM compiler leaves it out
(`valIn`). One symbol serves every hash: the kind `k : HashKind` is a
parameter, so no fold grows an arm.

*Collision resistance is not assumed.* Injectivity is false of any function
from all byte strings into `2^256` values and would make every claim vacuous.
A proof that needs two symbolic inputs to hash apart takes
`keccakBytes a ≠ keccakBytes b` as a premise; two literals it may evaluate.
Soundness does not rest on the hash being Keccak.

**The closers.** The hash is total (`Op2.total`: an identity naming no object
hashes `0`, which no program reads). `sol_decide` reads it as an atom compared
by its terms; `sol_close` by its object, carried past local, storage and
ledger updates, so one byte string hashed twice is one value. Under `⟨⟩`, a
hash of a byte string the function built is read off the memory: length
(`lenAtN`) and bytes (`memReadN`) down the writes, and where all are literals
(at most `keccakMaxBytes`, 64) the kernel evaluates it (`keccakAt`,
`Calculus/MemRead.lean`, Lean only). A symbolic byte or length keeps the atom.
The same clause serves `sha256` and `ripemd160`.

**`mapping(string => V)`, `mapping(bytes => V)`** is a `mapping(uint => V)`
with the marker `{}#hash` (`hashKeyRows`); `m[s]` reads
`m[keccak256(bytes(s))]`. solc's slot is `keccak256(s . p)`, layout, out of
scope.

**The ABI** (`abiEncode`, `abiDecodeAt`, `Syntax/Elab.lean`) is computed into
a fresh memory `bytes` with the array writes the model has:

- `abi.encode`: a 32-byte head per argument (`uintN`/`address`/enum
  right-aligned, `intN` sign-extended, `bool` `0`/`1`, `bytesN` left-aligned);
  a dynamic argument's offset in the head, its encoding in the tail; arrays
  and structs of values; nested types head and tail recursively (`AbiTy`,
  `abiSizeGen`, `abiTupleWriteGen`, `abiReadGen`).
- `abi.encodePacked`, `bytes.concat`, `string.concat`: each value at its own
  width, an `address` at 20 bytes and an enum at one (markers `a#address`,
  `e#enum`, which `sameShape` ignores); a struct or nested type refused, as
  solc does.
- `abi.encodeWithSelector`/`encodeWithSignature`/`encodeCall`: the selector
  folded at elaboration as solc folds it (`fnSignature?`, checked against
  solc's `evm.methodIdentifiers`); a non-literal signature is hashed at run
  time, the same function.
- `abi.decode` at value types, `bytes`/`string`, `T[]`, `T[k]`, structs and
  nested types: a word out of range, an offset or a length past the data
  reverts as solc's decoder does. A decoded calldata slice is read in place
  (`ByteSrc`).

**`sha256`, `ripemd160`, `ecrecover`.** `Hashes.lean` computes SHA-256 and
RIPEMD-160 as `Keccak.lean` does, checked against standard vectors.
`ecrecover(h, v, r, s)` hashes `abi.encode(h, v, r, s)` (`hoistHashWith`):
`0` where the precompile fails (`v` not 27/28, `r` or `s` outside `[1, n)`),
otherwise the address recovered by `Secp256k1.lean` through the irreducible
`ecrecoverKey`; high-s accepted. No authorization or injectivity premise is
inferred.

**Cost.** An encoding is a statement per byte, so symbolic proofs over 32-byte
words are slow; examples run the codec (`#run`) and prove small layouts. The
lowering functions live outside `hoist`'s `mutual` block, handed the
recursive calls (`ElabRec`, `elabRec`): the block went from about 190k
heartbeats to under 55k. Keep new large arms outside it.

## Function types

solkey has no function type; the model follows solc.

**Design: a tag and a dispatch, by the elaborator.** A contract's internal
functions are finite and known at elaboration, so a value of an internal
function type is a `uint`, its function's position in `Contract.funs` from
`1`; `0`, the default, is unassigned. As for bytes, no low module changes.

- The type is spelled `function(uint)returns(uint)` (`fnTyStr`, mutability
  dropped, `external` kept) and carries a marker row beside its width.
- A function named as a value is its tag (`fnTag`); assignment, storage,
  `delete` and `==` are the `uint` ones.
- A call `h(a)` through a value is a dispatch over the contract's functions
  of `h`'s signature (`fnDispatch`, compared after `canonFnTy`), each branch
  an inlined call, ending in a revert: solc's `Panic(0x51)` for an unassigned
  value, read as a revert.
- **Which functions a dispatch lists.** A function calls only those declared
  before it, so the dispatch lists those. One declared after that the contract
  names as a value (`fnTaken`) is refused ("declare the functions of type …
  first"); `fnTag` refuses a value of a later function when an earlier one
  calls through a value (`fnReachable`). The solc import orders members so
  (`callsOf`).
- A callee that is not a name (`s.f(x)`, `fs[i](x)`, `choose(b)(x)`) is
  evaluated into a fresh local first (`callValueName`, `fnTyOfExpr`).
- **External function types**: an address and a selector packed as the
  ABI's `bytes24`, `address * 2^32 + selector` (`fnPure`, `fnSelector?`);
  `h.address`, `h.selector` the quotient and remainder. A call is an external
  call dispatched on the selector over the contract's functions
  (`extDispatch`), so a call to `this` runs the callee (O8); any other selector
  is the world's. The closer reads `(address(this) * 2^32 + s) / 2^32` back
  (`Facts.cancelDiv`, Lean only).
- **Recursion through values**: a call through a value calls every function it
  may reach (`FunDecl.valueCallees`), so recursion through a value is
  recursion (`isRecursiveC`, `recPartnersC`); one recursive function of a type
  makes every dispatch of that type recursive.

## Revert data

solkey's `try` rule binds no data and a revert has no payload; the model
follows solc.

**Solidity's semantics.** `require(c, "m")`/`revert("m")` revert with
`Error(string)` (`0x08c379a0`); a panic with `Panic(uint256)` (`0x4e487b71`)
and its code; `revert E(a, b)` with `E`'s selector and `abi.encode(a, b)`.
`catch Error(string memory r)` runs when the data decodes as `Error`,
`catch Panic(uint c)` likewise, `catch (bytes memory d)` with the raw data.

**Design.**
- *The run.* `THalt.revertWith d` is a revert with data (`THalt.ofData` keeps
  `revertWith []` out); `Stmt.revertData parts` reverts with literal bytes, a
  custom error's selector or an ABI word of a value, by `revert`'s rules
  (`revertDataBox`, `revertDataDiamond`). The modalities read no data.
  `ExtResult.error`/`.other` carry another callee's reason and data.
- *Where data is computed.* Since no modality reads a top-level revert's
  data, literal and custom-error data are emitted only in the callee a
  self-call `try` runs (`selfFrame`) and its calls; elsewhere
  `require(c, "m")` is `require(c)`, so no other proof changes shape.
  Computed memory operands keep their bytes everywhere (`RevPart.mem`,
  `Semantics/RevertMemory.lean`); the importer accepts the whole-buffer
  rethrow `assembly { revert(add(d, 32), mload(d)) }` and no other assembly.
- *Dispatch.* A self-call reverting goes to `catch Error` when its data decodes
  as `Error(string)`, to `catch Panic` as `Panic(uint256)`, to the catch-all
  otherwise; another contract's outcome is the transaction table's.
- *Binding.* `Stmt.catchData` (the clause's body as the elaborator writes it)
  reads the data the call would revert with from the state the `try` started
  in, allocates it as memory `bytes`/`string`, binds the name and runs the
  body: the data of the very call that failed.
- *The calculus.* `catchDataBox` (Lean only, box only, no callbacks): a goal
  per datum the callee's body can revert with (`Stmt.revertDatas`, an
  over-approximation sound by `Prog.run_dataS`), literal or known in part
  (`Pat`: a custom error's argument is 32 unknown bytes), behind
  `require(a == address(this))`, and an any-bytes goal (`Fml.allocAll`) for
  another receiver. `catchDataDiamond` is `false`.
- *`Fml.allocAll x R φ`*: `φ` for every fresh memory object of any contents,
  read in the heap grown by it, so no heap-extension invariance is asked of a
  formula. Printed `∀ fresh bytes x; φ`, not writable in `dl{}`. Its sequent
  rule is `Proves.allocIntro` (KeY's `allRight` over a fresh object).
  `sol_decide` reads it as `false` at a goal and `true` at a premise;
  `sol_close` semantically (`CloseS.holds_allocAll`).
- *Panic codes.* `THalt.panic` keeps no code: the model panics on a failed
  `assert` and on overflow inside `checked { … }` (O2). In a self-call's
  callee every statement is preceded by its checks with their codes
  (`Prog.withPanics`: `0x11`, `0x12`, `0x31`, `0x32`), and enum conversion and
  internal dispatch emit `Panic(0x21)`/`Panic(0x51)`; the `Panic` goal is
  behind the codes the callee's data carry (`trySelfStep`, `CodeBinder.guard`,
  O8), so `catch Panic(uint c)` proves `c == 1` after an `assert`.
- *Custom errors*: `error E(…)` is kept as a body-less `FunDecl`
  (`Contract.errors`); its selector is folded as solc folds it
  (`errorSignature?`, `customSelector`).
- *Operand order* of `require`/`revert` arguments:
  `docs/solc-alignment.md`, "Error arguments and self-call panic payloads".

**Cost.** `Stmt` gained two constructors, `THalt` one, `Fml`/`Hyps`/`Premise`
one each (about 60 fold sites); `stmt_sim` stays within its pinned 11000
heartbeats only because the statements outside the EVM fragment are ruled
out by one lemma (`stmt_sim_outside`). Checking times did not move otherwise.

**Left open.**
- A memory operand has no static pattern (`RevPart.pat?` is `none`), so
  `catchDataBox` binds arbitrary bytes; an exact link between the callee's
  computed data and the catch local needs a proved reading of revert
  outcomes. A revert modality would add a fold case and a rule per statement
  across the calculus; not added.
- A fresh object's bytes read in a clause cost `sol_close` past its budget
  when premises read bytes too (`symbolicCustom` with `d[3] == 0x67`: about
  400k heartbeats against 200k). `sol_decide` would need an object-contents
  atom in `LTm`/`AEnv`, a constructor in every fold and soundness proof of the
  reflective closer; not added.
- A raw datum always includes the empty one (an evaluator's revert), so a
  `catch (bytes memory d)` goal holds for `d` empty too.
- Literal errors outside a self-call frame keep the empty-data lowering.
