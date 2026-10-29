# Source definitions S04.01–S04.03: state, observations, world

The independent source state that S02's expression and statement semantics
and S04.04's transactions run on (roadmap rows S04.01–S04.03 in
[coverage-plan.md](../coverage-plan.md)). Values are intrinsic in S01's
static types (`STy`, [source-s00-s01.md](source-s00-s01.md)); observations
are G01's (`Solidity/Roadmap/Contracts.lean`). Nothing here reads the
compiler, the EVM model or the intrinsic semantics.

## Modules

| Module | Content |
|---|---|
| `Solidity/Source/State.lean` | S04.01: `Layout`, `Val`, `KeyOf`, `Data`/`DataList`, `Heap`, `Calldata`, `Storage`, `Val.default` |
| `Solidity/Source/Observe.lean` | S04.02: ABI words and bytes, decoding, selectors, panic codes, `Panic`/`Error` data, `revertOutcome` |
| `Solidity/Source/World.lean` | S04.03: `Account`, `World`, `Transient`, the journal (`Entry`, `Op`, `ExecState`), `TxConfig`, `CallFrame`, rollback, transfers |
| `Solidity/Source/StateExamples.lean` | Controls on concrete data |

## S04.01: state definitions

Everything is over a `Layout` read off the declaration graph: the field
types of each struct, the size of each enum, the underlying type of each
user-defined value type.

- **Values.** `Val D τ` is a value of type `τ` with its invariants part of
  it. An integer or fixed-point value carries `lo ≤ v ≤ hi`, a `bytesN` its
  length, an enum value is a `Fin` of the enum's size, a user-defined value
  is a value of its underlying type, and an external function's selector
  has four bytes. A reference exists only at a reference type of its own
  location (`STy.loc?`): `memRef` at a `memory` type, `storRef` at a
  `storage` type (mappings included), `cdRef` at a `calldata` type. No value
  type has a reference inhabitant.
- **Aggregates.** `Data D τ` is the contents of a reference type. An array
  is its length (a static array's declared one, by `hl`) and its elements,
  a struct its fields' contents (`DataList D (D.fields d)`), `bytes`/`string`
  their bytes. A mapping is a total function from key *contents* (`KeyOf`:
  the bytes of a `bytes`/`string` key, the value of a value-type key), so
  two copies of one string are one key. Recursive structs through mappings
  and dynamic arrays are allowed, as in solc: the type is inductive over the
  contents.
- **Memory.** `Heap D` maps addresses below `next` to typed contents. An
  element of reference type inside a memory aggregate is `Data.val` of a
  `memRef`, a pointer, so nested aliasing is expressible
  (`StateExamples.alias_seen`). A write is at the object's own type
  (`Heap.write` takes `h.ty a = some τ`) and keeps every object's type
  (`write_ty`). It is seen through its address (`write_get`) and through no
  other (`write_other`). `Heap.copy` allocates a fresh object with the
  source's contents (`copy_get`), and writing the copy leaves the source
  (`copy_independent`).
- **Calldata.** `Calldata D` is the input bytes and the decoded objects.
  It has no write operation, so it is read only by construction.
- **Storage.** `Storage D L` is over a layout `L : SPath → STy` that gives
  each logical path (a state variable and its `Step`s: an index, a field, a
  key's bytes) its declared type. A path holds a value of exactly that type,
  or nothing, which reads as the default (`read_empty`). A write reads back
  (`write_read`) and is invisible through other paths (`write_other`).
  `set_restore` is the undo law the journal uses. G04 Q2 is respected: the
  logical aliasing of storage references is fixed, the physical packing is
  not observable.
- **Defaults.** `Val.default` is zero, `false`, the zero address, zero
  bytes, the first enum member, or the underlying default
  (`IntTy.zero_mem`, `FixTy.zero_mem`).

## S04.02: values and observations

These definitions follow G01 Q5 (revert outcomes are the full revert bytes,
panic codes included) and use the fixed Keccak-256 (`Solidity.Roadmap.Evm.keccakWord`).

- **ABI words.** `Val.word` is a value type's ABI word: two's complement
  for signed integers and fixed point, `bytesN` left-aligned, and
  addresses, enums and contracts right-aligned. A user-defined value takes
  its underlying value's word.
- **Decoding.** `readInt` decodes a word at an integer type, giving `none`
  for a word that is not the sign or zero extension of a value in range, as
  the ABI decoder reverts. `Val.word_int` shows that an integer's word
  decodes to the integer, and `readInt_reject` that `300` does not decode
  at `uint8`.
- **Bytes.** `wordBytes` is a word's 32 big-endian bytes
  (`wordBytes_length`, `wordBytes_value`).
- **Selectors.** `selector` is the first four bytes of a signature's
  Keccak-256 (`selector_length`). The constants `panicSelector`
  (`0x4e487b71`) and `errorSelector` (`0x08c379a0`) are checked against it
  by `#guard`, an evaluation rather than a proof.
- **Panics.** `PanicCode` has solc's ten codes. `panicData` is the revert
  data for a code (36 bytes); the code reads back from it
  (`panicData_code`), so distinct codes give distinct outcomes
  (`panic_distinct`).
- **Errors.** `errorData` is `Error(string)`'s ABI encoding
  (`errorData_prefix`).
- **Outcomes.** `revertOutcome` is the G01 `Outcome` of a revert with those
  bytes.

**Environment observations** (`msg.sender`, `msg.value`, `block.timestamp`,
`this`, external balances) belong to the session environment (G01
`SessionEnv`, `Request`, `Fixed.ledger`). A source semantics reads them and
does not choose them. The other block and transaction members (`block.number`,
`chainid`, `basefee`, `gasleft`, …) are outside the profile and are refused by
S01's `Builtin.status`. The cryptographic precompiles behind `ecrecover`,
`sha256` and `ripemd160` are G01's `Fixed.precompile`. Keccak-256 is
`keccakWord`.

## S04.03: world definitions

- **Accounts and the world.** `Account D L` is one instance of the
  compiled system: its balance, its nonce, its code (the contract's position
  in the compilation input, as G01's `Event.create` names it) and its
  storage over its layout. `World D L` maps each address to an instance.
- **External accounts** are not in the world. Their balances come from
  G01's ledger over the session environment, and their code from
  `SessionEnv.hasCode`, and only events change them, so the two models
  cannot disagree.
- **Transient storage.** `Transient D T` is each instance's transient
  storage over its own layout.
- **Transactions.** `TxConfig` is G01's `Request`; `tx.origin` is its
  sender.
- **The journal.** Every state change is an `Op`: an update of one
  instance's account (its storage, balance or nonce) or of its transient
  storage. `ExecState.apply` records the overwritten account or transient
  storage before changing it, as the EVM's journal does. `undo` restores the
  newest entry, and `undo_apply` shows it inverts one operation.
  `undoN_run` proves, by induction, that undoing as many entries as
  operations restores the start.
- **Frames.** `ExecState.enter` returns a `CallFrame` holding the call's
  `this`, caller, value, input and static flag, plus the journal length at
  entry. `CallFrame.rollback` undoes the journal back to that mark.
  `CallFrame.commit` keeps the state, so an enclosing revert still undoes
  a committed call.
- **Rollback theorems.**
  - `rollback_run`: after any operations since entry, the rollback is the
    entry state, world, transient storage and journal.
  - `rollback_inner`: an inner revert keeps the outer call's earlier
    operations, and an outer revert then returns to the outer entry.
  - `rollback_outer_after_commit`: an outer revert undoes a committed inner
    call.
- **Transfers.** `ExecState.transfer` moves value between two instances as
  two journaled balance updates. It fails exactly when the transfer is
  unaffordable or would overflow (`transfer_none_iff`), and a revert undoes
  it (`rollback_transfer`).
- **End of a transaction.** `ExecState.endTx` clears transient storage and
  the journal and keeps the world (`endTx_world`, `endTx_transient`).

## Controls (`Solidity/Source/StateExamples.lean`)

| Theorem | Statement |
|---|---|
| `alias_seen` | `a = [b]` points to `b`; writing `b` is seen through `b` and leaves `a`'s pointer |
| `copy_independent` | writing a copy of `b` leaves `b` |
| `storage_roundtrip` | a storage write reads back; an unwritten path reads `0` |
| `arith_ne_divZero`, `panic_arith_code`, `error_prefix` | revert data |
| `minusOne_word` | `int8 -1` decodes from its ABI word |
| `transfers` | an unaffordable transfer fails; an affordable one moves both balances |
| `revert_undoes`, `commit_visible` | a reverted call undoes its storage and transient writes; without the revert they are visible |
| `endTx_clears` | transient storage is cleared between transactions, storage kept |

## What S04.01–S04.03 do not do

- **Aggregates in storage.** Storage holds values at typed paths. Loading
  or storing a whole struct or array (`Data` to and from a path tree),
  dynamic array lengths and `push`/`pop`, `delete` of aggregates, and
  dangling references after `pop` are S02/S04.04 operations over these
  paths.
- **Layout well-formedness.** Nothing ties `Layout`, the storage layout
  `L` or `Calldata.objects` to the declaration graph or to the input yet.
  Calldata decoding and slices belong to the ABI work (out of this lane's
  scope).
- **Memory well-formedness.** A pointer's target is not required to have
  the pointer's type, and a nested reference element is not required to be
  a pointer rather than inline contents.
- **Frames.** There is no frame stack, call-depth limit, static-call write
  guard or log list. `enter` does not itself move `msg.value` (a call is
  `transfer` followed by `enter`). A sender's transaction nonce and a
  creator's `CREATE` nonce bump, which survive a revert, must be applied
  before the frame's mark.

## Gates

Recorded in [Handoff](#handoff).

## Review

A read-only finder and skeptic (neither using the Lean server) reviewed the
first version of these modules. The version above is the rework.

The reviews confirmed:

- the ABI word encodings, the panic codes, the selectors, `pad32` and
  `errorData`, including the empty-string case;
- `Val.word_int`, `wordBytes_value`, `panicData_code`, `panic_distinct` and
  the transfer lemma.

Fixed:

| Finding | Fix |
|---|---|
| references inhabited every type, value types included, so "in range by construction" was false (both reviews) | `memRef`/`storRef`/`cdRef` require `τ.loc?` to be their location |
| mapping keys were references, not contents (finder) | `KeyOf`: bytes for `bytes`/`string` keys, values otherwise |
| `Val.enum` took any `Nat`; static array length, `udvt` range and selector length unchecked; `Val.WF`/`Data.WF` cited but missing (both) | `Fin (D.enumSize d)`, `hl` for static lengths, `udvt` of a `Val` of the underlying type, `hs : sel.length = 4`; the `WF` citations removed |
| `Heap.write` could change a cell's type; the control wrote a `bool` over an array (both) | `write` takes `h.ty a = some τ`; `write_ty` |
| nested memory aliasing inexpressible (finder) | pointers as `Data.val (memRef …)`; `alias_seen` |
| `alloc_disjoint`/`write_alias` weaker than named; no copy operation (both) | `Heap.copy` with `copy_get`, `copy_independent`; `write_get` named for what it says |
| storage loosely typed: `read p τ` could return another type (both) | `Storage D L` typed by its layout; `read`, `write`, `set`, `set_restore` at `L p` |
| `SPath` steps untyped `Nat` with an unspecified key encoding (skeptic) | `Step` with `index`, `field`, `key` (contents' bytes) |
| `readInt` was not a decoder (finder) | `readInt` returns `Option`, rejecting non-extended words; `readInt_reject` |
| hard-coded selectors unchecked (both) | `#guard` against `selector` |
| rollback was a snapshot, so its theorems were `rfl` (both) | a journal of operations; `undo_apply`, `undoN_run`, `rollback_run`, `rollback_inner`, `rollback_outer_after_commit`, `rollback_transfer` |
| the world duplicated G01's external balances (both) | `World` holds the system's own instances only; external accounts are the session environment's |
| `revert_undoes` did not use the reverted state (skeptic) | it runs the call's operations and rolls them back |

Recorded, not fixed: the items under What S04.01–S04.03 do not do
(aggregate storage, layout and calldata well-formedness, pointer typing,
the frame stack, depth, static calls, logs, nonce ordering, `msg.value` in
`enter`). Environment and cryptographic observations are answered in
S04.02 rather than added: they belong to G01's environment and fixed
parameters, or are excluded by S01.

## Handoff

**Gates.** I ran `node scripts/check-g07.mjs --log` over a full
`./run-lean.sh`. Results:

- check-trust: 0 findings.
- check-layers: 0 modules reach the elaborator.
- check-orphans: 0 orphaned (753 reachable).
- check-noncircular: 0 violations (16 source modules).
- check-axiom-pins: 361 pins, 0 errors.
- check-source-grammar and `source-ctors --check`: clean.
- Script tests: pass.
- check-doc-paths: 46 missing, which is the baseline.
- G03 ledger: 38 errors, which is the baseline.
- The build: "Build completed successfully (738 jobs)" and "(262 jobs)".
- check-solkey: 37 mismatches, which is the baseline.

`TrustAudit.lean`'s source-state block passes in the Lean server.

**For S02.** Give memory and storage semantics over `Heap` and `Storage`:

- A storage reference evaluates to an `SPath` built from `Step`s, and a
  memory reference to an address.
- Assigning a reference copies the pointer. A copy is `Heap.copy`, or a
  storage load or store.
- Defaults come from `Val.default`.

**For S04.04.** Compose transactions from `Op`s run through
`ExecState.apply`:

- A call is `transfer` followed by `enter`. A revert is `rollback`; a
  success is `commit`.
- The transaction ends with `endTx`.
- External effects are G01 `Event`s.
- Still missing: the frame stack, the depth limit, static-call guards,
  logs, nonce ordering and aggregate storage operations (see What
  S04.01–S04.03 do not do).

**For the ABI work.** `Calldata.objects` must be the decoding of
`Calldata.input`, and `readInt` is the word-level decoder for integers.
