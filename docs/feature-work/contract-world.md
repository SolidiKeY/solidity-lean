# Contract world

Features: `newContract`, `creationTry`, `externalLibraryCalls`, `libraries`,
`constructorLifetime`, `worldAssumptions`, `addressBalance`, all partial. The
interface composes actual typed runs; the ordinary source importer does not
support arbitrary world effects.

## Typed world frames (`Solidity/Semantics/ContractWorld.lean`)

- A catalog-indexed account map: each installed account stores its catalog
  identity and storage at that contract's type. Addresses are bounded to 160
  bits; handles keep the expected identity, checked against installed code on
  entry. Balances include funded accounts without code.
- **Creation** keeps an address's prefunding, checks collision and sender
  funding, starts from fresh typed storage, runs the constructor, settles
  payments and installs code. The creator picks the fresh address: neither
  CREATE's nonce formula nor CREATE2 is modelled.
- **Settlement.** The run's ledger records net payments, not balances. A
  successful frame settles each other account's first entry against the world,
  rejecting unfunded debits, invalid addresses and overflowing credits. A
  failed frame returns no changed world; `atomic` restores the transaction's
  original world; `tryCreate` gives the handler the world before the creation
  frame. Argument evaluation and the success continuation are outside the
  catch. Divergence and exhaustion are not caught failures.
- **Libraries.** Catalog roles are fixed by the initial world; ordinary
  creation and calls refuse a library identity. A library deployment has no
  fields, initializers or user constructor. Linked execution checks the
  installed identity and runs the body over the caller's storage,
  self-address, balance, sender and value, charging no second payment. The
  nonpayable value check is not repeated (the value stays visible, as in
  solc's library dispatcher).
- `Solidity/Calculus/ContractWorld.lean` bridges `Spec` and formula box proofs
  to successful constructor/call outcomes. The precondition is required at the
  paid entry; the world settlement is a premise of a global invariant. No proof
  turns fuel exhaustion into success. `Reachable` separates funded
  constructor-reachable worlds from arbitrary states.

## Source commands (`Solidity/Frontend/WorldImport.lean`)

Hash-checked alternatives to `solc_import`, which stays world-unaware:

- `solc_world_factory`: a stateless, noninheriting factory method whose body
  returns one creation with literal arguments and value, or one creation try
  with constant Boolean success and bare-catch results. Constructor closure is
  checked. The generated `run` needs a proof of `assumptions w ctx = true`
  (factory/target roles, empty oracle input, no code at literal payment
  recipients), so an unsupported environment cannot turn a receive/fallback
  call into a balance update.
- `solc_world_library`: one direct public/external library call passing one
  caller storage root to one literal storage-field assignment, resolved by
  declaration IDs and elaborated as a closed typed program.

Generate fixtures with `node scripts/solc-ast.mjs --world-metadata`; explicit
abstractness metadata is required, so older trimmed fixtures are rejected.
`node scripts/contract-world.test.mjs` checks the metadata and hash rewrites
(`SOLKEY_ROOT` when the compiler checkout is elsewhere). The report read is
listed in `tests/trust-inventory.json`.

## Refused, and why

- Unresolved or world-effecting constructor calls and transient state in a
  factory.
- Constructor balance observations, until expressions read the global ledger.
- Computed view bodies and direct pure/view library calls: read-only frames
  admit only empty-body observations.
- Library-owned qualified structs (the fixture uses a shared top-level struct).

## Left

- `Reachable` ranges over the explicit `Operation` constructors; the source
  wrappers are not certified as those transitions, and creation-catch has no
  constructor of its own.
- A world-aware statement/frame interface for source `new` and calls: dynamic
  arguments, memory/ABI transfer, return decoding, callbacks, transient
  storage, gas. Effect-certified computed static bodies. Composition of
  factory catalogs.
- General library arguments, aggregate results, typed catches, nested
  external contract execution.
- Source balance expressions still use the single-contract observations;
  arbitrary-address balances exist only at the world API.


## Step 8 transient composition seam (2026-10-28)

Closed factory **targets** may now contain certified transient cells. Factory
owners still require default stateless implicit construction, and a transient
owner retains `solidity.worldFactory.owner`. The generated `run` stays a frame.
Use `World.transact` from `Semantics/TransientWorld.lean` once around a complete
typed composition of imported frames to get owner-specific entry/exit reset and
atomic uncaught rollback. Nested calls/catches retain the existing frame laws.
The transaction adapter preserves return values and exact halts; it does not
certify `Step`/`Reachable` or general source statement lowering. Details, evidence
and remaining refusals are in [transient-storage.md](transient-storage.md),
“Step 8”. This seam adds no delegatecall, static-body admission or policy change.
