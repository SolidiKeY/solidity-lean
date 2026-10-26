# Contract-world feature group

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

Owned features: `newContract`, `creationTry`, `externalLibraryCalls`,
`libraries`, `constructorLifetime`, `worldAssumptions`, `addressBalance`.
These remain partial. The new interface composes actual typed runs; it is not
a claim that the ordinary source importer supports arbitrary world effects.

## Typed world frames

`Solidity/Semantics/ContractWorld.lean` adds a catalog-indexed account map.
Each installed account stores its catalog identity together with storage at
that contract's type. Addresses are bounded to 160 bits; handles retain the
expected contract identity, which is checked against installed code on entry.
Balances include funded accounts without code. Creation retains an address's
prefunding, checks collision and sender funding, starts with fresh typed
storage, executes the supplied constructor, settles payments and installs code.
The creator chooses a fresh address explicitly. Neither CREATE's nonce/address
formula nor CREATE2 is modeled here.

The run's ledger records net payments, not global balances. A successful frame
settles its first entry for each other account against the world's balances,
rejecting unfunded debits, invalid addresses and overflowing credits. The
executing instance uses the run's resulting self-balance. A failed frame
returns no changed world. `atomic` restores the transaction's original world;
`tryCreate` gives the creation handler the world before that creation frame.
Argument evaluation and the success continuation are outside that catch.
Divergence and model exhaustion are not caught completed failures.

Library catalog roles are explicit and fixed by the initial world. Ordinary
creation and calls refuse a library identity. A separate library deployment
requires no fields, initializers or user constructor. Linked execution checks
installed library identity, then runs the resolved body over the caller's
typed storage, self-address, balance, sender and value. It charges no second
incoming payment. Library entry does not repeat an ordinary nonpayable value
check: the original value remains visible during delegation, as in the pinned
compiler's library dispatcher. General computed view bodies and direct pure/view library
calls remain unsupported: read-only frames conservatively admit empty-body
observations only.

`Solidity/Calculus/ContractWorld.lean` bridges existing Spec and formula box
proofs to actual successful constructor/call outcomes. The precondition is
required at the paid entry; the exact world settlement remains a premise for
a global invariant. No proof manufactures a successful outcome from fuel
exhaustion. `Reachable` distinguishes funded constructor-reachable worlds from
arbitrary typed states and carries the allowed-operation premise explicitly.

## Strict source fragments

`Solidity/Frontend/WorldImport.lean` adds hash-checked source commands:

- `solc_world_factory` accepts a stateless, noninheriting factory method whose
  whole body returns one ordinary creation with literal arguments/value, or
  one creation try with constant Boolean success and bare-catch results.
  The constructor and its base/field initialization come from the existing
  importer. Constructor closure is checked; unresolved or world-effecting
  calls and transient state are rejected. Literal send/transfer recipients
  are exposed as no-code assumptions, and external oracle input must be empty.
- `solc_world_library` accepts a whole direct public/external library call
  that passes one caller storage root to one literal storage-field assignment.
  The fixture uses a shared top-level struct, supported by the existing
  structural schema reader; importing library-owned qualified structs remains
  a separate type-reader interface. Compiler declaration IDs resolve the caller root, library and parameter.
  The command substitutes the resolved storage parameter with the caller's
  root and elaborates that exact assignment as a closed typed program.
  It does not reuse the ordinary importer's unsupported external-call body.
  The world additionally requires the installed linked identity and caller context.

Generate their fixture with `node scripts/solc-ast.mjs --world-metadata` and
the usual source/output/wrapper arguments. Explicit abstractness metadata is
required; older trimmed fixtures are rejected rather than treated as concrete.

These are alternative commands with explicit source-admission boundaries.
They do not silently change ordinary `solc_import` or `sol{…}` into a
world-aware interpreter. Each command creates a small typed code catalog.
The generated factory `run` requires a proof of
`assumptions w ctx = true`: ordinary factory/target roles, empty external
oracle input and no installed code at literal payment recipients. Unsupported
environments therefore cannot invoke this source API by silently replacing a
receive/fallback call with a balance update. Constructor balance observations
are also refused until expressions read the global ledger. The manual world
API retains explicit body/dispatch/environment obligations, as Lifetime does.

## Remaining interfaces

Reachability currently ranges over the explicit Operation constructors.
The source wrappers are not automatically certified as those transitions,
and creation-catch composition does not yet have its own Operation constructor.

Arbitrary source statements containing new/calls need a world-aware typed
statement/frame interface, including dynamic arguments, memory/ABI transfer,
return decoding, callbacks, transaction-scoped transient storage and gas.
Computed static bodies need an effect-certified interface. Factory catalogs
need composition for larger source worlds. General library arguments,
aggregate results, qualified library-owned struct import, direct pure/view
entries, typed catches and nested actual
external contract execution remain open. Arbitrary-address balance reads are
available at the explicit world API; source balance expressions still use the
single-contract interpreter's existing supported observations.

The source boundary follows pinned Solidity:
[creation and try/catch](https://github.com/argotorg/solidity/blob/1835d247de183f23e7b0e2bc4a50732af525b77c/docs/control-structures.rst)
[library context](https://github.com/argotorg/solidity/blob/1835d247de183f23e7b0e2bc4a50732af525b77c/docs/contracts/libraries.rst),
and [library dispatcher value checks](https://github.com/argotorg/solidity/blob/1835d247de183f23e7b0e2bc4a50732af525b77c/libsolidity/codegen/ContractCompiler.cpp#L525-L528).

## Validation and review

Worker handoff (historical): `patch_ready_unvalidated`. This patch was produced outside the real
checkout. Read-only finder/skeptic review checked settlement signs, self and
duplicate ledger entries, code identity, catch boundaries, source completeness
and current/origin frame APIs. It prompted proof-carrying source environment
admission and additional rejection regressions.

Temporary-file checks passed: the pinned compiler accepted the Solidity
fixture, and `node scripts/contract-world.test.mjs` checked deterministic
metadata serialization, all world-command hash rewrites, intentional ordinary
stale-import preservation and opt-in abstractness metadata. The test uses
`SOLKEY_ROOT` when the compiler checkout is elsewhere. These checks inspect
compiler input/output and helper behavior, not the Lean proofs. The patch worker
ran no Lean/MCP/build, kernel proof check or axiom report. The implementation is
now integrated; combined validation includes the three implementation modules,
both regression modules, headline axiom reports and the repository
layer/orphan/documentation and final build gates. The ordinary
source inventory remains partial; site registration belongs to integration.

## Integration trust inventory

The new WorldImport report read is explicitly inventoried in
`tests/trust-inventory.json`. It evaluates the existing importer's constructor
status to refuse unavailable constructor bodies. It does not construct a proof
or bypass kernel checking of the generated typed programs or world theorems.
Only this newly reviewed site was added; pre-existing inventory drift was not
re-pinned. Headline world and source-factory theorems use only the standard
Lean axioms printed by their examples.
