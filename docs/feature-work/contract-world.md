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

- Dynamic source arguments and general operation-valued catch/success bodies.
  The certified creation-catch operation currently models a bare catch with
  constant source results; it does not admit arbitrary handler code.
- A world-aware statement/frame interface for source `new` and calls: dynamic
  arguments, memory/ABI transfer, return decoding, callbacks, transient
  storage, gas. Effect-certified computed static bodies. Composition of
  factory catalogs.
- General library arguments, aggregate results, typed catches, nested
  external contract execution.
- Source balance expressions still use the single-contract observations;
  arbitrary-address balances exist only at the world API.

## Source operation certificates (2026-10-27)

Branch `feature/world-reachable-catch` starts at current `origin/master`
`f4dee4a29c2e208b36db4a4161a4723c735cd775`. The clean cloud clone is
`/workspace/solidity-lean`; groups 01–10 and their reports were preserved.
This increment certifies existing executable source wrappers; it does not
claim dynamic source arguments or general external-code execution.

`Operation.tryCreate` executes the existing typed `World.tryCreate`, including
argument evaluation before the catch. A catchable creation failure returns
exactly the precreation world. Exhaustion/divergence propagate; neither can
supply a commit or completed rollback. `Operation.guard` is a Boolean refusal
with no world selection or writes, preserving the factory's static guard.
Neither constructor adds a `Stmt` or a dynamic-logic rule.

`Solidity/Semantics/ContractWorldCertificates.lean` proves exact result erasure:
only the return value is forgotten; the committed world and every halt are
retained. `World.paidRun` is definitionally the old three-step wrapper prefix
(storage lookup, funded paid entry, settlement). Its certificate identifies
that prefix with an actual typed empty call. It retains all funding, payable,
identity and settlement checks. The factory certificate includes the static
and ordinary-code guards and composes this call with actual creation/catch.
The library certificate composes paid entry with actual linked execution; it
requires an explicit ordinary caller-role premise. Roles are catalog model
obligations, as before. No assumed external response or arbitrary poststate
is used to certify execution.

Both source commands now emit `operation`, `run_certificate` and
`run_reachable`. Reachability requires an already funded reachable input,
`allowed w operation`, and actual successful source execution. Factory
`assumptions w ctx = true` remains required. Exact erasure also retains failed
runs, so the existing `Step.rollback` can use its completed-failure premise;
exhaustion still cannot be a rollback witness. Source return handles and
Boolean results remain tested independently of their world-only certificate.

The real `tests/solc/ContractWorld.sol` fixture is unchanged. A concrete
constructor-rooted source-catch witness now reaches a world with sender 8,
factory 2, prefunded child 4, recipient 0, no installed child and result false.
It proves the incoming factory payment survives the caught constructor's
write/payment rollback. A zero-value read-only factory regression pins the
static refusal. Existing tests still cover callable child identity, false
assertion rejection, successful/failed creation, uncaught rollback, independent
library callers, missing links, static library refusal and environment admission.

Before editing, `Solidity.Examples.Tactics.ContractWorldSource` passed on the
starting master: supported direct creation and creation catch executed, while
`dynamicArgument` retained `solidity.worldFactory.arguments: factory parameters
are not lowered yet`. The source baseline took 297.249 s, cgroup peak
915,886,080 bytes. Actual runtime versions are Lean 4.24.0 (`797c613`) and Lake
5.0.0-src+797c613. `Solidity.KeySort` passed in 0.154 s. Checks use the documented
writer lock, `LEAN_NUM_THREADS=1`, explicit Lean `-j1` through an untracked
alternate TOML, and a local Docker cgroup with `memory.max=12 GiB` and no swap
allowance because this executor has no systemd bus. The repository and setup
toolchain are bind-mounted from this same attached environment.

Focused kernel checks pass for the certificate module, generated source
certificates and concrete reachability witness. The final focused source check
took 87.494 s (including regenerated-catalog imports), cgroup peak 842,190,848 bytes. Reported axiom sets contain only
`propext`, `Classical.choice`, `Quot.sound`. These are Lean semantic proofs;
they are not a compiler/EVM equivalence theorem. Broader gates and independent
reviews are recorded below when completed.

Shared-file edits: `Solidity/Semantics/ContractWorld.lean` (two additive
operation constructors/run arms), `Solidity/Frontend/WorldImport.lean` (the
paid-prefix helper and certificate declarations), existing source examples,
module map, feature manifest and generated inventory/catalog. The ordinary
importer, core statement/state representations, recursive-type migration,
ABI replay and inherited getters were not changed.

The independent read-only finder and skeptic found no confirmed semantic
defect. Their integration requests were addressed: the new module is imported
from `Solidity.lean` and listed in the module map; direct and linked generated
operations have executable regressions; argument exhaustion remains outside
the catch. The bare-catch scope, unchanged dynamic-source refusal and explicit
ordinary library-caller premise are recorded above. Neither reviewer invoked
Lean or wrote files.

All four edited implementation/example files passed per-file MCP error
diagnostics (29.824 s, cgroup peak 1,561,927,680 bytes); a known Python asyncio
shutdown warning followed successful diagnostics, and the process exited 0.
The entire source-control file also passed independently against solc 0.8.38
analysis fixtures for legacy (7.430 s) and viaIR (7.326 s), retaining every
positive/negative test and axiom query. Total pipeline validation took 15.987 s,
cgroup peak 332,320,768 bytes. Compiler SHA-256 is
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
[New evidence](../../tests/contract-world-certificates/world-pipelines.json)
records source/control/fixture hashes and exact pipeline commands. Raw focused,
MCP and pipeline logs and environment-specific replay commands are in the same
new directory; no historical report was overwritten.

## Combined validation and handoff (2026-10-28)

The final `./run-lean.sh` completed with exit 0: **686 default-target jobs,
259 TestSuite jobs**, then 377 frozen taclets and all 131 read-bearing
annotations matched. Elapsed time was **145m34.609s**; recorded cgroup peak was
**12,884,901,888 bytes (12 GiB)**, equal to the enforced limit. Swap allowance
was zero. Previously checked setup/focused artifacts were retained, so this is
the measured bounded combined run, not a clean-checkout cold benchmark. An
attachment refresh disconnected the original output stream; the same surviving
build container's logs and terminal status were recovered without restarting
or duplicating Lean work.

The three selected ordinary-import upstream fixtures remain blocked by
`transaction/block/self-address or cross-contract host behavior not adapted`:
`tryCatch/create.sol`, `libraries/external_call_with_storage_mapping_parameter.sol`,
and `functionCall/creation_function_call_with_args.sol`. Both required legacy
and viaIR replays are explicitly blocked, not passing observations. All original
source/expectation rows, including gas rows, are retained with hashes in the
[new handoff](../../tests/contract-world-certificates/README.md). Their runner
checks took 3.420 s, cgroup peak 318,824,448 bytes, exit 1. An initial malformed
command ran no fixtures; its failed-invocation log is retained separately.

Final static checks pass: trust (715 sources, 240 inventoried sites, no
findings), reachability (701 modules, no orphans), layers (153 core modules,
no frontend leaks), strict automation (491 automatic, 61 with a step budget,
11 refuted, none pending), and generated inventory consistency (212 features,
783 classified upstream symbols). The affected metadata/hash Node regression
passes 1/1. The documentation-path audit still reports 20 missing references,
all in unchanged archived group03/group10 reports or an existing Mathlib
citation; it is not recorded as passing. No historical report was rewritten.

The reviewable implementation is `1e37a2256e277ef24b04284ad0de9f822feaca8c` on
`feature/world-reachable-catch`. Complete commands, per-fixture outcomes,
standard-axiom checks, compressed raw logs, exact remaining refusals and shared
file edits are in
[validation.json](../../tests/contract-world-certificates/validation.json).
The source certification increment is complete; dynamic source creation
arguments, general library arguments/results and ordinary world-aware execution
remain explicitly unsupported. No master push or merge was performed.

The final independent read-only finder and skeptic also verified all retained
log/exit, archive/fixture, pipeline, source/control/model, compressed coverage
and implementation-patch hashes. Neither invoked Lean or builds; no confirmed
inconsistency remained. The temporary root build configuration was removed
after validation, with its exact contents retained in the handoff.

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
