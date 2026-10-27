# Transient storage: source integration and composed execution

Current follow-up (2026-10-27): ordinary source declarations now retain their
transaction-local region in the existing typed logical root product. Reset,
projection/disjointness, source/call/rollback and opt-in owner/delegate controls
are implemented. General source-world dispatch and physical assembly remain
outside this implementation. See the follow-up section below for current
validation; the reproduction-only handoff and supplement sections are historical.
The follow-up supersedes their whole-contract source-refusal requirement for
the admitted fragment.


Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

Worker handoff (historical): **patch_ready_unvalidated**. The worker supplied the implementation
without Lean checking; the supplement is now included in combined integration. At that handoff the `transientState` inventory was
missing: ordinary source elaboration and scoped transient terms/rules were not
implemented. Physical transient layout, raw `tload`/`tstore` and gas remain
outside the logical model.

## Historical supplement and source refusal

`transientState` is **missing**: ordinary source elaboration and scoped
transient terms and rules do not exist. What exists is a typed supplement that
composes transient operations with the ordinary `Prog.run`. Physical layout,
raw `tload`/`tstore` and gas are outside the model. Semantics follow the
[Solidity v0.8.38 transient-storage chapter](https://github.com/argotorg/solidity/blob/1835d247de183f23e7b0e2bc4a50732af525b77c/docs/contracts/transient-storage.rst).

## Supported (`Semantics/Transient.lean`)

- `Slot L p` is a declaration position indexed by its primitive type;
  `Store L` holds exactly the declared values. Reference-typed cells cannot be
  declared. The cells are separate from `State.storage`.
- An ordinary fragment carries `Prog.within μ P = true`; a static context also
  checks `Prog.within .view P`. `Program.ordinary_frame` reuses
  `Prog.run_frame`. `Prog.within` admits only heap-neutral fragments.
- Zero-value calls to the same owning contract share persistent and transient
  cells. A child starts with fresh heap and locals, `msg.sender = selfAddress`
  and zero `msg.value`. A successful return adopts the child's storage,
  ledger, balance and transient cells and restores the caller's heap and
  transaction metadata. `TRun.tryCall` is unchanged.
- A caught revert or panic restores the whole entry `FrameState`, successful
  descendant writes to either store included. Divergence and exhaustion
  propagate. Static execution forbids transient writes in all descendants;
  pure frames cannot read transient cells.
- `Program.transact` enters through `Lifetime.World.enter`, starts from
  `Store.empty` and discards the store at exit. `transact_ok` needs actual
  successful entry and execution; `transact_ordinary` equals
  `Lifetime.System.run` for an ordinary-only body. A failed transaction
  commits nothing.
- `Calculus/Transient.lean` reads the supplement with `Modality.afterRunTR`
  (boxes exclude panic; diamonds keep the exhaustion policy) and bridges
  ordinary `Spec` proofs, including those from `Proves.valid`. It is not a new
  `Taclet` and does not extend `Fml`.

Example: `Examples/Tactics/TransientStorage.lean`.

## Refused, and why

- **A contract with any transient declaration is refused whole**, before any
  declaration is lowered: otherwise it would print as an ordinary persistent
  root. Unused declarations, public getters and functions that never mention the
  cell are covered. A structured diagnostic may replace the guard only if
  `scripts/transient-storage.test.mjs` still passes; it must not be relaxed
  because the supplement exists.
- Memory-allocating fragments and locals spanning fragment boundaries.
- Calls to another owning contract and delegate calls.

## What full support needs

- Transient declarations in `Contract`, and typed reads and writes in the
  scoped syntax, signature, updates, terms, printers, quotation, tools and
  elaborator. A transient read is a mutable value, not `Simple`: it cannot move
  across a sibling call that changes the cell. Widths, signedness, aliases and
  mutability must be kept.
- **A `State` field alone is unsound.** Callback and loop havoc must range over
  the new store, and every rebuilding, weakening, frame and anonymous-state
  proof must include it. `FrameKeeps`/`Prog.storeAt` (`2c1ce2e7`) must separate
  persistent from transient modification; a view loop frame preserves both,
  and a mutable callback cannot preserve transient cells by fiat. `holds`,
  `holdsC`, the closers, `Upd.Lands`, function and recursive contracts,
  `TGFrame` and their soundness proofs migrate together.
- A world interface with typed owner identity and rollback of all
  descendants, delegate ownership included.

## Reference check

`node scripts/check-transient-vectors.mjs SOLJSON_FILE EXTERNAL_NODE_MODULES`
runs signed transactions on the pinned solc 0.8.38 in a Cancun VM, legacy and
via-IR, including two successive transactions (reset of transient, persistence
of storage) and the compiler rejections. The false source properties panic
there; in the source runner they stay pending, which is not a refutation.

## Group 09 source integration follow-up (2026-10-27)

The code repair follows the original lane commits `600f49b6` and `efa1a6b4`.
It does not replace their reproduction report or historical corpus evidence.
The current per-fixture results are in
[the repair report](../../tests/upstream/group09-transient-source-repair.json).

### Representation and soundness

`Storage C` remains the intrinsic product `SFields C.vars`. It is now explicitly
the **joint logical store**, not the EVM persistent word address space.
`Contract.transientRoots` classifies declaration identities, and `transient_ok`
certifies that each transaction-local root exists at a primitive backend type.
The normal source width, address, byte and function-signature markers remain
attached to those roots. Function cells use the existing signature-marked
function-tag representation, not raw code addresses.

This avoids introducing an extra mutable state field that old reconstruction,
havoc or frame proofs could accidentally preserve or lose. Ordinary scoped
reads/writes, terms, updates, `holds`, `holdsC`, recursive/function contracts,
loop modifies sets and their soundness already quantify over the complete root
product. A transient read is the ordinary mutable `Val.read`, not `Simple`.
Thus the existing calculus applies to transient operations directly. No new
statement constructor, taclet, axiom or proof-limit override is needed.

`Storage.RegionRoot C region T` certifies the declaration type and region.
`RegionRoot.disjoint` proves a persistent root and transient root cannot name
the same declaration; `persistent_write` proves the corresponding frame law.
`resetTransient_get` and `resetTransient_find` state defaulting of transient
roots and exact preservation of persistent paths. `resetTransient_idem` proves
normalization idempotent. The source example additionally proves that the
contract certificate makes reference-valued transient roots impossible.

`Storage.resetTransient` reuses the existing proved `anon` operation with the
initial logical store as its source. It changes only classified roots. This is
not a physical packing/slot model. The representation warning was given before
editing; history's `1a78f65f` core layering and `2c1ce2e7` modifies-set optimization
remain in place. No deep embedding or state-family reconstruction refactor was
introduced.

### Actual source and transaction boundaries

Both ordinary and initializer reconstruction paths preserve the transient
marker after compiler-declaration-ID renaming. The finder caught erasure in
the second path during development; that confirmed issue was fixed. The syntax
rejects transient declaration initializers, and the contract certificate rejects
reference-valued transient declarations. Constructors can still assign cells:
the constructor and its field initialization execute in one frame.

`Lifetime.World.ofState`, `observe` and `enter` normalize transient cells.
The general `enter_storage` theorem correctly states equality with the reset
store, not preservation of the entire joint product. Persistent observations
remain unchanged. Payment is booked by `World.enter`; `State.transactionEntry`
only resets transient cells and memory for the scalar replay, which sends no
value. It does not book a second payment.

The upstream replay uses this entry operation before each non-constructor
vector. It retains persistent state and call ordering, runs constructor effects
before the first call, and restores the complete entry state on failure. Internal
calls, self calls and caught descendants never invoke transaction reset. Their
existing successful-state adoption and failure rollback operate on the joint
product, so they share or roll back both regions.

The replay also finds already-compiled public getters through their retained
`SourceCallable.getter` identity and **exact canonical ABI signature**. It never
invents a getter body or substitutes an unrelated function when one is missing.

Scalar tuple assignment now accepts multiple nonlocal targets only when every
target is a distinct scalar declaration name (a local or direct primitive root).
All right-hand values are captured before writes. Captures preserve narrow,
byte-alignment, address and function-signature information. Potentially aliasing
computed paths and repeated names retain their refusals and existing diagnostic
pins. A generic calculus proof covers all typed scalar input values; concrete
byte/function-tag controls catch metadata loss through integer temporaries.

A new limited `logicalStorageBase` feature admits an in-range literal `layout at`
declaration for logical field observations. The original physical `storageLayout`
feature remains excluded. Raw slots, packing, offsets, `tload`/`tstore` and general
assembly remain refused. This distinction admits the three assigned fixtures
whose expectations only read logical fields without pretending to discharge any
slot/assembly observations in the other fixtures.

### Owner and delegate interface

`Semantics/TransientWorld.lean` adds an **opt-in** `Operation.transact` adapter.
The existing `ContractWorld.Operation.run` and its callers are unchanged. The
adapter resets each installed account at its own catalog-indexed contract type,
runs one entire existing operation tree, then discards cells. Calls to different
owners use different typed account products; delegated library bodies use the
caller's product, identity, sender and value through the existing checked frames.
Failure restores the complete entry world, including all successful descendants'
persistent and transient writes; exhaustion/divergence retain error status.
`transact_ok` requires a real successful operation-tree outcome.

The automatic approval reviewer rejected an earlier proposed replacement of the
shared `Operation.run` semantics because of its broad blast radius. The separately
selected wrapper is the approved safer alternative. No shared world operation was
rewritten or silently switched to the new interface. General ordinary source
factory/library/world dispatch remains excluded by the existing guards; the
explicit catalog/body/ABI/environment obligations of the manual world API remain.
Existing `ContractWorld.Step` and `Reachable` still use raw `Operation.run`;
only clients explicitly selecting `Operation.transact` receive the new boundary.
Their existing reachability relations are not silently upgraded.

### Controls and interpretation

The source controls include constructor sharing, reset between successive
transactions with persistent retention, failure rollback, distinct regions,
actual successful self calls, a successful nested call followed by an ancestor
revert, and false persistent-alias assertions. The tuple controls cover arbitrary
input values, a false sequential-write interpretation, repeated-target refusal,
byte alignment and function-tag signatures.

`TransientSourceImport.lean` imports the new source fixture generated with the
SHA-pinned 0.8.38 compiler and kernel-checks successful execution of the actual
lowered self-call and rollback methods at a concrete deployed address. A false
source assertion must produce a panic. Declaration metadata is pinned for both
the ordinary and inherited contract.

The source tester's callback safety controls use explicit `@custom:key box`, as
existing self-call safety tests do. They are partial-correctness claims; the
strategy's default diamond rule for these calls is incomplete. Successful
execution is checked separately and cannot pass if the self-call is always
rejected. The source test binds the concrete deployment address `1`; it makes no
universal-success claim about the single-contract model's no-code address `0`.
No assigned fixture expectation, premise or proof limit was changed.

`Examples/Tactics/TransientWorld.lean` controls execute actual typed creation/call/library frames,
verify that a delegate changes only the caller's transient region, reject the
shared-owner interpretation, check transaction reset and persistent commit, and
check rollback of a successful delegate followed by failure.

Runtime matching remains observational evidence against the pinned upstream
vectors. These checks do not prove universal correctness of Solidity compilation,
execute generated solc EVM/SSA code, model physical slots, or establish general
source-world coverage. Reference compiler diagnostics remain separate checks.


### Frozen fixture results and integration scope

The authoritative `after-current/01` through `after-current/28` runs use one frozen
model SHA-256 `522d41b3a922d821b23e8c679300749ee866a1bab8f7f171a87ae25c75b5dc82`.
All 28 were broken at reproduction on this lane; 21 now match every retained
observation in **both** required legacy and viaIR modes (42 matching variants).
No assigned case was already fixed before this repair. There are no runtime
mismatches, fuel/time blocks, or host/configuration blocks in this final run.
The entire suite remains incompatible: seven fixtures (14 variants) remain
broken/excluded with actual `solidity.inlineAssembly` gaps:

- `inlineAssembly/inline_assembly_transient_storage_access_inside_function.sol`
- `storage/delete_overlapping_transient_after_storage_array_pop_same_base_type.sol`
- `storageLayoutSpecifier/state_variable_reference_types_slot_offset.sol`
- `storageLayoutSpecifier/transient_state_variable_slot_offset.sol`
- `variables/transient_state_variable_cleanup_assignment.sol`
- `variables/transient_state_variable_cleanup_tstore.sol`
- `variables/transient_state_variable_slot_inline_assembly.sol`

These are retained exclusions, not expected successful executions or passing
compiler-diagnostic checks. Full before/after rows, all observations, gaps,
per-fixture source/expectation hashes, raw report hashes and exact command arrays
are in the repair report. The historical `group09-transient-source.json`,
`tests/upstream/results`, pinned source archive and source/expectation bytes are
unchanged. Aggregate serial fixture time is 100.098 seconds; individual durations
are recorded in each invocation.

The runner and compiler are unchanged. Shared importer and tuple/getter changes
are deliberately limited to certified scalar roots, exact retained declaration
identities, and literal logical bases. Integration does not depend on another
lane's unpublished frontend/runner changes. General source-world dispatch,
physical packing/slots/offsets and assembly semantics remain separate work.

Reproduce one fixture by sourcing `/workspace/.setup/activate.sh`, then using its
recorded command (one exact path, never a broad family filter):

```sh
node scripts/solidity-upstream.mjs verify
node scripts/solidity-upstream.mjs run --compiler /workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js --filter test/libsolidity/semanticTests/variables/transient_state_variable_tuple_assignment.sol --batch-size 1 --out .lake/upstream/group09/review-tuple
```

The report's invocation array is authoritative for supported flags. Keep fresh
output directories, compiler SHA verification and both required pipelines; do
not overwrite historical results. Runtime agreement is observational evidence,
not a compiler correctness theorem.


### Final validation and handoff (2026-10-27)

Implementation commit `692a60cc` preserves the previous two lane commits. The
repair report records the validation follow-up. Full build/sort,
frozen SolKey TestSuite/corpus replay, strict automation, source controls, upstream
runner tests, module reachability, core layering and feature inventory checks
completed. Exact commands, elapsed times and retained log paths are in the repair
report's validation records; each fixture invocation includes its own command.

Lean MCP diagnostics were unavailable. Configured per-file Lean checks and full
kernel builds were used instead. Accepted proof logs contain only `propext`,
`Classical.choice` and `Quot.sound`; reset/disjointness projections require only
`propext`. There are no new axioms, `sorry`, dependencies or raised heartbeats.
The source/expectation bytes, pinned archive, historical results and frozen SolKey
were unchanged. This remains a dependency-free intrinsic implementation.

The first full-build process was interrupted by a managed-executor reconnect;
its successful modules and log were retained. Both full-build logs record one
actual compatibility issue: the declaration-replacement example in
`Solidity/Examples/ContractTypes.lean` needed to replace its transient-root
classification and certificate along with `vars`. The example now explicitly
classifies its replacement root as persistent, without weakening the invariant.
Its per-file check and final full-build retry passed. All 28 fixtures were then
rerun into distinct `after-current` directories to match the final model hash.

The broader checks retain two unrelated baseline limitations: documentation
paths report 13 missing references already recorded in the previous handoff, and
the trust-source inventory reports 25 findings, byte-for-byte identical to an
independent audit of `origin/master`. No new findings were introduced. These are
not recorded as passing gates. All long build logs are retained under
`/workspace/.setup/logs`; corpus output was captured before its checker deleted
the temporary log. Absolute timings are recorded without a baseline performance
comparison. Lean compilation was scheduled serially within the 16 GiB executor.
The resumed default-build attempt took 6696.727 seconds and failed only the
certificate example; its completed module artifacts were retained. The successful
cached build/TestSuite/sort retry took 939.268 seconds, the final exact-fixture
runs took 100.098 seconds in aggregate, and the frozen corpus gate took 70.443
seconds. The existing decision-array kernel check alone took 2338 seconds; it
passed without an OOM event or any proof-limit change.

The required finder and independent skeptic reviews were read-only and opened
no Lean workers. Confirmed issues found during development (initializer marker
erasure, feature classification, successful self-call controls, tuple metadata
controls and the declaration-replacement example) were fixed. Final reviews
confirmed all 28 raw report/fixture hashes, 42 matching variants with every vector,
14 excluded variants with actual assembly gaps, unchanged historical inputs,
standard axiom evidence and no further confirmed defect.

The lane is reviewable locally; no push or merge was performed. The patch export
and its SHA-256 are supplied in the final handoff. Remaining scope is precisely
the seven retained assembly/physical-layout fixtures above and general source
world dispatch; the existing manual typed owner/delegate interface has only the
explicit opt-in transaction adapter described here. Do not infer full fixture
compatibility or universal compiler correctness from the 21 passing cases.
