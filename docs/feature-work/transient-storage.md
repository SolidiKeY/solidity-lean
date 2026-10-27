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

## Historical supplemental interpreter

`Semantics/Transient.lean` supplies an explicit model-building supplement that
composes typed transient operations with the actual ordinary `Prog.run`.
`Slot L p` is a declaration position indexed by its primitive type. `Store L`
has exactly the declared values; a reference-typed cell cannot be declared.
Labels are documentation; positions identify cells. The cells are separate
from `State.storage`, its roots and its physical representation.

An ordinary fragment carries `Prog.within μ P = true`. Execution checks source
mutability compatibility, and an inherited static context additionally checks
`Prog.within .view P`. These checks reuse the current frame analysis; the
supplement does not infer safety from a user-supplied arbitrary state
transformer. `Program.ordinary_frame` uses `Prog.run_frame` and its conditional
balance/storage/ledger preservation directly. `Prog.within` currently admits
only heap-neutral fragments. Memory-allocating ordinary fragments and locals
spanning fragment boundaries are not admitted by this API.

Zero-value calls to the same owning contract share persistent and transient
cells. A child starts with fresh heap/locals, `msg.sender = selfAddress` and
zero `msg.value`; entry does not book the outer payment again. Successful
return adopts child storage, ledger, balance and transient cells, and restores
the caller's heap and transaction metadata. This supplements the ordinary
interpreter; it does not change `TRun.tryCall`'s existing frame semantics.
Calls to another owning contract and delegate calls are not represented here.

A caught revert, revert with data or panic restores the whole entry
`FrameState`, including successful descendant writes to either store.
Divergence and exhaustion propagate instead of becoming successful catch
results. Static execution prohibits transient writes through all descendant
calls; pure frames cannot read transient cells. Source mode compatibility is
checked separately from inherited static execution.

`Program.transact` uses `Lifetime.World.enter` for payment and fresh top-level
entry, supplies `Store.empty`, and discards the transient store at exit.
`transact_ok` requires actual successful entry and execution. The address,
time, payable-interface and environment restrictions of a lifetime model are
still its explicit caller obligations. `transact_ordinary` states equality
with the existing `Lifetime.System.run` when the body has only its ordinary
fragment. A failed transaction returns no changed world; it cannot commit.

`Calculus/Transient.lean` reads the supplement with the existing
`Modality.afterRunTR`: boxes exclude panic, and diamonds retain the ordinary
exhaustion policy. It provides sequencing, successful-post extraction, and
ordinary `Spec` box/diamond proof bridges, including reuse of a theorem obtained
from `Proves.valid`. This is not a new transient `Taclet` or an extension of
`Fml`. `Examples/Tactics/TransientStorage.lean` exercises actual persistent
ordinary writes alongside transient sharing/reset/rollback, typed boolean and
integer cells, static writes, false properties and an ordinary calculus proof.

## Historical source admission safety (before the follow-up)

Until the ordinary scoped bridge exists, the contract reader must reject a
contract containing a transient declaration, rather than print it as an
ordinary persistent root. The header guard runs over the inherited state
declarations before lowering any of them. It also covers unused declarations,
public getters and a function that never mentions the cell. This supplements
the concurrent source-admission work; the integrator may replace the guard
with an equivalent structured whole-contract diagnostic only if the regression
continues to pass. It must not be relaxed merely because the supplement exists.

The source fixture has successful and failing reentrancy/rollback properties,
static writes, a header/getter-only case, inheritance and a persistent control
contract. `scripts/transient-storage.test.mjs` requires whole-contract refusal
for the transient contracts, proves the persistent control assertion, and
keeps its false assertion pending. A pending row is not a refutation; the
independent EVM vectors check the false source properties actually panic.

## Historical separate-state migration plan

Full source support requires retaining transient declarations in `Contract`
and introducing typed reads/writes in the ordinary scoped syntax, signature,
updates, terms, printers, quotation, tools and source elaborator. A transient
read must be captured as a mutable value, not classified as `Simple`: it cannot
move across a sibling call which changes the cell. Narrow widths, signedness,
aliases and source mutability must be retained.

Adding a field to `State` alone is unsound. Callback and loop havoc must range
over the new store, and all state rebuilding/weakening/frame/anonymous-state
proofs must include it. The current modifies-set `FrameKeeps`/`Prog.storeAt`
interface (origin/master commit `2c1ce2e7`) must distinguish persistent root
modification from transient modification. A view loop frame must preserve both
stores; an arbitrary mutable callback cannot preserve transient cells by fiat.
The calculus's `holds`, callback `holdsC`, closers, `Upd.Lands`, function and
recursive contracts, `TGFrame` and their soundness proofs need to migrate
together. Different owning contracts also need a world interface with typed
owner identity and rollback of all descendants, including delegate ownership.

This patch leaves those indexed datatypes unchanged. It does not undo the
upstream speed-oriented core layering or the modifies-set optimization.
Consequently it avoids invalidating the dependent constructor folds just to
land a store field that the existing calculus cannot yet read soundly.

## Validation and review

The patch worker did not run Lean, MCP, builds, or source runners against the
real checkout. All following Lean claims are proof scripts requiring validation.
The primary should check the semantic module, then its calculus bridge, then
the example module; inspect their headline axiom sets. Check the frontend after
merging concurrent source admission and build `Solidity.Frontend.Testing` before
running `node --test scripts/transient-storage.test.mjs`.

The worker ran only pure scripts against its own staged files:

- `node --check` on both new JavaScript scripts: passed.
- Pinned solc `0.8.38+commit.1835d247` and an in-memory Cancun VM: 18 signed
  transaction executions across legacy/viaIR passed, including two real
  successive transactions on the same VM with transient reset and persistent
  preservation. The test never manually clears the transient store.
- Twelve compiler rejection checks (six invalid declarations/effects in both
  pipelines): passed.

The reference command is `node scripts/check-transient-vectors.mjs SOLJSON_FILE
EXTERNAL_NODE_MODULES`. It pins compiler bytes, needs no Lake dependencies,
does not install anything, and writes no fixture or checkout output.

The read-only finder checked current and origin/master frame interfaces,
fresh self-call semantics, header admission and ordinary proof integration.
The read-only skeptic confirmed the semantic boundary and found a cross-carrier
panic-exclusion proof issue in `holds_bind`; it was corrected by transporting
the exception equality explicitly. Self-review also replaced decidability-based
error equalities over dependent states with direct reduction proofs. Neither
reviewer invoked Lean or changed files. The dependent recursor, structural
store recursion and normalization in `transact_ordinary` remain focused
elaboration checks for the integrator.

After Lean validation, run reachability/layering, doc-path, inventory consistency,
ordinary TestSuite/corpus and frozen-SolKey checks appropriate to integration.
Do not upgrade the feature status based on these supplemental examples.

## Upstream reference

Semantics follow the manifest-pinned [Solidity v0.8.38 transient-storage
chapter](https://github.com/argotorg/solidity/blob/1835d247de183f23e7b0e2bc4a50732af525b77c/docs/contracts/transient-storage.rst).
The source/EVM tests use actual zero-value self-calls, successful descendants,
an ancestor revert, static execution and top-level transaction boundaries.

## Historical Group 09 source-integration reproduction (2026-10-26)

Status: **incomplete / reproduction only**. No source-integration repair was
implemented. This evidence does not upgrade `transientState`, and is not a
`patch_ready` handoff. Ordinary transient declarations remain refused.

The attached managed executor was used at `/workspace/solidity-lean`, with
`/workspace/.setup/activate.sh` sourced. The independent branch
`codex/group09-transient-source` starts at current `origin/master`
`006fcd593f5beeb540e7adf2bc76de4638566924`. No master push or merge was made.
Lean reports `4.24.0` (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`), Lake
`5.0.0-src+797c613`; `lake build Solidity.KeySort` passed. The runtime gate is
an actual build, not the environment's readiness label.

[The separate reproduction report](../../tests/upstream/group09-transient-source.json)
retains all 28 assigned historical rows, including `variants[].gaps` where
present, all fresh mode results, each exact command, fixture SHA-256, provenance
and elapsed time. Historical `tests/upstream/results` and pinned source and
expectation bytes are unchanged. `afterRepair` is null because no repair was
implemented; it does not denote a second run or a passing result.

All 28 fixtures were historically broken and remain broken in the current
runner. All 56 required legacy/viaIR variants stop at the whole-contract
`solidity.transientState` guard before runtime execution. None is already fixed;
none of these isolated runs timed out or exhausted fuel. No observations were
removed and no runtime agreement is claimed. The current reason is:

> transient declarations require transaction-local execution; this contract is not supported yet

The default 120,000 ms timeout and 1,000 loop fuel were retained. The 28 isolated
commands took 119.353 seconds in total, including repeated verification/build
checks (not a Lean semantic performance benchmark). Their command pattern is:

```sh
source /workspace/.setup/activate.sh
node scripts/solidity-upstream.mjs verify
node scripts/solidity-upstream.mjs run \
  --compiler /workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js \
  --filter test/libsolidity/semanticTests/constructor/transient_state_variable_initialization.sol \
  --batch-size 1 --out .lake/upstream/group09/before/01
```

The report supplies the other 27 full paths and distinct output directories.
The SHA-checked compiler is `0.8.38+commit.1835d247.Emscripten.clang`, SHA-256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
The archive hash is
`9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d`;
the runner hash is
`c860ec034b8dbf26c632f45a0c52c215df9eda9fc2fd10e3c3f8b84f4a37d468`.
The fresh model hash is
`c86945ed62a18ffccf0b72b291c6271f44462f7b1d60b101e73fd2ec565c8699`;
the historical model hash is
`c042a72f4d864a780a366ad4f27d148df0d7e213d33c37d4b6a51f0ad33710df`.

### Required migration and retained exclusions

The read-only finder and independent skeptic both confirmed the following
interfaces still need coordinated implementation and soundness proofs:

- `State` has persistent storage only. `Contract`'s ordinary roots cannot
  represent transient declarations. Source declaration identity, primitive
  widths/signedness and function-pointer types must survive elaboration.
- `TGFrame`, `FrameKeeps`, modifies sets and `Fml.anonHavoc` do not constrain
  or quantify transient cells. Typed terms/updates, callback reading, loops,
  recursive/function contracts and state reconstruction must migrate together.
- `Tools.Upstream.replay` executes `Prog.runF` and retains `o.st.glob`.
  It does not enter through `Transient.Program.transact`, which supplies the
  supplement's fresh cells. Deployment effects, transaction reset and caught
  descendant rollback must be connected to the actual source execution path.
- The supplement supports zero-value self-calls. Distinct owner identities and
  delegate ownership are absent; ordinary `ContractWorld` library execution
  cannot supply those transient semantics merely by linking the modules.
- `Calculus.Transient` bridges ordinary proofs and supplemental sequencing;
  it does not implement transient scoped terms, taclets or source proofs.

No representation refactor was attempted. History records `1a78f65f`'s core
layering for checking speed and `2c1ce2e7`'s modifies-set loop frames. A future
migration must warn about checking cost and preserve these interfaces' purpose.
Removing admission guards alone would give persistent semantics to transaction
storage and is unsound.

Actual fixture source, rather than filename inference, identifies seven
assembly/physical-observation exclusions that must remain even after typed
source integration:

- `inlineAssembly/inline_assembly_transient_storage_access_inside_function.sol`
- `storage/delete_overlapping_transient_after_storage_array_pop_same_base_type.sol`
- `storageLayoutSpecifier/state_variable_reference_types_slot_offset.sol`
- `storageLayoutSpecifier/transient_state_variable_slot_offset.sol`
- `variables/transient_state_variable_cleanup_assignment.sol`
- `variables/transient_state_variable_cleanup_tstore.sol`
- `variables/transient_state_variable_slot_inline_assembly.sol`

These are under `test/libsolidity/semanticTests/`. The function-pointer fixture
also needs a typed internal-function-pointer transient cell, beyond the current
primitive-only supplemental layout. The other 20 fixtures are not excluded by
this review: their ordinary source semantics remain unimplemented. In
particular, `state_variable_struct.sol`, `state_variables_transient.sol` and
`transient_state_variable_slots_and_offsets.sol` contain no assembly and must
not be excluded solely on their names or layout syntax. Required pipelines,
all vectors and all observations remain obligations.

### Reproduction validation

No Lean MCP diagnostics tools are exposed in this thread. The repository's
`lean-verify` skill was read; configured Lake commands were used instead.
No Lean code, proof limit, premise, expectation, axiom or dependency changed.
There are no new soundness theorems in this evidence patch.

- Snapshot verification: all 11,622 files passed.
- `lake build Solidity.KeySort Solidity.Tools.Upstream`: passed on retry.
  The initial concurrent build exited 135 in `Tools.Run`; the successful
  build and all fixture commands subsequently completed. Full logs are in
  `/workspace/.setup/logs/group09-*`; this incident is not a source verdict.
- `node --test --test-isolation=none scripts/solidity-upstream.test.mjs`:
  all 14 passed with temporary-file write access. The first read-only-sandbox
  attempt failed on `mkdtemp`, before rerunning successfully.
- `lake --no-build lean tests/upstream/Replay.lean -- --tstack=131072`:
  all five existing sequencing/rollback/inconclusive-halt replay checks passed.
- `lake build Solidity.Semantics.Transient Solidity.Calculus.Transient`: passed.
- `node scripts/check-orphans.mjs`: 667 reachable, zero orphans.
- `node scripts/check-layers.mjs`: 143 core modules, none reaches elaborator.
- `node scripts/check-automatic.mjs --strict`: 491 automatic, 61 budgeted,
  11 refuted, zero pending.
- `./scripts/check-testsuite.sh --solkey tests/migration/solkey/keyext.solidity.examples`:
  passed (552 derived, 11 refuted, one excluded, zero pending). The activation
  script's external `SOLKEY_EXAMPLES` lacks its adjacent pin manifest, so the
  frozen repository snapshot was supplied explicitly.
- `lake exe solkeycheck --key tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key`:
  passed, 377 parsed taclets and all 131 read-bearing annotations covered.

Finder/skeptic reviews were read-only and opened no Lean workers. The skeptic
verified all exact paths, source hashes, provenance and 56 refusal variants;
confirmed the migration blockers; and rejected filename-based exclusions.
It also checked pipeline selection: `Frontend.Import` derives evaluation
order from compiler provenance when no explicit option is given. No pipeline
selection defect is claimed here. Both reviews distinguish reproducible refusal
from execution coverage. The source-integration task remains outstanding.

Additional completed controls:

- `lake build Solidity.Examples.Tactics.TransientStorage Solidity.Frontend.Testing`:
  passed (244 jobs including cached dependencies). Existing `static_preserves`,
  `attempt_rollback`, `transact_ordinary`, `holds_bind` and `ordinary_spec_box`
  each printed exactly `[propext, Classical.choice, Quot.sound]`.
- `node --test --test-isolation=none scripts/transient-storage.test.mjs`:
  passed, including whole-contract refusal and the persistent positive/negative
  controls (8.729 seconds). This is a safety regression, not transient source
  execution coverage.
- The independent skeptic also checked the written report against the raw
  isolated reports. Its ambiguity finding was fixed: the field is now
  `additionalRequirementsBeyondSourceIntegration`, and a common source-integration
  requirement applies explicitly to every row, including empty additional lists.

Final corpus gate:

```sh
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
./scripts/check-corpus.sh --solkey tests/migration/solkey/keyext.solidity.examples
```

Passed: probe/generator comparison and `SolidityCorpus` build (257 jobs),
including the existing TestSuite derivations and report. The first corpus
build was stopped to avoid overlapping Lake artifact writers; the sequential
four-thread attempt reached the managed executor's 16 GiB memory limit and
was also stopped. Neither interrupted attempt is a passing gate. The successful
one-thread retry changes concurrency only, not heartbeats, proof limits, fuel
or expectations. Full retained logs are
`/workspace/.setup/logs/group09-corpus-serial.log` and
`/workspace/.setup/logs/group09-corpus-serial-build.log`.

The documentation-path checker still reports its 13 missing references in
unchanged vendored documents and `Solidity/Eqns.lean`, with no finding in this
patch. No broad default-library rebuild was performed: this patch changes only
documentation and reproduction evidence; the targeted builds, proof controls,
replay, source-admission, sort and corpus checks above are its completed gates.
All shared frontend/runner and core files remain unchanged, so this evidence
patch has no unpublished dependency on another group's implementation.


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

`TransientWorld.lean` controls execute actual typed creation/call/library frames,
verify that a delegate changes only the caller's transient region, reject the
shared-owner interpretation, check transaction reset and persistent commit, and
check rollback of a successful delegate followed by failure.

Runtime matching remains observational evidence against the pinned upstream
vectors. These checks do not prove universal correctness of Solidity compilation,
execute generated solc EVM/SSA code, model physical slots, or establish general
source-world coverage. Reference compiler diagnostics remain separate checks.


### Frozen fixture results and integration scope

The authoritative `after-final/01` through `after-final/28` runs use one frozen
model SHA-256 `b59b563b228a0f95ba024be4b16051f4b73ae5c91fe549bbb4ea6b8c84c1abdd`.
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
unchanged. Aggregate serial fixture time is 97.080 seconds; individual durations
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
