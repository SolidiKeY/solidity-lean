# VY5: assembly composition and differential backfill

Status: **partial implementation checkpoint; full lane blocked on concrete
prerequisites**. No general Yul support or whole-pipeline theorem is claimed.

Repository: `/workspace/solidity-lean`. Base:
`0b078cefaf7daad79007b87b72df64eb6936420f`. Branch:
`codex/solidity-inline-assembly5-20261031/vy5-composition`.
The exact committed head is recorded in the external handoff after committing,
avoiding a self-referential commit ID. The previous `work` branch at
`2fe1f8932f96be15b00df03ba2cde46f64a87758` and existing caches were preserved.
The pinned base was fetched by exact SHA and its direct-parent relationship
verified. No other lane was integrated or modified.

## Queue accounting

The table and checks below describe the original checkpoint; the dated recovery
section updates its reference-adapter results without closing proof obligations.

| Item | Result and remaining obligation |
|---|---|
| Work 1: Y10 composition | Pending. The G03 extension has 24 explicit pending obligations, six constructor combinations and exact dependency/owner validation. No concrete V16/VY3/VY4 assembly interfaces exist in this tree. No residual predicate or generic certificate wrapper substitutes for them. |
| Work 2: G52 assembly differential harness | Partial. All 80 pinned upstream fixtures are inventoried and probed in both pipelines, optimizer off/on. Raw compiler input/output, hashes and original expectations are retained. The existing bounded EVM adapter is reused unchanged for upstream-required default profiles; its unsupported cases remain blocked. Lean comparison, full memory/world observations and source correspondence are pending. |
| Work 3: whole-pipeline witnesses/closure | Pending. External reference controls cover all six combinations, success/failure, malformed import, incorrect opcode, constructor failure, dirty bits, allocation, storage, logs and rollback. Three narrow recognizer-refusal equalities are kernel checked. These are not whole-pipeline witnesses. Final joint imports and composition remain open. |
| Backfill A | Inventory, byte-preserving extraction, fixture parser reuse, compiler runner/provenance validation and local mocks implemented; actual pinned compiler/EVM output retained. No V17 or legacy generated output was copied/replaced. Full observation adapters remain pending. |
| Backfill B | Independent expected outcomes, advisory policy controls, constructor combinations, exact child/owner dependencies and missing/stale-proof rejection implemented. Closure is intentionally rejected until reviewed concrete interfaces can replace pending entries. Wire-up remains pending. |

The human-approved [YQ1–YQ7 decisions](../solidity-scope.md#inline-assembly-decisions-2026-10-31)
are implementation directions. The manifest still reports the actual excluded
`inlineAssembly` row with empty evidence. The pre-existing importer still
recognizes only declaration-sensitive `memoryRethrow?`; no source definition,
frontend dispatch, core state or owner prerequisite was rewritten.

## Artifacts and reproduction

Lane-owned files:

- [Pinned extraction](../../scripts/yul-composition/inventory.py): standard library only; validates the pinned archive and every selected file before writing raw bytes. Populated extraction drift is rejected.
- [Harness](../../scripts/yul-composition/harness.mjs): actual solc AST preflight, raw input/output preservation, compiler/source/settings/output hashes, original fixture settings/expectations, both-pipeline probes and optional bounded reference execution.
- [Fixtures](../../tests/yul-composition/fixtures.json): independent outcomes for six combinations plus positive/negative controls. The incorrect-opcode control retains the source expectation 42, then deliberately substitutes a SUB target slice that returns 40. A separate corrupted target always reverts. Both remain recorded mismatches.
- [Ledger](../../tests/yul-composition/ledger.json): supplement to G03, with real source-constructor names checked and no closed assembly row.
- [Finite proof catalog](../../tests/yul-composition/proof-controls.json): source/signature/dependency hashes reject stale or missing recognizer controls; the separate kernel gate is mandatory.
- [AST feature collector](../../scripts/yul-composition/coverage.mjs): provenance-bound presence inventory for actual manifest rows, explicitly without semantic/admission coverage.
- [Mock tests](../../scripts/yul-composition/harness.test.mjs) and [inventory tests](../../scripts/yul-composition/inventory_test.py).
- [Rethrow controls](../../tests/yul-composition/RethrowControls.lean): isolated boundary tests, outside public core imports.

Run under the required writer lock and hard resource scope:

```sh
python3 scripts/yul-composition/inventory.py --extract /workspace/vy5-composition/corpus --out /workspace/vy5-composition/corpus/inventory.json
node --test --test-concurrency=1 scripts/yul-composition/harness.test.mjs scripts/yul-composition/coverage.test.mjs
python3 scripts/yul-composition/inventory_test.py
node scripts/yul-composition/harness.mjs --compiler /workspace/vy5-composition/soljson-v0.8.38+commit.1835d247.js --corpus /workspace/vy5-composition/corpus --out /workspace/vy5-composition/reviewed-reference --execute-reference --optimizer-also
node scripts/yul-composition/coverage.mjs /workspace/vy5-composition/reviewed-reference /workspace/vy5-composition/feature-coverage.json
```

Use the exact compiler SHA-256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`,
version `0.8.38+commit.1835d247.Emscripten.clang`, upstream revision
`1835d247de183f23e7b0e2bc4a50732af525b77c`, Osaka. Archive SHA-256:
`9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d`.
Original fixtures/expectations are immutable; compiler probes may be outside
an upstream EVM-version constraint and never become upstream matches.
`slotnum_pre_amsterdam_function.sol` retains the existing adapter's unsupported
`<amsterdam` constraint rather than silently inventing its interpretation.

## Actual coverage and proof boundary

The reference matrix has 416 compiler probes (80 upstream + 24 lane fixtures,
two pipelines, optimizer off/on): 72 observation matches, eight deliberate
corrupted-target mismatches, four precise missing-import diagnostic matches,
303 pending and 29 blocked rows. An exit 0 requires every owned local control
in every requested profile (including precise refusal, allocation sanity and
negative-target sensitivity), without missing/duplicate rows; it does not mean these pending/blocked rows passed.
The unchanged upstream adapter returned 32 working and 40 blocked fixture
reports (64 working and 80 blocked pipeline variants); eight fixture-level
adapter failures remain on their probe rows. It runs only upstream-required
unoptimized profiles, separately from the four-way compilation probes.

The actual execution adapter observes exact success/failure, return/revert
bytes, literal raw logs and deployment addresses (plus a relative `self`
projection for independent log oracles), selected deployed-account storage slots,
runtime installation bytes and reverted writes/logs. Memory effects are
observed through these outputs. It does not compare raw final VM memory,
complete account worlds/balances/nonces, adversarial callees or source-state
writeback. Mock world/memory comparison tests only test the comparator.
Reference host limits stay at the existing 100,000,000 message gas and
5,000,000 steps; host/instruction-budget exhaustion and unknown engine
exceptions are blocked. Actual EVM out-of-gas/stack-overflow are machine failure
observations, and cannot satisfy the local controls that specifically expect
`revert`. Non-memory-safe/compiler-dependent/callcode controls are advisory
AST policy scans, not evidence the absent VY1 importer implements them.
The canonical exception remains owned by the existing importer.

Dirty high bits are independently observed as `0x142` when copied directly
inside assembly and `0x42` through a Solidity uint8 return, in each tested
pipeline/settings pair. Allocation pointers and layout sanity are recorded
individually, without requiring cross-pipeline equality or asserting YQ3
refinement. Runtime installation checks are finite reference evidence only.

The modifier fixture combines an assembly `x.slot` write with Solidity reads
and post-body writes; unchecked combines Solidity overflow with assembly;
loops exercise for/while/do-while/break/continue. Separate try success,
plain/bytes/Error/Panic catches, nested creation and ordered Yul-log/Solidity-emit
controls retain their independent outcomes. The feature collector records
16 actual manifest rows across 416 AST probes, all with assembly semantic
coverage pending and zero assembly obligations closed.

Corrupted targets are explicitly separate from unmodified solc evidence.
Original installed bytes are checked and retained. The incorrect-opcode control
first validates the specified ADD slice `0x60016029015f5260205ff3` against 42,
then replaces it with SUB slice `0x60016029035f5260205ff3`; only return bytes
must differ. The always-revert control first validates the original compiler
runtime against 42, then installs `0x5f5ffd`; failure, bytes and exception must
differ, with actual exception `revert`. Every replacement is read back, and
original compiler bytes and their hash, reference bytes and successful preview,
and mutant bytes/hash/observations are retained. Neither
mutation is presented as an unmodified compiler output.

Three exact theorem signatures, all without premises, live in namespace
`Solidity.Yul.Composition.RethrowControls`:

```lean
extra_statement : memoryRethrow? [dataDecl] (block [stmt 32, stmt 32] [ref 7, ref 7]) = none
different_names : memoryRethrow? [dataDecl] (block [stmt 32 "other"] [ref 7, ref 7]) = none
malformed : memoryRethrow? [dataDecl] (Json.mkObj []) = none
```

Each is proved by kernel reduction and reports only `propext`,
`Classical.choice`, `Quot.sound` inherited through the recognizer. Seven
runtime `#guard` checks cover the positive canonical exception, absent/mismatched
declarations, wrong offset/location/type and slot references. Those paths cross
the existing opaque JSON numeric parser and are not presented as kernel proofs.
Failed `decide`/`rfl` experiments are retained in evidence, including their error
placeholders; no such placeholder or new axiom is in the passing source.
No budgets, semantic premises, observations or expected outputs were weakened.

## Concrete prerequisites still required

The ledger maps Y01/Y01.02/Y02/Y03/Y09.01 to VY1 (intrinsic scope/arity,
checked parsing, semantics and word rules); Y04/Y05/Y06/Y09.02 to VY2
(physical views, V04b MemOK, memory-safe preservation, allocation refinement
and V10/V11 layout agreement); Y08.01/.02 to VY3 (actual V12 lowering and V15
opcode/EVM correspondence); Y07.01/.02/Y09.03 to VY4 (actual V13/G42 world,
creation, returndata, rollback and log/emit observation amendment).
V04 source semantics and V04b MemOK remain explicit inputs. V16 must supply
G48 source coverage, G49.01 backend composition, G49.02 runtime theorem,
G49.03 failure/nonvacuity/progress, G50.01 deployment, G50.02 transactions,
G51.01 soundness and G51.02 specification transfer. `G51.interface` is a
prerequisite interface obligation distinct from final G51.01, avoiding a cycle.

Existing `Solidity/Roadmap/Contracts.lean` provides contract *types*:
`Admission.sound/complete`, `Lowering.dom/agrees/cert`,
`Compilation`, `Execution` and `PublicCorrectness` (coverage, both pipelines,
environment onto, fixed/session agreement, creation table, hash preimages,
refinement and reachable decode). These are not assembly instances.
Existing Bridge instruction-boundary composition explicitly excludes source
storage refinement and does not supply VY3/Y10 correctness.
The final proof must instantiate the actual contracts and discharge their real
hash/resource/environment premises, allocation/log amendments and every source
constructor. No full theorem signature is fabricated here.

## Validation and resources

Actual toolchain: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613.
Docker image digest:
`sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852`.
Each heavy invocation is serial, with `LEAN_NUM_THREADS=1`, Lean `-j1`,
Docker memory 12 GiB and memory+swap 12 GiB (cgroup swap max 0). The
attached outer cgroup has a 16 GiB hard limit and no host swap. No additional
12 GiB OS reservation was imposed. OS availability, aggregate RSS, disk and
kernel memory/OOM counters are retained. Private caches remain on disk.

| Gate | Recorded result |
|---|---|
| Exact base/branch/ancestry | Pass; original branch preserved. |
| KeySort | `lake -f lakefile.vy5.toml build Solidity.KeySort`: exit 0, two jobs; 25,776,128-byte cgroup peak, zero OOM. Temporary config supplies Lean `-j1`; tracked config unchanged. Initial unsupported Lake `-j1` attempt retained as failure. |
| Focused affected build | Body and its ten prerequisites: 11 jobs passed; existing AST unused-variable warning retained. |
| Rethrow per-file/axioms | `final-focused.log`: three scoped axiom reports plus seven guards pass. Installed local MCP 0.29.0 was later discovered and invoked through stdio: `final-mcp.log` reports success, partial=false, no errors/dependency failures. Its nonfatal Pydantic/shutdown warnings remain raw. No MCP/build overlap. |
| Mock/inventory | 31 JavaScript tests and two Python tests pass; `reviewed-backfill.log`. |
| Four-way reference | Exit 0 with eight required corrupted-target mismatches; 468,725,760-byte sampled aggregate RSS, 501,911,552-byte cgroup peak, zero OOM. |
| Full repository policy | `./run-lean.sh` via the untracked serial-config wrapper: exit 0, 981 library jobs, 262 TestSuite jobs; 377 taclets / 131 read annotations match the frozen rules. Peak sampled aggregate RSS 11,558,801,408 bytes; cgroup peak exactly 12 GiB, max/reclaim events 3438, zero OOM. Minimum observed OS availability 5,388,128,256 bytes. |
| Full public assembly closure | Pending missing actual V16/VY3/VY4 interfaces and G01 amendments. |
| Base/head comparisons | Layer check passes. Documentation checker retains the same 48 missing references; original G03 checker retains the same stale-generated-output failure. Raw base/head outputs are identical; no unrelated generated output repaired. Final newly tracked paths/links and scoped checks are recorded in the handoff. |

## Independent reviews

Separate read-only finder and skeptic reviewed implementation and subsequent
fixes, without Lean server/builds. Confirmed findings fixed: stale settings
metadata, mutable dependency/owner edges, vacuous negative controls, ignored
nested reference mismatches, omitted expected logs, missing raw replay compiles,
G51 dependency cycle, legacy-success gating of viaIR reference execution,
missing emitter identity, weak loop/modifier/constructor controls, deployment
exception classification, snapshot metadata, engine/host provenance and precise
malformed-import diagnostics. A real log run exposed object-key-order comparison;
the failed output was retained, comparator corrected and regression added.
The final expanded source is independently re-reviewed before committing; results and any remaining limitations are in the handoff. Every owned local control/profile is now required, and source-bound finite-proof registrations reject staleness without closing assembly obligations.

## Handoff locations

Absolute artifact root: `/workspace/vy5-composition`.
Evidence directory: `/workspace/vy5-composition/evidence`.
Raw final four-way reports: `/workspace/vy5-composition/reviewed-reference`.
Feature-row evidence: `/workspace/vy5-composition/feature-coverage.json`.
Pinned extraction: `/workspace/vy5-composition/corpus`.
Final handoff, original patch, Git bundle and checksum manifest are generated
at that root after committing. They contain full head/base/branch identities,
commands, exits, raw failures, resource/review evidence and all pending work.
The full assignment remains unfinished; no push, PR or merge is authorized.

## Reference adapter recovery — 2026-10-31

Reviewed recovery follows checkpoint `2f8682af36deb36b1a39c0c1cc85a482e71e360a`
on the same branch/VM. The existing full-assignment goal remains blocked; this
manual turn neither resets it nor establishes automatic continuation.
Original artifacts under `/workspace/vy5-composition` remain unchanged. New
artifacts and full committed identity are under
`/workspace/vy5-composition/recovery-20261031/handoff.json`.

The missing `args.map` field was a real adapter error: the existing parser emits
raw ABI `calldata`/`expectedBytes` vectors for bytes32, dynamic arrays and similar
signatures. The lane wrapper consumes those exact bytes with the exported
bounded engine, preserving selectors and every original call. Shared V17/legacy
scripts are unchanged. Ordered anonymous logs include literal emitter, topics,
data and order. Omitted arrows retain calls with empty expected output. Gas
metadata is retained as telemetry/profile selection, never semantic output.
The [per-fixture recovery ledger](../../tests/yul-composition/reference-recovery.json)
retains original reasons, source hashes, exact profiles and call counts.

All 44 missing-map, 30 conservative-host and six expectation-syntax blocked
variants in the previous nested reference output now execute and match. Pinned
EVMHost/ExecutionFramework inputs supply accounts, value, environment and
transaction number/time; real transaction-sequence regressions cover transient
reset and EIP-6780 new-versus-old destruction. The actual first deletion test
failed because SimpleStateManager metadata deletion leaves code; the wrapper
now explicitly clears public code/storage as well. Failed tests are retained.
EthereumJS CREATE address derivation differs from the pinned host's pre-increment
nonce convention: address-returning creation oracles are explicitly blocked;
no whole-host equivalence is claimed. No current selected fixture hits that
boundary. Blockhash history and unsupported settings remain fail closed.

Pinned SemanticTest.cpp defaults SSA-CFG on when viaIR runs. Actual compiler
probes confirm it requires `experimental:true`; the wrapper preserves that
setting and required SSA-CFG profile separately from ordinary viaIR and
explicit gas-metadata optimized profiles. The `<amsterdam` fixture accepts Osaka
according to the pinned fork ordering. Seven old-fork fixtures still exclude
Osaka: basefee_berlin_function, blobbasefee_shanghai_function, blobhash_pre_cancun,
clz_pre_osaka, difficulty, mcopy_as_identifier_pre_cancun and
tload_tstore_not_reserved_before_cancun (all `.sol`). Each retains three blocked
profiles and its exact fork reason; no expectations were changed.

Final `recovery-reviewed` command exits 0: **53 JavaScript tests, two Python
tests; 80 fixtures, 248 runtime profiles, 227 matching and 21 fork-blocked**.
The integrated 416 four-way compiler probes retain 72 matches, eight intended
mutant mismatches and four diagnostic matches; 304 remain pending and 28 blocked.
The single former blocked-to-pending probe is the repaired `<amsterdam` adapter,
not a proof pass. Nested runtime reports are separate from those compiler probes.
All raw compile inputs/outputs, provenance, observations, failures and commands
are saved in `reviewed-reference`, `reviewed-integrated` and recovery evidence.

Reports reject missing/reordered calls, changed pinned oracle/settings, omitted
profiles, malformed bytes/logs/deployment, wrong compile-input hashes and hidden
mismatches. A prior mismatch dominates a later adapter block. Independent finder
and skeptic reviews found and prompted fixes for profile labels, immutable
oracle binding, deployment evidence and compile metadata validation. Both accept
the final reference-only scope; review records are in the recovery handoff.
The integrated dynamic-import deadlock (exit 13) and earlier failing regressions
remain raw evidence, followed by passing reviewed runs.

No Lean source/import, theorem statement, proof budget, admission rule, manifest
verdict or other lane changed in this recovery. Existing gas/msize/pc/own-code,
callcode and non-memory-safe admission refusals plus canonical rethrow remain.
This external runner may observe excluded upstream programs without admitting
them. No new theorem or axiom report is claimed. Prior KeySort and full-policy
exit-0 evidence remains applicable to unchanged Lean: Lean 4.24.0
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Lake 5.0.0-src+797c613.
No redundant full Lean build was run. Existing docs/G03 exit-1 outputs retain
hashes `01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a`
and `3bada79141a6a9818dc160a9d15066bbebc678462507be4dba6130aa3371f681`.

Recovery heavy checks were serial under the writer lock, Docker memory=swap
limit=12 GiB (no added swap), one CPU and LEAN_NUM_THREADS=1. Final sampled RSS
561,205,248 bytes, minimum OS availability 17,309,073,408 bytes; zero OOM.
No proof/fuel/node/test budget increased. The final resource record includes
exact command, limits and samples; disk retained more than 19 GiB headroom.

Work 1 remains pending all 24 child obligations and six combinations; concrete
VY1–VY4/V16 and recorded V04/V04b/V12/V13/V15 contracts are missing. Work 2 and
Backfill A/B improved, but complete raw-memory/world/storage observations and
universally quantified source/target correspondence remain open. Work 3, G48–G51
and final joint kernel/import/composition gates remain pending. No dependency
preparation, compiler match or mock closes them. No new semantic question is
established; original YQ1–YQ7 authorization remains in force.

## State and memory observation checkpoint — 2026-10-31

This reviewed checkpoint follows `5d2025cfae09794e8f70784fca51d83da2f5239c`
in the same clean assigned branch and VM. The original artifact root and
`recovery-20261031` artifacts are preserved. New full head/base/branch, patch,
bundle, raw evidence and checksum paths are recorded after committing in
`/workspace/vy5-composition/observations-20261031/handoff.json`. The existing
full-assignment goal remains blocked; no reset or reactivation is performed.

The lane-owned [observer](../../scripts/yul-composition/capture.mjs) decorates
public methods on an isolated machine instance and subscribes to public events;
shared engine/parser sources, dependency lockfiles and limits are unchanged.
It discovers accounts and persistent/transient slots from actual API accesses,
not fixture expected keys. Each transaction and frame preserves pre/post account
existence, balance, nonce, code bytes/SHA256 and all discovered slot words.
SHA256 is evidence integrity, not an EVM codehash. API access counts, ordered
mutations, checkpoint/commit/revert and transient-clear payloads retain rollback
and reset evidence. Explicit next-transaction EIP-6780 cleanup includes deleted
accounts and cleared code/storage. Transaction pre-state precedes host cleanup;
frame pre-state is at beforeMessage, after engine caller-nonce handling. Frame
post-state follows the engine journal decision, and top-level cleanup may already
have reset transient slots; the pre-clear payload remains a separate observation.

The scope is the **API-touched domain since observer installation**, including
seeded host accounts. It is not Ethereum-wide enumeration or a state-root proof.
The private-token `capturedMachine` factory installs capture immediately after
the exported fresh engine constructor, before all later writes. This justifies
zero initial values for subsequently discovered slots even after a constructor
bulk clear. A generic observer with unknown preinstallation storage blocks a new
slot first seen after bulk clear; it does not infer emptiness from a nonexistent
account (the public simple manager permits detached storage). Initial transient
slots are discovered using public toJSON. Raw regressions preserve both cases.
Unknown/missing APIs or capture errors block execution evidence rather than
becoming empty state. Native/precompile internals and untouched accounts remain
outside this capture boundary.

Raw final frame memory is read through the public result memory API. Pre-opcode
LOG/RETURN/REVERT snapshots retain allocated bytes, offsets, lengths, frame and
step/PC identity as diagnostics; no PC/gas builtin is admitted. Final per-frame
last-call returndata uses public interpreter getters and remains separate from
frame output and memory. The nested-revert control distinguishes parent buffer
77, parent output42, child revert memory77 and rolled-back persistent/transient
slots0. Memory never becomes an arbitrary cross-pipeline equality. The original
allocation layout/refinement and dirty-bit controls retain their expected values.
No source-level returndata-buffer correspondence theorem is claimed.

Four source-hash-bound [controlled oracles](../../tests/yul-composition/state-oracles.json)
cover memory-storage-logs, try-catch, modifiers and constructors in legacy/viaIR,
optimizer off/on: **16 state-oracle matches**. The registration has frozen hash,
required IDs and fail-closed gate recomputation. Additional real bytecode tests
cover external balance/nonce/code, stateful calls, transient reset, nested reverted
writes/value transfer, memory and returndata. Consistent wrong slot/balance/nonce/
memory/buffer evidence mismatches despite unchanged return bytes; missing worlds,
frames, request/result bindings, oracle rows or context metadata block. Mutation
tests distinguish malformed evidence from genuinely wrong observations.

Final serial `observation-final` exits0: **73 JavaScript and two Python tests**;
80 pinned fixtures,248 runtime profiles retain **227 byte/log matches and21
old-fork blocks**. Working upstream profiles record674 unique transaction
captures and838 frames, including838 final memory and last-call-buffer captures,
plus765 pre-opcode memory regions. Their independent whole-state comparisons
remain explicitly pending. The [observation coverage ledger](../../tests/yul-composition/observation-coverage.json)
records exact per-fixture/profile counts and the16 controlled matches. Projection
against original report SHA256
`0183a26c65468d780c31e74a7fd1ed127d601eb43b9f96f9cd36555cef6c678c`
confirms unchanged sources/settings/profile identities, input hashes, all calls,
failure/bytes/logs, metrics, gas telemetry and cleanup evidence. Seven older-fork
constraints are unchanged. The separate416 compiler probes retain72 matches,
eight intended mutant mismatches,four diagnostic matches,304 pending and28
blocked. AST coverage remains16 manifest rows with **zero obligations closed**.

Separate read-only finder and skeptic reviews (without Lean/server/build) found
and prompted fixes for frame-domain omission, request/result binding, vacuous or
missing oracles, provenance hashes, unknown prevalues after clear, fresh-constructor
handling and nested context metadata. Both accepted final source and scope;
raw early probe/focused failures remain alongside passing runs. Reviews, exact
commands and per-run resources are in the new handoff. The final run used the
writer lock, one CPU, LEAN_NUM_THREADS=1 and aggregate Docker12GiB memory with
memory-swap equal12GiB (no swap allowance). Sampled peak RSS1,091,117,056 bytes;
minimum OS availability16,802,652,160 bytes; no resource stop/OOM. More than16GiB
disk headroom remained. No engine step/gas or proof/test budget increased.

Work2 and BackfillA/B advance through concrete capture and controlled oracles;
full source/target world, storage, memory and returndata comparisons remain
partial. Work1/3, all24 obligations, six combinations and final joint Y10/G48–G51
kernel/import closure still require actual VY1–VY4/V16 and the other recorded
owner interfaces. No Lean source/import, intrinsic representation, theorem,
premise, axiom or budget changed; no new kernel gate is claimed. Prior KeySort
(two jobs,exit0) and full policy (981 library/262 TestSuite jobs,exit0) are attributed
to their tested earlier tree, whose Lean files are unchanged. Actual toolchain
remains Lean4.24.0 `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Lake5.0.0-src+797c613.
Baseline docs/G03 exit1 failures are preserved; scoped new paths and ownership
are checked without repairing unrelated history. Existing YQ1–YQ7 decisions,
admission refusals and canonical-rethrow exception remain unchanged. No new
semantic/profile decision is needed for this external observation checkpoint.

## Finite state oracles — 2026-10-31

This reviewed checkpoint continues `c8a35ef7134a6d3966d4afd2b7b531881141d6d1`
in the same VM/branch. All earlier patch/bundle/handoff/evidence manifests remain
unchanged. New committed head, commands and checksums are recorded after commit
at `/workspace/vy5-composition/oracles-20261031/handoff.json`. The existing
full-assignment goal stays blocked, without reset/recreation/reactivation.

Independent expectations were recorded before the new control executions in
`oracles-20261031/before-execution-premises.json`. The unchanged fixture sources
and original expected verdicts remain authoritative. The
[seven-row local registry](../../tests/yul-composition/state-oracles.json) and
[five-fixture upstream registry](../../tests/yul-composition/upstream-state-oracles.json)
carry source hashes and explicit premises; frozen registry hashes, required IDs,
call order and recomputation reject missing/stale/forged matches. The
[oracle module](../../scripts/yul-composition/oracles.mjs) predicts identities
before execution: self is CREATE(fixed caller,nonce0), child is CREATE(self,nonce1).
Tests independently check the short RLP/Keccak formulas. Neither createdAddress,
storage contents nor getter output supplies an expected address/value.

The three added existing local controls are:

- **mixed-logs:** Yul LOG0 emits word42, followed by Solidity anonymous E(word43),
  both from independently predicted self. Two ordered, length32 memory windows
  are checked at their actual LOG0 offsets. No absolute buffer address or
  cross-pipeline pointer equality is assumed.
- **new-constructor:** C starts nonce1; its single zero-value CREATE uses nonce1,
  advances C to2 and creates D with nonce1,balance0,slot0=42. Exact ordered frames
  include creation then the x() static getter returning42. Created runtime bytes
  must actually be installed at the predicted child; this is a finite installation
  relation, not a compiler correctness proof. Creator/caller balances and nonces,
  pre/post child state and getter identity are checked in all four profiles.
- **constructor-failure:** the deployment-phase `runCall` reverts with empty
  bytes/logs. The predicted candidate retains no account/code or known slots;
  persistent/transient journal rollback and REVERT(0,0) frame/memory evidence are
  required. The caller nonce advances0→1 outside the message checkpoint in this
  genuine runner. The returned candidate address is explicitly distinct from a
  retained deployed account. No `runTx`, fee accounting, account-deletion or
  unavailable transaction-finalization behavior is inferred.

Together with the previous four controls, all seven match **28 compiler profiles**
(legacy/viaIR, optimizer off/on). Wrong child address/slot/nonce/balance/code,
missing getter/installation/phase, retained failed-candidate effects, reordered
logs, malformed/missing memory and stale source/registry evidence fail. Mutations
preserve equal return bytes/logs where appropriate, so a byte-only result cannot
stand in for an independent state assertion.

Selected upstream source-derived assertions now match **15 profiles /30 calls**:
slot_access (keccak256(word1||word0), ordered a=0→4,b=0),
inline_assembly_memory_access (ABI bytes5=ASCII12345),
optimize_memory_store_multi_block (f=0x42,g=true, RETURN-relative windows),
optimize_memory_store_multi_block_bugreport (x=5 and original64-byte LOG0 window),
and transient_storage_creation (put/read42, explicit pre-clear42, final transient0).
These are finite selected assertions;212 working upstream profiles still have
pending independent state oracles. Seven older-fork fixtures retain21 blocked
profiles. Memory checks use semantic LOG/RETURN windows and preserve allocation
freedom. The reference engine's CREATE convention is explicit; this does not
prove its address convention agrees with the pinned C++ host.

Raw frame logs now have explicit captured/not-provided status and are bound to
separately recorded output logs. Account and slot access evidence is indexed by
frame and must occur in both corresponding worlds and declared slot domains;
coordinated snapshot/domain deletion no longer passes. A nested third-party
BALANCE regression checks the account-only case. Definite mismatches dominate
later missing-state blocks. Required selected controls cannot silently disappear
by changing their status to blocked.

The first new focused run retained a real failure: transient toJSON represents
42 as minimal bytes `0x2a`, not a padded word. The adapter now validates/decodes
that raw payload only for comparison, retaining the original raw bytes and
unchanged expected word42. Wrong0x2b mismatches; malformed payload blocks. No
expected value was changed to match an output. Read-only finder and skeptic
reviews accepted the fixes and final scope; raw failed and passing exits remain.

Final `oracles-final` exits0: **91 JavaScript tests and two Python tests**;
80 fixtures/248 profiles retain **227 byte/log matches and21 fork blocks**.
The separate416 compiler probes still contain72 matches,eight intended mutant
mismatches,four diagnostic matches,304 pending and28 blocked. Original
source/settings/input hashes, ordered calls, failure/bytes/logs, metrics/gas
telemetry and cleanup evidence match the previous checkpoint exactly. The
[coverage ledger](../../tests/yul-composition/observation-coverage.json) records
all finite state matches separately;674 transactions/838 frames and765 memory
regions remain captured. AST presence covers16 manifest rows and closes **zero**
proof obligations.

Heavy gates ran serially with the existing writer lock, one CPU,
LEAN_NUM_THREADS=1, aggregate12GiB Docker memory and equal memory-swap limit
(no swap allowance). Final sampled RSS1,029,709,824 bytes, minimum OS availability
16,783,130,624 bytes, zero OOM/resource stop; more than15GiB disk headroom remained.
Gas/step/proof/test budgets are unchanged. No shared engine/parser/dependency lock,
fixture source/expected verdict, admission rule, Yul owner implementation or
G03 obligation changed. Lean source/imports are unchanged, so no new kernel pass
is claimed; the inherited KeySort exit0/two jobs and full-policy exit0 remain
attributed to their tested earlier tree. Actual Lean4.24.0 commit797c613 and
Lake5.0.0-src+797c613 are retained. Docs/G03 exit1 baseline evidence remains;
new links and zero-new-findings are checked without unrelated historical edits.

Work2/BackfillB now include independent finite state oracles for the three
requested locals and five selected upstream sources. Work2 and BackfillA/B
remain partial: unselected upstream state expectations, untouched/native worlds
and universally quantified source/target/storage/memory/returndata correspondence
are open. Work1/3, all24 obligations, six combinations, G01 amendments and final
joint Y10/G48–G51 kernel/import closure still need actual VY1–VY4/V16 and recorded
owner interfaces. No axiom/sorry, weakened theorem/premise or generic proof wrapper
is introduced. YQ1–YQ7 authorization and canonical-rethrow exception are preserved;
no new semantic/profile question is established.

## Physical and ordered-state backfill — 2026-10-31

This reviewed checkpoint follows `be8a5a17f1eb7e0e61e833bab979e56fe04f461f`
in the same assigned VM/branch. All earlier artifacts and checksum manifests
are preserved. New full committed identity and exact commands are exported after
commit in `/workspace/vy5-composition/physical-20261031/handoff.json`. The existing
full-assignment goal remains user/auditor-confirmed blocked and untouched;
get_goal is not exposed. No new goal/status transition is assumed.

Source-derived expectations were saved before new EVM execution in
`physical-20261031/before-execution-physical21.json`,
`before-additional-execution.json` and `before-execution-pinned.json`.
The [expanded registry](../../tests/yul-composition/upstream-state-oracles.json)
contains39 sources, each with its original source hash, full ordered source-plan
hash, explicit call assertions and pending-domain boundaries. No expected values
were copied from VM slots, addresses, code or returns. Frozen registry hashes
and required IDs reject stale/missing registrations.

The new physical controls cover all four storage-access variants and the mapping
pointer case. Packed uint16 x/y use slot0 at offsets0/2, z uses slot1; storage
array a aliases length slot0; a struct behind a separator uses slot1. Ordered
writes/readbacks preserve7. Separator slots are asserted zero only where actual
source getters access them, never by filling unavailable state. Mapping pointers
return roots0/1/2 and offset0 without reading mapping contents.

MCOPY cases derive destination bytes from the original literal input and
EIP5656 temporary-buffer semantics, covering both overlap directions, in-place,
non-overlap and zero-length copy. Only the semantic RETURN-relative ABI byte
window is compared; no absolute allocation address or arbitrary final compiler
memory is equated. Zero-copy optimizer elimination is allowed by the source
semantics: the oracle does not invent an MCOPY opcode-count requirement. Wrong
forward-overlap results and changed bytes fail while reported return bytes/logs
are kept unchanged; missing memory/phase/frame evidence blocks.

All currently unselected transient_storage_* sources and the inline transient
Yul-function case now have finite assertions. Tests distinguish transient slot1
from packed slot0, shared state across8ordered selfcalls, reset between configured
top-level calls, constructor/runtime phases, persistent versus transient stores,
internal reentry rollback and caller-owned delegatecall effects. Exact nested
self-call selectors/arguments and return words are independently predicted.
The CREATE2 low-level case explicitly leaves target identity/code/target-owned
state pending; only independently known self nonce/slot/window assertions are
counted. The unsalted selfdestruct case predicts children from self nonces1/2 and
checks the stored address, known child state and transient42 before cleanup.
Newly created-child deletion after an unavailable next boundary is not inferred.
These are runCall/frame/explicit cleanup controls, not runTx, fees, native-world
or transaction-finalization proofs.

Productive source-derived backfill continued beyond that physical subset with
18 function/stack/control/calldata cases: multi-result assignment and nested
functions, ASCII bytes32 padding, sum45, break/continue/nested loops, factorial
witnesses0..4, if/switch/leave, the condition-sideeffect loop and three calldata
array cases. The sideeffect loop independently predicts ordered slot0 prevalues
0/2/4 and postvalues2/4/2. Fixed memory offset0 is asserted only for explicit
source Yul return(0,n); other ABI windows remain RETURN-relative. Calldata offsets
0x44/0x84 follow the source input encoding, not a memory-allocation policy.

Review found a real request-binding gap: duplicated requestData/capture fields
could be changed together. The adapter now reconstructs runtime selector plus
full arguments from the pinned source plan. Constructor argument suffixes and
initcode-prefix SHA256 must match the pre-EVM compiler receipt. This hash is
receipt linkage, not an expected state/address derived from observed code.
Coordinated selector/argument/initcode mutants with unchanged outputs now fail.
Each call also binds value, ordinal and actual capture transaction; per-call
missing data cannot erase an earlier definite mismatch. No source semantics,
expected verdict, admission exclusion or proof premise was weakened.

Final `physical-final` exits0: **131 JavaScript tests, two Python tests**;
80 fixtures/248 runtime profiles (required defaults plus named metadata profiles) retain **227 byte/log matches and21
older-fork blocks**. **39 upstream sources /121 profiles /275 ordered calls** now
have finite independent assertions. **106 working profiles** still lack such
oracles, and selected partial domains remain separately pending. Seven original
local controls retain28 profile matches. The separate416 compiler probes still
partition72 matches,eight intended mutants,four diagnostic matches,304 pending
and28 blocked. Complete original source/settings/plan/profile/input hashes,
ordered calls and actual bytes/failure/logs/metrics/gas telemetry/cleanup are
unchanged. The [coverage ledger](../../tests/yul-composition/observation-coverage.json)
records the exact per-profile assertions and pending domains. Captures remain
674 transactions/838 frames/765 regions; AST presence is16 feature rows with
**zero kernel obligations closed**.

Both independent read-only finder and skeptic reviewed source, new derivations
and final accounting without Lean server/builds. The intermediate authoring
function-boundary mistake was caught before execution, preserved, corrected,
and syntax-checked; its authoring-process exit0 is not a kernel/runtime gate.
Raw failed cache/absence probes and shell edits are retained in the new evidence.
The passing final scripts are separate from those raw operations.

Published master was inspected by immutable-object fetch and git show only,
without ref/worktree/index integration. Initial readback was
`93920309f5c800c9ce4809bc74700ed4fde65fb2`; it advanced during audit to
`4165de133bafd522ab18099e18cad489bb1aa7d6` (published memory integration). The
stale-commit audit exited1 and was preserved; the new exports were inspected
again read-only. Both snapshots have no core Solidity/Yul or
SolcJson/Yul exports or Yul imports in its public root; InlineAssembly still
recognizes canonical rethrow only. Existing pure Scalar composition exports are
present, but are not assembly correctness interfaces. Thus actual assembly
Y01–Y09/VY1–VY4 and V16 joint coverage/correctness exports remain unavailable;
this does not assert that general prerequisite lanes are wholly absent. Raw
commands, exact exports/excerpts and fetch outcomes are in
`physical-20261031/owner-export-readback.json`, `owner-export-readback-latest.json`
and `published-master.json`. Published try/memory components are available; no
claim is made that their general owner lanes are missing, and none was integrated.

Heavy gates ran serially under the existing writer lock, one CPU,
LEAN_NUM_THREADS=1 and aggregate12GiB Docker memory with equal memory-swap limit
(no swap allowance). Final sampled RSS1,041,383,424 bytes; minimum OS availability
16,780,316,672 bytes; zero OOM/resource stop, more than13GiB disk headroom. Original
step/gas/proof/node/test budgets are unchanged. No Lean source/import changed,
so inherited KeySort exit0/two jobs and full-policy exit0 remain attributed to
the earlier tested tree; no new kernel gate is claimed. Actual Lean4.24.0 commit
797c613 and Lake5.0.0-src+797c613 are retained. Historical docs/G03 exit1 failures
are preserved against the exact base, with new links checked separately.

Work2 and BackfillA/B improve through these external controls but remain partial:
unselected and explicitly pending state domains, whole-world/source/target/
storage/memory/returndata correspondence remain open. Work1/3, all24 proof
obligations, six constructor combinations, G01 amendments and final joint
Y10/G48–G51 kernel/import closure still require actual assembly-compatible owner
interfaces. No other-worker integration, shared engine/parser/lockfile rewrite,
fixture/verdict change, axiom/sorry, budget increase or publication occurred.
YQ1–YQ7 and canonical-rethrow behavior remain intact; questions remain empty.

## Remaining finite-oracle backfill — 2026-10-31

Starting checkpoint ec708bf11d7fd6f0b5abf521d9fab58b4d47bf1a is preserved.
The remaining34 working upstream sources now have source-derived assertions:
calldata offsets/lengths and alias assignments, pure/control/constants/function
pointers, explicit host/environment inputs, Fixed Keccak windows/storage,
selfbalance and reverted/static transient effects. The unchanged original call
plans, bytes/failure/log expectations, settings and required profiles are retained.
Selected RETURN windows describe semantic bytes and relative regions; compiler
allocation addresses are not compared across pipelines. Dirty-bit differences
and original failure verdicts remain intact. Expectations were saved before
execution in the new artifact directory below.

All73 working sources now have finite independent assertions:227 profiles and
458 ordered calls, with21 older-fork profiles still blocked. The complete
original compiler/runtime receipt and observation projection matches the
previous physical checkpoint exactly. This is finite selected-domain evidence,
not complete memory, untouched-world or source/target correspondence. The
[coverage record](../../tests/yul-composition/observation-coverage.json) retains
per-profile pending domains. Local controls remain28 profiles. The416 compiler
probes remain72 matches, eight intended mutant mismatches, four diagnostic
matches,304 pending and28 blocked; zero kernel obligations closed.

CREATE2 target addresses are independently calculated from caller, salt and
receipted initcode. The source hexadecimal bytes32 literals are right-padded,
not numeric words. The initial authoring oracle used numeric salt padding;
focused run v1 correctly failed (164/165 JS tests, exit1). That raw failure and
the corrected source derivation are preserved. Final checks bind each predicted
target to nonce/balance, nested CREATE2 initcode, compiler-receipted runtime and
transient state owner. These are compiler-receipt-relative finite controls,
not compiler correctness proofs or independent runtime-byte semantics.

For the existing selfdestruct fixture, five profiles additionally capture the
actual supported host beginFrame cleanup after the complete original plan.
The separate record verifies deletion of the newly created child, survival of
the older child, state/slot clearing and transient reset. It adds no source call
and does not label runCall as runTx or claim consensus transaction finalization.
Missing, reordered, malformed or wrong owner/address/code/nonce/state evidence
fails closed. Equal-return mutations cover calldata windows, hash slots, funding,
CREATE2 inputs/receipts and cleanup, alongside all original eight mutants.

Final serial gate:183 JavaScript tests and two Python tests passed; pinned solc
0.8.38/Osaka reference227 working/21 blocked; integrated matrices and feature
coverage passed with the counts above. Exact commands, exits and raw outputs
are in `/workspace/vy5-composition/evidence/remaining-final.*`.
The writer-locked bounded runner used one CPU, aggregate12GiB memory and equal
memory-swap limit, LEAN_NUM_THREADS=1, unchanged engine budgets, no OOM/stop;
peak sampled RSS1,032,871,936 bytes, minimum OS availability16,751,665,152 bytes.
No Lean source/import changed: earlier Lean4.24.0/Lake5.0.0-src+797c613,
KeySort exit0/two jobs and full-policy exit0 remain attributed to their tested
tree. Historical docs/G03 exit1 baseline failures remain failures.

Independent read-only finder and skeptic reviews, without Lean server/build,
accepted the source changes after the CREATE2 fixes; final documentation and
accounting reviews are retained in the new handoff evidence. No shared replay,
parser, dependency lock, fixture/verdict, admission, shared G03 obligation ledger
or owner file changed.
Published master4165de133bafd522ab18099e18cad489bb1aa7d6 has general memory/try
components but no assembly correctness exports, as recorded in the prior exact
immutable-object readback. No worker integration occurred.

Work1 and Work3 remain blocked; Work2 and BackfillA/B remain partial for complete
assigned observation/source correspondence and owner wiring. All24 obligations,
six combinations, G01 amendments and concrete joint Y01–Y09/Y10/G48–G51 kernel
and import closure remain pending. No generic theorem replaces those proofs.
The existing full-assignment goal remains blocked and untouched; get_goal is
not exposed in this turn. YQ1–YQ7 remain authoritative; no new question arises.
New versioned patch, bundle, handoff, raw evidence and checksums are under
`/workspace/vy5-composition/remaining-20261031/`; all earlier manifests/artifacts
are preserved. This checkpoint does not complete the original lane.


## Parallel consumer interface — 2026-11-01

The human scheduling amendment permits actual peer inputs in a private tree.
Preserved checkpoint916ad2c5; verified immutable VY3 checkpoint250555de and
VY4 checkpoint9c631ecb are staged, with exact source hashes in
[producer inputs](../../tests/yul-composition/producer-inputs.json), at
`/workspace/vy5-dependencies-20261101` (provenance commit921a3b4b).
The assigned branch contains only VY5 modules, not producer definitions.

[Interface](../../Solidity/Yul/Composition/Interface.lean) exports
`Solidity.Yul.Composition.completeAndCopy` over actual VY4 `Effects D L T`,
address-indexed source layouts, explicit operations/logs/outcome, strict source
window coordinates, destination and existing target byte-memory `Slice`.
Its result is `Option (Effects D L T × Slice)`. Failure is not replaced by empty
bytes. `literalSum : UInt8 → UInt8 → Compilation.Slice 0 1` consumes actual VY3
arity-indexed literalPair/addWords. No invented producer AST/state semantics,
axiom, opaque obligation or assumed correctness theorem is introduced.

[Concrete](../../Solidity/Yul/Composition/Concrete.lean) proves rollback plus
copy, exact selected bytes/outside-memory preservation, failed completion then
successful completion, strict nested windows and concrete numeric ADD over any
caller tail. Operations/logs/outcome remain explicit inputs; this is not source
try/catch adequacy. Copy generates PUSH/MSTORE8 constants from supplied outcome
bytes under the existing gas/stack-exception-free target executor; it is not
RETURNDATACOPY lowering or EVM correspondence. Bounds and destination fit are
real theorem premises. All successful axiom reports contain only standard axioms.

[Controls](../../Solidity/Yul/Composition/Controls.lean) executes inhabited typed
worlds with slot7, stale returndata and caller logs, supplied child write42 and
nonce increment, copying ab/cd across31/32 with sentinels30/33 and stack99.
Revert yields slot7/nonce0/one log; success slot42/nonce1/two logs. Wrong-result
ADD, underflow and zero-length out-of-bounds controls remain negative.
Private affected build54jobs and per-file installed MCP diagnostics pass for
all three modules (success=true, partial=false, no errors). Failed initial
Lake CLI, namespace/list-normalization and witness syntax attempts are retained.
Independent finder/skeptic reviews use no Lean server/build; their requested
scope and inhabited-witness fixes are incorporated. A failed documentation
shell command was corrected before commit and is not a passing gate.

This early interface package is a dependency input, not full lane delivery.
VY1/VY2 packages remain in transfer; exact required dirty-local/physical facts
and remaining compiler/world adequacy contracts are named in producer inputs.
All24 full obligations/six combinations remain pending. New concrete component
laws do not relabel them complete. Final combined root/full policy gates remain
required; no new RUNTIME_GATE_PASS is claimed. The prior finite controls and
immutable artifacts are unchanged. New evidence/package paths are under
`/workspace/vy5-composition/parallel-20261101/`.


## Parallel concrete components — 2026-11-01

Continued after the early interface checkpointe75bad809cfda97eedc97d694eaeeac3243ae353.
[TargetRepeat](../../Solidity/Yul/Composition/TargetRepeat.lean) proves actual
ADD execution for every finite repetition and arbitrary caller tail, including
wraparound controls. It is not a source for/while or compiled-jump theorem.
[ScopeTransport](../../Solidity/Yul/Composition/ScopeTransport.lean) transports
the computed ADD result through the actual VY3 newer-prefix/SWAP/POP operations
to an indexed outer local and reads it back. Both Fin bounds and depth<16 are
explicit. This is not a source modifier/library calling convention or real-EVM
stack-capacity theorem. [WordBridge](../../Solidity/Yul/Composition/WordBridge.lean)
losslessly connects existing Roadmap Fin256 words to VY3 BitVec256, proves both
round trips and actual modular ADD agreement, preserving511 rather than cleaning
to255. It defines no new word semantics or dirty/narrow source-local policy.

The [component ledger](../../tests/yul-composition/component-ledger.json)
registers13 selected ready component facts, current module hashes, every original
24obligation and all six combinations, with precise ready/pending producer facts.
There are15 named checked component laws including helpers/negative discrimination;
all scoped axiom reports contain only standard axioms (some round trips use none).
No full obligation or source combination is relabeled complete. The original
ledger only gains a narrow link to this record; source admission/manifest and
all original expected verdicts remain unchanged. Core layer registration adds
only the composition namespace; public-root producer integration stays private.

The newly delivered immutable V16 checkpointbea6e0e334f448aebb6f7c7a68321b4e419b43d2
was SHA256/bundle verified. Its compatible Transport/Relational modules were
staged exactly in the private tree. [V16 input record](../../tests/yul-composition/v16-producer-input.json)
and [checked signatures](../../tests/yul-composition/V16Signatures.lean) identify
actual completion_at_need/composed_completion/composed_observation declarations.
General interfaces are available; actual assembly Lang/pass/Cert, Forward,
Guard, Allowed/Admissible and composition closure/completion inputs are still
owed. No generic certificate law is presented as concrete assembly adequacy.
Other producer files, shared engine/parser/lockfiles and active checkouts were
not rewritten or imported into the assigned branch.

[Component driver](../../tests/yul-composition/ComponentDriver.lean) executes
actual checked world/word/target components and emits actual backend ADD bytes.
[Runner](../../scripts/yul-composition/component.mjs) compares selected projections
against exact encoded target execution and the independently saved
[Solidity control](../../tests/yul-composition/ComponentControls.sol), pinned
solc0.8.38/Osaka in legacy/viaIR with optimizer off/on. It retains constructor,
pair and caught-call captures, success/failure/bytes/ordered logs and touched
state, original compiler receipts, runtime installation hashes and identities.
Compared projections are ADD259, returnedabcd, caller log11 and final slot7;
the synthetic Lean nonce operation and arbitrary final compiler memory are
not asserted equal to the Solidity run. Copying supplied outcome bytes remains
PUSH/MSTORE8 materialization, not RETURNDATACOPY lowering or an EVM proof.

Optimized solc removes the reverted SSTORE42. Original unoptimized captures
show the write; all profiles retain slot7, ordered caller logs and exact bytes.
An initial guard requiring this unobservable write in optimized traces failed
and is retained; internal trace agreement is explicitly pending, not silently
identified. Independent reviews found dropped pair failure/logs, weak producer
registry identity and encoded deployment provenance/report gaps. Fixes bind
actual results to every capture, fixed caller/zero value, independent selectors,
exact ordered profiles, compiler input/output receipts, installed runtime and
frozen producer identities. Missing/malformed/stale/reordered evidence,
coordinated equal-byte revert/log/state/owner/request mutations and false proof
closure all fail closed. Finder/skeptic reviews use no Lean server/build.

Final private joint policy gate passed explicit KeySort build2jobs, library1005
jobs, TestSuite262jobs and SolKey377taclets/131read annotations. Actual Lean4.24.0
commit797c613 and Lake5.0.0-src+797c613 are recorded before the successful gates.
Installed per-file MCP checks pass all six own modules, driver and V16 signature
file with success=true, partial=false, no errors; nonfatal server shutdown
warnings remain raw. After final report fixes,192JS+2Python pass; four component
compiler profiles and exact encoded target match. Original reference227working/
21fork-blocked and416compiler probes72match/8intendedmismatch/4diagnosticmatch/
304pending/28blocked remain unchanged. Strict check491automatic/61budgeted/
0manual/11refuted/0pending and source/TestSuite trust audits pass with zero
findings. These legacy strict rows do not discharge the assembly ledger.

Heavy checks remain serial, LEAN_NUM_THREADS=1/Lean-j1, aggregate12GiB/no swap,
with OS/RSS monitoring and the writer lock. The combined kernel/script gate sampled
RSS1,744,191,488 bytes with minimum OS availability16,871,350,272 bytes, no OOM or
resource stop. The final complete-import policy gate sampled RSS1,743,634,432
bytes and minimum OS availability17,568,440,320 bytes, also exit0. A targeted
orphan audit initially found four unregistered supplied VY3 controls; all four
were registered privately and the final closure has zero orphans. Exact
transitive producer bodies match their commits (48VY3/16VY4/6V16 modules).
Disk reached370MiB due duplicated stopped-container caches; every
new cache file was hashed/preserved in independent disk objects before retiring
only redundant new stopped containers. All earlier containers/caches/artifacts
remain intact. Mutable input-index versions were all retained and latest chosen
explicitly; future checks share a persistent disk cache. A final audit caught
one5388-byte mutable index still sharing an old object inode. Its exact original
bytes were recovered from another retained index version, verified against the
original SHA256, and isolated atomically; all saved cache objects now verify.
The cause/fix is retained in cache-index-recovery.json. More than6GiB headroom
was restored. No proof/gas/step/node/test budget increased.

Work1/Work3 now have concrete component/kernel progress and remain partial;
Work2/BackfillA/B remain partial for universal correspondence and actual producer
wiring. VY1/VY2 packages are not delivered in the inspected exchange index;
physical ownership/writeback and dirty-local/source execution remain exact
producer inputs, alongside specific compiler/world/V16 certificates and G01
amendments. Concrete full Y01–Y09/Y10/G48–G51 closure is unfinished. New ready
facts do not count as final coverage or solve all original queues. Existing
get_goal read tool is unavailable; no new/reset goal or competing continuation
is created. New reviewed patch/bundle/handoff/evidence/checksums are under
`/workspace/vy5-composition/parallel-20261101/final/`; the early immutable package
and all six earlier checksum manifests are preserved. Historical docs/G03 exit1
failures remain failures with exact-base equality, checked separately.


## Actual physical/source consumer checkpoint — 2026-11-01

Continuation of the original frozen assignment, based on reviewed checkpoint
0a3d13bc70bbf076eeab9a553c347e9e4dcccd25 and pinned base
0b078cefaf7daad79007b87b72df64eb6936420f. The earlier missing-VY2-package
condition is resolved by verified physical checkpoint
2bb7bb20852e986f81a44aaaadfda104cac9c3f4. Bundle SHA256
fd2a31455a32aa05f1ff64853c5c3bc950d36b436df91c6045c7bec99c00d711 and
archive SHA256 a3c0d4258ebf35e2a69107236f381f1497512ca7dedb38df12f5eb4a9e1c5b2b
match the delivered immutable input. All455 archived files match its committed
Git tree. The union of151 required source files was checked against that tree;
128 new producer files were staged with no conflicting existing bodies. These
are private dependency inputs, not producer completion or master publication.

The private tree `/workspace/vy5-dependencies-20261101` extends prior validated
3d25df6a6a74d8df936b112aba880cae2d751faa through physical stage
527be7e1b529ec31c1269a8b215296f8034b6ddc to reviewed consumer tree
a3b983b7abafbf299a0b2ac4452a55c849d6e37b. Producer definitions are unchanged.
Only this private root imports the new physical consumer closure; the assigned
branch does not pretend its unsupplied producer imports build standalone.
[Physical producer receipt](../../tests/yul-composition/physical-producer-input.json)
records exact paths/hashes and remaining facts.

Four new intrinsic consumer modules add26 named kernel laws:

| Module | Concrete result and real premises |
|---|---|
| [PhysicalFrames](../../Solidity/Yul/Composition/PhysicalFrames.lean) | Successful represented preparation and exact request/account equality link the public physical write to the actual Source.applyOp action. Persistent full-word/MemOK additionally requires nonstatic context, persistent bank, source MemOK and finite separation. The same source action projects into actual VY4 completion/target copying; child success then outer rollback restores source, complement journal and owned-byte journal together. |
| [PhysicalBytes](../../Solidity/Yul/Composition/PhysicalBytes.lean) | Strict actual returndata window agrees with physical byte reads/copy and actual VY3 materialization, given valid physical source range and bounded target extent. Empty physical copy beyond a word is distinguished from an invalid strict returndata window. |
| [PhysicalControls](../../Solidity/Yul/Composition/PhysicalControls.lean) | Uses the producer's ownedOriginPlan/Run unchanged: raw0xab000002 makes logical bool true while preserving the original owned byte2 and padding. Real child raw0xcd000003, static refusal, complete source/journal rollback, memory sentinels, wrong owner/slot and stale owned-byte/padding controls are inhabited. |
| [PhysicalMemory](../../Solidity/Yul/Composition/PhysicalMemory.lean) | Actual typed heap lookup and MemoryImage encoder, concrete Placement, byte bound, reserved-word invariant, strict window and target bound imply reserved-word preservation and target/physical byte agreement. All65 producer placements, including different/unaligned addresses, supply the same payload byte. This is read/encode agreement, not an allocator or G01 refinement theorem. |

Exact dependent indices/signatures/premises and scoped axiom reports are in
`/workspace/vy5-composition/physical-source-20261101/Signatures.lean` and raw
`/workspace/vy5-composition/evidence/physical-source-joint-policy.log`.
All26 new laws have only standard propext/Classical.choice/Quot.sound where
needed, or no axioms. No new axiom/sorry, admission change or raised budget.

The precise physical/world gap remains explicit: VY4 Effects carries execution,
full-topic logs and returndata, but not VY2 complement/owned-byte journals or
Source.EMState locals/heap. The consumer projects execution and supplies the
world log prefix/buffer explicitly; Source.St.logs has a different encoding and
is not silently converted. Same-frame algebra is not an actual Yul call theorem.
No new replacement world semantics, allocator refinement, dirty-local cleanup,
full memory-safe-block preservation or Y07/compiler adequacy is certified.

[PhysicalDriver](../../tests/yul-composition/PhysicalDriver.lean) executes the
actual source/physical and target definitions. A separately source-derived
[Solidity control](../../tests/yul-composition/PhysicalControls.sol) preserves the
same diamond storage layout at42, bool slot43 and both raw writes. Pinned
solc0.8.38+1835d247/Osaka, legacy/viaIR with optimizer off/on, each executes the
same ordered8-call plan: peek; outer child-success/revert; peek; first write;
static child refusal; peek; successful child; peek. All4profiles/32calls match
independently specified logical/raw results, ordered empty logs, finite pre/post
slot42–48 maps, deployed/caller accounts, semantic RETURN/REVERT byte windows,
child identity, and raw rollback writes. Return windows use relative offsets,
not equality of arbitrary compiler-final memory or allocation pointers. Native
runCall nonce changes are retained as engine host behavior; it is not runTx.
Source static revert[] and native static-state-change exceptions are retained
separately; no halt-class correspondence is inferred.

The [runner](../../scripts/yul-composition/physical-source.mjs) binds all151
producer bodies, current consumer bodies, retained actual Lean stdout/stderr,
command/exit metadata, exact source/settings/profile/call identities and raw
compiler receipts. Missing evidence is an error; no empty-state fallback or
mismatch-to-blocked downgrade. The frozen
[physical ledger](../../tests/yul-composition/physical-component-ledger.json)
registers26 facts and keeps24 full obligations/six combinations pending. The
existing13-fact registry is extended only with delivered producer provenance;
its earlier actual component controls and exact emitted ADD replay still pass.

Focused per-file MCP diagnostics pass all4new modules and driver with
success=true, partial=false and no errors; nonfatal server shutdown warnings
remain raw. Explicit KeySort passes2jobs on Lean4.24.0 commit797c613 and
Lake5.0.0-src+797c613. Required `./run-lean.sh` passes1137library jobs,
262TestSuite jobs and SolKey377taclets/131read annotations. Layer check184core/
0elaborator and orphan check1152reachable/0orphan pass. Strict check retains
491automatic/61budgeted/0manual/11refuted/0pending. Scoped signatures/axioms pass.
The encompassing shell command exits126 only after these gates when direct
trust-wrapper invocation lacks execute permission. A bash retry exits1 because
the minimal image lacks Git; both failures remain raw. Feeding the host's exact
NUL-delimited private-tree file inventory to the unchanged trust checker passes:
1167sources/246inventoried sites/0findings, exit0. No successful build was rerun
to conceal these invocation failures.

All247JS+2Python tests pass serially, including missing/reordered profiles/calls,
wrong owner/slot/owned byte/padding, rollback, child caller, static flag, semantic
memory, retained Lean execution, stale producer/source/runner/oracle/ledger
hashes and false closure. Prior component4profiles/encoded ADD match after the
intentional producer receipt extension. Prior227working upstream byte/log
profiles with finite assertions/458calls,21older-fork blocks and eight intended
mutants are unchanged and remain attributed to their sealed reports; the
unmodified full upstream command is not rerun as new evidence.

Independent read-only finder and skeptic reviews used no Lean/server/build.
Both accepted the typed heap theorem and found evidence-reader gaps: deployment
identity/install code, missing physical-ledger validation, retained actual Lean
execution, pre-state and nested child request binding. All confirmed findings
were fixed and mutation-tested; separate final rereviews accepted the fixes
with no remaining concrete finding. Raw reports are exported with this handoff.

All heavy checks are serial under the existing writer lock, LEAN_NUM_THREADS=1,
Lean-j1, enforced aggregate12GiB/equal memory+swap (no swap), with OS headroom,
RSS/disk monitoring and persistent disk cache. Resource command/exit/sample
records are retained; no OOM/resource stop or increased proof/gas/step/test limit.
Historical docs/G03 exit1 remain failures with exact-base zero-regression checks,
not global passes. Seven prior sealed checksum manifests and all original
artifacts/caches/failures are preserved.

Work1/Work3 remain partial: actual physical/source/kernel progress is now ready,
but all24 full Y01–Y09/Y10/G48–G51 obligations and six entire source combinations
remain open. Work2/BackfillA/B remain partial for universal correspondence,
complete semantic observation contracts and actual compiler/source/world wiring.
VY2 delivery is no longer a blocker. Remaining concrete producer facts are VY1
Yul/dirty-local execution, physical-world journal/log integration, G01 amendments,
and real compiler/world/V16 assembly Lang/pass/Cert/guards. Generic certificate
laws and finite external tests do not supply them. The pre-existing full goal
remains blocked and untouched; get_goal is not exposed, and no new/reset/
reactivated goal or competing continuation was created in this manual recovery.
No semantic question is pending. Fresh patch/bundles/handoff/evidence/checksums
are versioned under `/workspace/vy5-composition/physical-source-20261101/final/`.


## Actual raw-local / physical / scoped-loop consumer — 2026-11-01

This continues the frozen Y10 assignment from reviewed
 d36a280a9e6a68eefc2283b62e4623b3bfbeabdc on the assigned branch, pinned base
0b078cefaf7daad79007b87b72df64eb6936420f. The missing-VY1-package condition is
resolved by sealed c7b128fd10df2fa51929cb68bdba020cf2ca07a5. Verified bundle
SHA256 a046a61d2cb221d6701a6c354bbfc72b344220128e972a7d32d610a8c7a96f48,
archive46fd3b2e1f5b35707657c2f68ca416def082593c71fb4b2b435e3e7165788cf6,
and interface409cb6fc38c5e535a1fcdd0f2a7d7eeab61d4568ff33b7c9ba17012ee5776e84
match delivery. All80 archive modules match the committed tree/module hashes;
125-file import closure adds80 files with no version conflict. The delivered
interface's optional source/Interface path is not relied on; actual module
bodies/signatures from the verified Git bundle are the inputs.

The existing private dependency tree extends physical checkpoint
 a3b983b7abafbf299a0b2ac4452a55c849d6e37b via VY1 stage
020814b93b87a683ce7931618779b4bfba6691cf to validated
c6c529aaa6075488ff84b8606af508432dd50053 at
`/workspace/vy5-dependencies-20261101`. No foreign producer definition changed.
The assigned branch retains source-only consumer modules; supplied dependencies
and the complete root registration remain private development inputs, not a
master integration or standalone general-assembly admission claim.
[Exact producer receipt](../../tests/yul-composition/local-producer-input.json)
records125 source hashes,80 added modules and retained producer limitations.

Four new modules add43 named kernel component laws, independently witnessed:

| Module | Actual result and boundary |
|---|---|
| [LocalPhysical](../../Solidity/Yul/Composition/LocalPhysical.lean) | Executes the actual represented physical Source action first, retaining the entire physical result and both journals; only actual Except success enters actual VY1 runLocalBlock. Full raw-word/control projection holds at every horizon; source errors, horizon exhaustion and completion remain distinct. Static failure preserves original source/journals and executes no local code at every fuel. |
| [LocalPhysicalControls](../../Solidity/Yul/Composition/LocalPhysicalControls.lean) | Same actual originEnv/Source.Ctx carries six source locals but seven word cells: dirty bool2, uint8=257, two distinct same-type external-function locals with full raw address/selector fields, fixed byte and a heap-backed nonword memory reference. Actual physical raw0xab000002 and child0xcd000003, checked preparation/owner/separation/nonstatic/MemOK, full Source.St/nonword retention, raw clean?/runClean refusal, coupled three-journal rollback and all-completed-horizon equality are proved. |
| [LocalPhysicalMemory](../../Solidity/Yul/Composition/LocalPhysicalMemory.lean) | Reconstructs the complete physical raw word after actual local execution. Actual retained heap lookup/MemoryImage/Placement/reserved-area/window/target bounds yield exact target byte-copy agreement, without an allocator refinement or full raw-state MemOK assertion. |
| [LoopPhysical](../../Solidity/Yul/Composition/LoopPhysical.lean) | Actual intrinsic Yul FOR uses a scoped zero-initialized counter after the physical step and dirty prefix: three iterations produce raw uint8=1025; CONTINUE runs post/test and also1025; BREAK is consumed after one increment,513; wrongcount2 gives769. Source/nonword/rawslot persist and every completed horizon has the same complete outcome. This is not old Source.RStmt loop dispatch, lowering, or full Solidity-loop coverage. |

The physical-first boundary has no assumed producer theorem. Its static error
is retained as Except.error; successful local exhaustion is Except.ok none.
Both physical journals are returned alongside that result. Initial and physical
clean phases have actual Source.MemOK witnesses with a real allocated AABB byte
object backing memRef0. Raw LocalValues are distinct from old clean Source.Locals:
word-view identity does not imply literal LocalValues identity. All pure cells
are retagged raw by writeback, even unchanged/canonical words. The theorem
no_raw_resume proves every Unit-returning old Source.EM action is refused by runClean on the
completed raw witness. No cleanup policy or ordinary-source resumption is inferred.

The rollback law uses the actual VY2 source/complement/owned-byte journals and
restores the full clean Source state. The raw-local transport law rebases St
between actual local runs with identical initial locals; it does NOT execute a
physical action after raw local writeback or claim dirty-local frame rollback.
The precise missing direction is an actual raw Source hook/operator/frame/session
semantics preserving LocalValues; old runClean demonstrably cannot supply it.
Source.St.logs55 is an internal preservation sentinel, not silently mapped into
native logs or VY4 topic observations. Physical-world journal/log integration,
G01 allocation/unified-observation amendments, actual compiler/world/V16 assembly
certificates and all full Y10 combinations remain open.

[LocalDriver](../../tests/yul-composition/LocalDriver.lean) executes actual producer
and consumer definitions and retains seven ordered horizons, complete word cells,
all legal transfers, static halts, raw-resume refusal, real heap/nonword/log
sentinels, raw physical words and target BB memory sentinels. No missing capture
is replaced with zero. The independently source-derived
[expectations](../../tests/yul-composition/local-expectations.json) were saved
before native observations. The [finite fixture](../../tests/yul-composition/LocalPhysicalControls.sol)
compares the same raw fields/storage/AABB output in pinned solc0.8.38+1835d247/
Osaka, legacy/viaIR and optimizer off/on. All4profiles/20orderedcalls pass:
peek; joint physical/raw block; peek; child-success/outer-revert; peek. Expected
values never changed. Raw bool2/u8=257/full-word Fn fields agree in this control
across profiles; no general ordinary-Solidity cleanup/pipeline theorem follows.
Return windows are relative, without native/source allocation-pointer equality.
Source logical account1/log sentinel and native predicted account domain are
separate finite controls, not an asserted address/world correspondence relation.

The first new fixture wrapper failed compiler8894 because inheriting a contract
with custom storage layout is forbidden. Its complete raw input/diagnostic is
retained. The corrected new wrapper inherits the same uncustomized B/C bases
and repeats D's unchanged fields/methods with explicit layout42. The older
PhysicalControls.sol and every original expected outcome remain unchanged.
[Runner](../../scripts/yul-composition/local-source.mjs) validates full ordered
capture/result/request/frame identities, deployment address/runtime installation,
pre/post slot42–48 maps, account balance/nonce/code, selected RETURN/REVERT windows,
child ownership/input and rollback writes. runCall host nonce behavior remains
separate from runTx/deferred cleanup. Complete untouched-world/source adequacy
is not claimed. Current receipt/source/oracle/ledger bytes and all actual private
producer/consumer bodies, retained Lean stdout/stderr/command/exit metadata and
raw compiler receipts are revalidated on report read, not merely declared hashes.

[Local ledger](../../tests/yul-composition/local-component-ledger.json) registers31
facts; [loop ledger](../../tests/yul-composition/loop-component-ledger.json) adds12.
[Extra catalog validator](../../scripts/yul-composition/component-extras.mjs)
rejects missing selected catalogs, stale proof bodies and false closure. All24
full obligations/six source combinations remain pending. The previous physical
and component catalogs are preserved as their tested historical scopes; these
new extensions supersede their earlier missing-VY1-package condition.

Final affected scripts pass328JS+2Python, including actual filesystem-read
missing/stale receipt/source/oracle/body simulations, equal-return wrong storage/
world/memory, lost dirty bits, function aliasing, wrong nonword/source, control/
horizon/static/resume/rollback mutations and stale/missing/false-proof catalogs.
Final private joint gate passes actual Lean4.24.0 commit797c613 and
Lake5.0.0-src+797c613, explicit KeySort2jobs, library1221jobs, TestSuite262jobs,
SolKey377taclets/131read annotations,188core/0elaborator and1236reachable/
0orphans. Strict remains491automatic/61budgeted/0manual/11refuted/0pending.
All43 exact signatures/scoped axiom reports pass with only standard axioms or
none. Final per-file MCP checks pass four new modules, driver and private root:
success=true, partial=false, no errors; nonfatal shutdown warnings remain raw.

The first joint command passed build/signature/strict phases then failed trust
with six newly imported .admit method-name registrations missing. That exit1
and every earlier failed edit/fixture probe remain raw. Actual Builtin.admit is
an ordinary Except Refusal Unit tier/resource/callcode checker; all six sites
are its definition/method uses/unfolds/lemma statements, not Lean proof admission.
The [isolated registration](../../tests/yul-composition/local-trust-registration.json)
and exact patch are independently reviewed: only private tests/trust-inventory
appends six exact sites,246→252. Main shared inventory and checker/forbidden-token
rules are unchanged. Final same-checker trust1251sources/252sites/0findings passes.
No axiom/sorry/native proof bypass or expected semantic verdict change occurs.
An orphan audit accidentally run in the source-only assigned checkout correctly
failed with13unintegrated consumer modules; that exit1 is retained separately.
The correct private import-root audit passes, without claiming standalone main
source support. Historical docs/G03 exit1 remain baseline-identical failures.

Independent read-only finder and skeptic reviews used no Lean/server/build.
They found physical-halt loss in the first adapter and a current-file provenance
reader gap. Both were fixed and discriminating tests added. Separate rereviews
accepted all43 kernel laws, fixture/driver/runner, narrow private trust amendment
and coverage boundaries with no remaining concrete source finding. Detailed
review records and exact commands/outputs/resources are exported with the handoff.

Heavy work remains serial under the writer lock, Lean-j1/LEAN_NUM_THREADS=1,
hard aggregate12GiB/equal memory-swap (no swap), OS/RSS/disk monitoring and disk
caches. Docker uses vfs and each check copied its immutable base; this caused
rapid disk loss. Only new stopped dirty-source containers were retired after
SizeRw=0 and exported directory-only bind-placeholder differences were verified;
exact inspect/directory metadata and logs, immutable image and ALL mounted caches
remain preserved. A strict empty-diff guard first refused those mount directories
and removed nothing; that failed probe is also retained. No prior container,
source, sealed manifest/cache or evidence was discarded. No resource/proof/fuel/
node/gas/test budget increased and no OOM/hidden resource stop occurred.

Work1/Work3 remain partial despite43 new actual joint/loop laws and checked import
closure. Work2/BackfillA/B remain partial despite20new native calls, fail-closed
source/proof/provenance controls and ready-input consumption. Original227working
upstream profiles/458finite asserted calls,21older-fork blocks,416compiler probes
and eight intended mutants remain unchanged and attributed to sealed tested
reports; unchanged full reference commands were not rerun as new evidence.
Concrete Source.RStmt/JSON/dirty-ordinary operators/raw function frames/sessions,
physical-world journals/logs, G01 contracts and actual compiler/world/V16 assembly
facts still block all24/six final source obligations. No generic assumption or
finite control substitutes for those proofs. The full goal stays blocked and
untouched; get_goal is not exposed, no status change/reset/recreation or competing
continuation occurred. DecisionsYQ1–YQ7 remain those recorded in solidity-scope.md.
No new semantic question is pending. Fresh committed patch/private bundle/interface/
handoff/evidence/checksums are versioned under
`/workspace/vy5-composition/dirty-source-20261101/final/`; all eight earlier sealed
manifests, raw failures and caches are preserved.


## Scoped function/loop composition — 2026-11-01

This reviewed component continues the entire frozen assignment from
5bf18485d33c88495a140134d1f49f0dfcb7aec0 on the assigned branch, base
0b078cefaf7daad79007b87b72df64eb6936420f. It uses ONLY already-staged producer
inputs. No new VY1 retrieval, active-source snapshot, producer turn, goal/status
change or compiler-expectation answer was attempted. The existing two VY1
compiler-expectation questions remain unanswered. Earlier YQ1–YQ7 decisions and
the parallel-work amendment remain authoritative.

[FunctionPhysical](../../Solidity/Yul/Composition/FunctionPhysical.lean) adds26
named kernel laws using actual intrinsic Stmt.functions, Bodies, Expr.call,
Policy, WordAdapter.functions and runLocalBlock. It does not introduce another
interpreter or assume a compiler/source simulation. The two signatures are
both1argument/1return; their bodies have only two own local slots (argument0,
return1) and EMPTY external context. Caller source locals cannot be captured.
The loop passes the actual raw uint8 word explicitly and assigns the return.

The first function returns normally with x+256. The second calls that actual
first function on x+256, executes leave, then has a poison return assignment0.
Leave must prevent the poison. After the existing dirty prefix sets small257,
three nested calls produce1793. The wrong same-arity callee produces1025;
omitting leave produces0. These are actual closed runner results at the
UNCHANGED horizon32, not an external result oracle. Intrinsic Member proofs
exclude wrong argument/result signatures2/1 and1/2; the caller flow is normal.
All-completed-horizon equality preserves the full raw result, source and control.
Horizon0/4 exhaustion and static no-call at every fuel remain distinct from
completion. Full seven-cell raw snapshots retain bool2 and the two distinct
same-type external-function fields, including their dirty high bits.

The joint adapter is the existing actual physical-first boundary. Its ENTIRE
physical result, source step and BOTH real complement/owned-byte journals are
retained at every fuel. Full Source.St and the backed nonword memory alias are
preserved; complete raw slot0xab000002 reconstruction and the actual AABB heap
window/BB target copy are proved with the existing placement/reserved/bounds
premises. Actual child-source/outer rollback restores all three journals. The
transport law rebases Source.St between actual function runs from identical
initial clean locals; it does NOT execute old Source after raw writeback or prove
raw-local frame rollback. The clean bridge refuses every Unit-returning old
Source.EM action on the raw result. No cleanup/resumption theorem is invented.

Initial direct rfl/projection reductions exceeded the existing200000heartbeat
limit. The failure logs remain raw. Variable-fuel source/nonword/raw lemmas and
a structural control lemma avoid re-evaluating the closed function loop during
elaboration; the statements and actual program are preserved. No heartbeat,
fuel, node, gas, test or resource limit was raised. An initial diagnostic helper
named mcp.py shadowed its Python package and exited1 before Lean started; its
source/cache/error are preserved and the renamed helper passes. The commit
whitespace check also caught indentation on a blank no-leave fixture line; only
that whitespace was trimmed. Its failure/original source are preserved and
final byte-bound compiler receipts/script checks were refreshed successfully.

[FunctionDriver](../../tests/yul-composition/FunctionDriver.lean) executes the
actual interpreter and producer states. It records ordered horizons, raw results,
function arities, wrong-callee/missing-leave outputs, static halts, raw-resume
refusal, nonword/heap/source-log sentinels and both physical journal lengths.
[Independent expectations](../../tests/yul-composition/function-expectations.json)
were frozen before native execution. The
[finite Solidity fixture](../../tests/yul-composition/FunctionPhysicalControls.sol)
uses the same uncustomized B/C bases and explicit storage layout42 as the earlier
control, without modifying any earlier fixture. Its compose/composeWrong/
composeNoLeave methods match1793/1025/0. All4 pinned solc0.8.38+1835d247/Osaka
legacy/viaIR optimizer off/on profiles pass28orderedcalls: peek; all three
function variants; peek; successful-child/outer-revert; peek.

[Runner](../../scripts/yul-composition/function-source.mjs) reuses existing
compiler/capture primitives and the older provenance validators. It validates
actual current producer/consumer bodies, frozen source/oracle/ledger bytes,
retained Lean stdout/stderr/command/exit metadata, exact profiles/call identity,
deployment/runtime, finite pre/post accounts/slot42–48 maps, ordered results/logs,
relative RETURN/REVERT windows and the external self-child rollback trace.
Internal Yul function calls are not EVM message frames. Source logical account1
and log55 are separate preservation witnesses, not silently identified with
native addresses/logs. Allocation pointers are not compared across pipelines.
This is finite compiler/EVM evidence, not a Source/compiler/world theorem.

The [26-fact catalog](../../tests/yul-composition/function-component-ledger.json)
is required by the active ledger selector. Missing/stale catalog/body/source/
receipt/profile/call/return evidence, wrong arity/leave/timeout/static state,
dirty-bit loss, function aliasing, journal drift, equal-return wrong storage/
world/memory, and false proof closure fail closed. All410JS+2Python tests pass.
Original328tests, all earlier source fixtures/expectations,227working upstream
profiles/21fork blocks and eight intended mutant mismatches remain intact and
attributed to their sealed tested reports. No unchanged full reference command
was rerun as fresh correspondence evidence.

The existing private tree c6c529aaa6075488ff84b8606af508432dd50053 is preserved as
ancestor of cb325c26a3c9be45f41506d23fe60555369ace92 at
`/workspace/vy5-dependencies-20261101`. Its root adds only the new consumer import;
producer definitions and the earlier exact trust registration are unchanged.
Final registered joint gate exits0: actual Lean4.24.0 commit797c613,
Lake5.0.0-src+797c613; KeySort2jobs; library1222jobs; TestSuite262jobs;
377taclets/131read annotations;189core/0elaborator;1237reachable/0orphans;
strict491automatic/61budgeted/0manual/11refuted/0pending;
trust1252sources/252sites/0findings. All26 scoped signatures/axiom reports show
only standard axioms or none. Final MCP diagnostics pass the consumer, driver
and private root with success=true/partial=false/no errors; nonfatal shutdown
warnings remain raw. Standalone main-source import support is not claimed.
Historical docs/G03 exit1 and earlier joint exit126/trust-wrapper exit1 remain
failures; exact-base zero-regression comparisons are reported separately.

Separate independent read-only finder/skeptic reviews used no Lean/server/build.
Both accepted the actual scoped function semantics, arity/leave controls,
physical/source/raw boundaries, driver, finite fixture, provenance reader and
mutation controls with no remaining concrete finding. Exact signatures and raw
evidence are under `/workspace/vy5-composition/function-source-20261101/`.
Heavy checks use the unchanged writer lock and bounded runner, serial Lean-j1/
LEAN_NUM_THREADS=1, enforced12GiB/no swap and unchanged1GiB OS-headroom guard.
Disk/RAM were monitored; only new stopped VFS metadata-only copies were retired
after preserving/validating inspect metadata and logs, immutable image and ALL
mounted caches. No earlier cache/evidence/container was deleted and no hidden
resource stop occurred. Existing guard files/floors were not reduced.

Work1/Work3 remain partial despite this concrete function+loop component and
validated imports. Work2/BackfillA/B remain partial despite28new ordered native
calls and strict finite coverage/provenance controls. All24full Y01–Y09/Y10/
G48–G51 obligations and six FULL Source combinations remain pending. Actual
Source.RStmt/JSON/raw ordinary operators/function/session hooks, physical-world
journal/log integration, G01 contracts and actual compiler/world/V16 assembly
certificates are still missing. Source-only local/scoped-function components
and finite EVM tests do not discharge them. No goal was reset/recreated/
reactivated/status-changed; get_goal remains unavailable and the original
blocked identity is preserved. No new semantic question is introduced.
Fresh reviewed patch/bundles/interface/handoff/evidence/checksums are versioned
under `/workspace/vy5-composition/function-source-20261101/final/`.

### Genuine recursive physical composition — 2026-11-01

[RecursivePhysical](../../Solidity/Yul/Composition/RecursivePhysical.lean) uses
only already-staged intrinsic Syntax/Bodies/Member/Policy/WordAdapter/LocalBlock.
Its actual2argument/1result scoped function calls itself with n−1 and x+256;
base n0 assigns x and leaves. Function bodies have empty external context; the
raw local argument is passed explicitly, never captured. Starting n3 and the
actual dirty prefix small257 returns1025. The inhabited32horizon completes;
all completed horizons have this SAME full result by actual runner stability.
Missing decrement exhausts the actual runner at32 (and every sampled horizon
0/1/2/4/8/16/32); this is NOT a universal divergence or native timeout theorem.
The indexed wrong1argument reference is uninhabited. No proof/fuel/test budget
was increased and no axiom/sorry was introduced.

The18 registered laws retain exact raw words/control, unchanged complete Source.St,
nonword memoryRef0, the complete real represented physical result, residual and
owned-byte journals, actual coupled child-success/outer-rollback3journals and
bounded BB heap-window target copying. Real source/owner/request/preparation/
separation/nonstatic/MemOK premises are inherited from the SAME concrete physical
execution. Rollback transport rebases the old Source.St between actual runs from
initial clean locals; it does not resume dirty locals or roll them back through
old Source. Raw clean-bridge refusal is checked separately. This is an owned
component law, not general Source dispatch/compiler/world/Y07 adequacy.

[RecursiveDriver](../../tests/yul-composition/RecursiveDriver.lean) retains actual
execution projections, no missing-to-zero fallback. The new independent
[fixture](../../tests/yul-composition/RecursivePhysicalControls.sol) and frozen
[expectations](../../tests/yul-composition/recursive-expectations.json) derive
1025 and the wrong-addend1028 before native execution. All4 pinned solc0.8.38
+1835d247/Osaka legacy/viaIR optimizer off/on profiles pass24orderedcalls:
peek; recurse; wrong-add; peek; successful child/outer revert; peek. Native missing
decrement is deliberately not executed as a fabricated fuel correspondence.
The existing28call function fixture/expectations remain unchanged. Source logical
account1/log55 are distinct from finite native accounts/logs; internal recursive
Yul calls are not EVM message frames. RETURN/REVERT windows are relative; no
cross-pipeline pointer equality, complete untouched-world or runTx claim is made.

The [reader](../../scripts/yul-composition/recursive-source.mjs) validates retained
actual Lean execution, exact source/oracle/catalog/request/profile hashes, full
ordered fields and actual parent FunctionPhysical provenance. Both independent
read-only reviewers found the missing parent-function provenance link; fixed by
verifyFunctionInputs, frozen parent catalog and an actual private-body drift
mutation. They accepted the fix and scopes with no remaining actionable finding,
without Lean/server/build/edits. Missing/false recursion timeout, raw words,
nonword/source/world/storage/rollback/memory, arity, call order, source hashes,
parent/selected catalogs and proof closure fail closed. All492JS+2Python tests pass.

Existing private cb325c26a3c9be45f41506d23fe60555369ace92 is preserved as ancestor of
27014d0974884290737dbbf758e155fdc7663cc3; only new consumer/driver and one private
root import were added. Main standalone import support is not claimed. Final
registered joint gate exits0: Lean4.24.0 commit797c613; Lake5.0.0-src+797c613;
KeySort2jobs; library1223/TestSuite262jobs;377taclets/131annotations;190core/
0elaborator;1238reachable/0orphan; strict491automatic/61budgeted/0manual/
11refuted/0pending; trust1253sources/252sites/0findings. Scoped18signatures/
axiom reports use standard axioms only. Final per-file MCP consumer/driver/root
success=true/partial=false; nonfatal async shutdown warnings remain raw. Initial
MCP exit1 (redundant impossible arity branch) and one fixture-generation ValueError
are retained; fixed without budget/premise changes. Historical docs/G03 exit1 and
other earlier failures remain failures, exact-base comparisons are zero regression
only. Existing bounded runner/lock,12GiB/no swap,-j1/LEAN_NUM_THREADS=1 and1GiB
OS-headroom guard are unchanged. No protected data/cache/evidence was deleted;
only new stopped metadata-only container copies were retired after preserving
and validating inspect/logs/directory metadata, with immutable image/mounts kept.

Work1/Work3 and Work2/BackfillA/B all remain PARTIAL. All24 full Y01–Y09/Y10/
G48–G51 obligations and six full Source combinations remain pending. Actual Source
raw ordinary operators/function/session/JSON hooks, physical-world journals/logs,
G01 amendments and concrete compiler/world/V16 certificates remain open. Two VY1
compiler-expectation questions remain unanswered. No new producer retrieval or
goal creation/reset/reactivation/status change occurred; get_goal is unavailable.
Evidence and reviewed patch/bundles/interface/handoff/checksums are versioned at
`/workspace/vy5-composition/recursive-source-20261101/final/`.

### Raw-local catch/rollback transport — 2026-11-01

[RawCatchPhysical](../../Solidity/Yul/Composition/RawCatchPhysical.lean) advances
the Y10 try/catch consumer component with actual staged LocalState/runLocalBlock,
local_rebase, represented physical source actions and coupled rollback. It does
not add a Source hook or interpreter. The26 registered laws establish an ACTUAL
completed recursive raw prefix on the initial Source.St (seven words including
bool2/small1025, distinct function fields and memoryRef0), exact caller companion
identity after child success/outer rollback, all-horizon catch continuation
transport, and completed-result uniqueness. The continuation consumes existing
RAW LocalValues, adds256 to small (1281), retains all other raw bits/nonword alias,
and preserves complete caller Source.St/heap/source log55. It refuses runClean.
All real residual/owned-byte journals and source rollback remain coupled to the
same existing VY2 execution, including full reconstructed childCD000003 and
restored0 physical words. Wrong owner/slot and wrong rollback controls remain
explicit. No cleaning or raw function/session resumption is inferred.

The precise producer boundary is `representedSourceStep`/`Source.applyOp`:
these take the existing Source.EMState containing old Source.Locals, whereas
`LocalState` contains LocalValues and `LocalState.runClean` refuses raw values.
Here physical source operations run on their ACTUAL old EMState carrier and raw
locals are an unchanged companion; afterRollback is explicitly that companion
paired with the real restored Source.St. `complete_state_restore` proves exact
companion state identity, not a missing raw call-frame execution semantics.
`actual_prefix` witnesses raw origin with the real runner; no execution-agreement
premise or assumed theorem substitutes for it. General Source try/catch dispatch
and shared physical/world journal adequacy remain missing.

Actual VY4 `complete_revert` separately retains the supplied caller log55 and
exact failure data; `completeAndCopy` executes the real bounded target-copy
instructions. Dead bytes copy DE/AD between untouched EE neighbors; empty failure
copies nothing and preserves EE bytes; requesting one missing byte returns none.
VY4 Effects carries execution/logs/returndata, not VY2 complement/owned journals.
Its log prefix is an explicit input, never a silent conversion from Source.St.logs.
The catch code is a supplied local continuation; the general Source dispatcher
that selects it and binds catch bytes is not proved.

The actual [driver](../../tests/yul-composition/RawCatchDriver.lean) and new
[finite Solidity fixture](../../tests/yul-composition/RawCatchPhysicalControls.sol)
retain exact independent [expectations](../../tests/yul-composition/raw-catch-expectations.json).
The native fixture really executes Solidity try/catch around self-calls: caller
raw words and marker7/log55 precede outerAB/childCD writes, transient22/33 and
logs66/77; successful child effects are then reverted by the outer frame. Catch
continues raw small1025 to1281, wrong addend to1282, and returns exact DEAD/empty
catch lengths/data along with raw words, c0 and the AABB alias. Original sources,
fixtures and expected values are unchanged. Four pinned solc0.8.38+1835d247/Osaka
legacy/viaIR optimizer off/on profiles pass32orderedcalls, including direct
nonempty/empty failures and follow-up reads. Both outer/child logs and transient
writes have raw frame/operation evidence; only caller log55/marker7 survive.

The [reader](../../scripts/yul-composition/raw-catch-source.mjs) validates actual
parent Recursive→Function→local/physical/peer bodies, frozen own source/oracle/
catalog, retained Lean stdout/stderr/command/exit, compiler/source/settings and
profile matrix, call order/identity, precise touched persistent/transient maps,
accounts/nonce/balance/code, frame owners/requests/outcomes, exact last-call
buffers, log order and relative RETURN/REVERT/LOG windows. This remains finite
runCall evidence, not runTx, total untouched-world, cross-pipeline pointer
identity or Source/compiler correspondence. Source logical account1/log55 and
native addresses/logs are distinct test domains. All586JS+2Python tests pass;
mutations retain equal root returns while corrupting state/owner/journal/frame/
window/catch bytes, caller prefixes, metadata or imported private bodies and
fail closed. No missing evidence becomes empty or pending in a selected case.

Separate independent read-only finder/skeptic reviews accepted code and mutation
controls without findings, no Lean/server/build/edits. The private tree preserves
27014d0974884290737dbbf758e155fdc7663cc3 as ancestor of
587371709d6f37c753d41c4bc7cf53c7371df15a, adding only this consumer, driver and one
root import; producer bodies are unchanged. Main standalone import support is
not claimed. Joint gate exits0: Lean4.24.0 commit797c613, Lake5.0.0-src+797c613;
KeySort2jobs; library1224/TestSuite262jobs;377taclets/131annotations;191core/
0elaborator;1239reachable/0orphan; strict491automatic/61budgeted/0manual/
11refuted/0pending; trust1254sources/252sites/0findings. All26 signatures and
transitive axiom reports use only standard axioms or subsets; no new axiom/sorry.
Final per-file MCP consumer/driver/root: success=true/partial=false/no errors,
with raw nonfatal async shutdown warnings retained. Initial MCP exit1 reserved
identifier/indexed log constructor errors and next exit1 closed reduction/
Decidable failures remain raw; factored through arbitrary raw values without
raising the200000heartbeat budget. A provisional new fuel prediction was
corrected from2 to4 by reading evalStmtNode/evalExpr depth BEFORE driver/native
execution; prior oracles, values and budgets were untouched. Both oracle versions
are retained. Historical docs/G03 exit1 remain failing with exact-base output
equality reported separately. Existing bounded runner/lock, serial Lean-j1/
LEAN_NUM_THREADS=1,12GiB/no swap and OS-headroom guard are unchanged. All old
cache/evidence/manifests remain protected; only this turn's stopped VFS
metadata-only copies were retired after preserving/verifying inspect/logs and
directory metadata; immutable image and mounted data remain intact.

Work1/Work3 and Work2/BackfillA/B remain PARTIAL. All24 full Y01–Y09/Y10/G48–G51
obligations and six full Source combinations remain pending. General Source raw
operators/JSON/function/session hooks, physical-world journal/log/G01 integration
and concrete compiler/world/V16 assembly adequacy remain open. Both VY1 compiler
questions remain unanswered. No new producer retrieval, goal creation/reset/
reactivation/status change, push/merge/PR or service occurred; get_goal is absent.
The original blocked goal is untouched. Reviewed patch/bundles/interface/handoff/
evidence/checksums are versioned at
`/workspace/vy5-composition/raw-catch-20261101/final/`.

### Scoped functions after raw catch — 2026-11-01

[CatchFunctionPhysical](../../Solidity/Yul/Composition/CatchFunctionPhysical.lean)
starts directly from `RawCatchPhysical.completed.state`: raw small1281, bool2,
full dirty function fields, memoryRef0 and the complete retained Source.St. The
real code is ONLY `.functions FunctionPhysical.F (FunctionPhysical.definitions
withLeave)` followed by the indexed call/assignment. It does not prepend dirtyCode,
ofClean or another interpreter; producer bodies are unchanged. Existing nestedBody
adds256 then calls existing incrementBody for another256; its actual leave skips
poison0. The inhabited32horizon therefore yields1793. Wrong callee yields1537;
missing leave yields0. Separate explicit WRONG input-reset control starts from
old clean initial locals and yields513 plus flag1/address4660/selector16909060.
It is never used on the real path or inferred as solc cleanup. Both arity-error
references remain uninhabited using the actual Member group.

The24 new component laws are distinct from ALL24 original full obligations,
which remain pending. `all_horizon_rebase` covers arbitrary typed LocalValues,
both Source.St values, both boolean controls and every horizon, including
exhaustion. `source_preserved`, `nonword_preserved`, `completed_from_unique` and
`raw_from` cover arbitrary typed inputs with actual completed-run premises, not
an execution-agreement oracle. The concrete witness proves complete output/flow,
source/heap/log55/nonword preservation and all-completed-horizon uniqueness.
runClean still refuses the raw output. Real coupled physical residual/owned-byte
journals, reconstructed restored0 and exact supplied VY4 failure/window relations
remain tied to the same actual restored Source.St; no extra physical step or
raw Source function/session semantics is invented. Native-to-Lean fuel equality,
Source try/catch selection/byte binding and physical-world/G01/compiler/V16
adequacy are not consequences of these laws.

The [actual driver](../../tests/yul-composition/CatchFunctionDriver.lean) records
input1281 separately from output1793, wrong1537/poison0/reset513, arities, all raw
cells/control, every selected horizon, clean refusal, nonword/heap/source/world
logs, real journals and failure/window data. Horizon0/1/2/4/8 exhausts and16/32
completes, as independently predicted from staged evaluator/body depth BEFORE
execution; original32fuel budget is unchanged. No missing field becomes zero.

The new [native fixture](../../tests/yul-composition/CatchFunctionPhysicalControls.sol)
retains the prior raw-prefix and actual try/catch operations in a new source and
continues with scoped Yul functions inside catch. Independently frozen
[expectations](../../tests/yul-composition/catch-function-expectations.json)
cover normal/wrong-callee/missing-leave/explicit-reset and empty-data variants,
follow-up reads and direct nonempty/empty outer failures:4 pinned solc0.8.38
+1835d247/Osaka legacy/viaIR optimizer off/on profiles pass40orderedcalls. All
original fixture/oracle files remain unchanged. Caller marker7/log55 survives;
outerAB/childCD and transient22/33/logs66/77 revert. Exact DE/AD or empty catch
bytes, AABB alias, full function fields and relative frame memory remain observed.
This is finite runCall/touched-world evidence, not total-world/runTx, pointer
identity, Source/compiler correspondence or an answer to LIB1/unchecked-add.

The [reader](../../scripts/yul-composition/catch-function-source.mjs) validates
actual parent RawCatch→Recursive→Function→local/physical/peer closure, frozen
parent and selected own catalogs, current source/body/oracle/settings hashes,
retained Lean command/exit/stdout/stderr, required profile/call order, touched
accounts/storage/transient maps, all relevant frame identities/write indices,
ordered logs/buffers and RETURN/REVERT/LOG windows. Raw input reset, callee/leave/
arity confusion, equal-return wrong owner/slot/journal/world/memory, missing or
stale source/private bodies/receipts/catalog/evidence fail closed. All690JS+2Python
pass, including previous586JS controls; prior native evidence remains attributed
to sealed tested trees. No unchanged full reference command was rerun as fresh
correspondence. Separate independent finder/skeptic read-only reviews accepted
source and mutations, no findings or Lean/server/build/edits.

Private587371709d6f37c753d41c4bc7cf53c7371df15a is preserved as ancestor of
9cc86ee418a700936b30595a38734705a32a6bac; only this owned consumer, driver and one
private root import were added. Main standalone import support is not claimed.
Joint gate exits0: actual Lean4.24.0 commit797c613; Lake5.0.0-src+797c613;
KeySort2jobs; library1225/TestSuite262jobs;377taclets/131annotations;192core/
0elaborator;1240reachable/0orphan; strict491automatic/61budgeted/0manual/
11refuted/0pending; trust1255sources/252sites/0findings. All24 scoped signatures/
transitive axiom reports show standard axioms or subsets, no axiom/sorry. Final
MCP consumer/driver/root success=true/partial=false/no errors; raw nonfatal async
shutdown warnings remain. Initial MCP exit1 from ambiguous `initial.2` is retained;
qualified actual LocalPhysicalControls.initial without changing outcome/budget.
Historical docs/G03 exit1 and exact-base comparison remain failure/zero regression,
not passing global gates. Supported writer lock/bounded runner, serial-j1/
LEAN_NUM_THREADS=1,12GiB/no swap/OS-headroom guards and all proof/test limits are
unchanged. Disk was measured throughout; no protected cache/evidence was deleted
or guard reduced. Only this turn's stopped metadata-only VFS copies were retired
after preserving/verifying inspect/logs/directory metadata and retaining image/
mounted data. No hidden resource stop occurred.

Work1/Work3 and Work2/BackfillA/B remain PARTIAL. All24 original Y01–Y09/Y10/
G48–G51 full obligations and six full Source combinations remain pending. Exact
remaining boundaries: Source.applyOp/representedSourceStep still accept old
Source.EMState/Source.Locals, while raw LocalState.runClean refuses raw values;
general Source dispatch/try selection/catch-byte binding/raw ordinary operators/
function/session hooks, physical-world journal/log/G01 and actual compiler/world/
V16 adequacy remain absent. The two VY1 LIB1/unchecked-add questions remain
unanswered. No producer retrieval, goal creation/reset/reactivation/status change,
push/merge/PR or service occurred; get_goal is unavailable. Original blocked goal
identity stays unchanged. Reviewed immutable patch/bundles/interface/handoff/raw
evidence/checksums are at `/workspace/vy5-composition/catch-function-20261101/final/`.

### Actual Source halt capture with raw companion — 2026-11-01

[AttemptPhysical](../../Solidity/Yul/Composition/AttemptPhysical.lean) consumes
the ACTUAL `Source.EM.attempt` from Source/Machine, with28component laws distinct
from all24 original pending obligations. For arbitrary computations, dependent
callee-local indices and typed inputs, `attempt_run` proves outer.ok containing
the exact old inner Except result and ENTIRE poststate by the concrete definition,
not an execution oracle. `companion_actual`/`full_poststate` retain the actual
callee result/locals/Source.St alongside the unchanged indexed raw caller. Explicit
old callee locals are supplied separately; no ofClean/runClean/raw-caller reset
or second untyped state is introduced. No VY4 caller-frame producer is duplicated.

The concrete input is actual CatchFunctionPhysical.completed.state (small1793,
bool2/full dirty function fields/memoryRef0). An ACTUAL EM.modSt prepends source
log99 before EM.lift succeeds or halts. All six witnessed outcomes retain99/55
and the original caller raw words: successBEEF, revertDEAD, empty revert, panic,
timeout, stuck. `classify`/`route` are explicit CONSUMER routing: success skips
the continuation, revert preserves all bytes, timeout/stuck propagate unchanged
with the exact stuck reason. Source.Halt has no panic constructor: Source.panic
is revert(panicData), preserved byte-for-byte, including the36byte assert payload.
Continuation fuel0 retains caught bytes and none execution, distinct from Source
Halt.timeout. Attempt does NOT roll back; `no_implicit_rollback` proves retained
source log99. Real physical rollback and its three-journal invariants remain the
separate existing operation; no rollback conclusion is inferred from attempt.

Full captured revert bytes are returned as data; ONLY data.length is bound by an
existing typed Yul word literal into the current raw small cell, then actual
existing scoped-function code executes. It yields2307/2305/2341 for lengths2/0/36
(start1793 plus length plus512), without initialization or clean conversion.
Arbitrary-data/all-horizon rebase, completed-result uniqueness, nonword retention,
raw writeback/refusal and exact actual outcome/poststate transport are proved.
This is not allocation/binding of a Solidity catch memory variable or Source.tryStmt
semantics. Source/Eval.enterInstance separately uses attempt, restores heap,
rolls back on revert and propagates other halts; runMods separately saves/restores
fnLocals. Their general raw dispatcher/function/session/caller-frame hooks remain
producer obligations, not reimplemented here. Source EM still operates on old
Source.Locals; our raw LocalValues remain a separate explicit companion.

The [actual driver](../../tests/yul-composition/AttemptDriver.lean) retains each
captured outcome, branch, raw/poststate log prefix, full panic/revert bytes and
continuation exhaustion. New independent [native source](../../tests/yul-composition/AttemptControls.sol)
and frozen [expectations](../../tests/yul-composition/attempt-expectations.json)
exercise successBEEF (no continuation), DEAD/empty/panic catches with length-bound
raw continuation, and reads: four pinned solc0.8.38+1835d247/Osaka legacy/viaIR
optimizer off/on profiles pass24orderedcalls. Actual native external frames roll
back outerAB/childCD/transient22/33/log66/77 while caller marker7/log55 persists.
That native rollback is NOT the Source attempt primitive's log99 retention.
Native timeout/gas/stuck correspondence is not asserted. Both nonempty/empty
catch and full panic-tail buffers, ordered frames/writes/logs, touched accounts/
persistent/transient maps and relative RETURN/REVERT/LOG windows are checked.
Finite runCall evidence is separate from kernel laws, runTx/untouched total-world,
allocation identity and full Source/compiler/world correspondence.

[Reader](../../scripts/yul-composition/attempt-source.mjs) binds actual main/private
Source.Machine/Value/Observe bytes plus the existing CatchFunction→RawCatch→peer
closure, frozen source/oracle/catalog/settings/current bodies, retained Lean
command/exit/stdout/stderr, exact profile/call identity and all ordered fields.
Success good() is external pure, so its nested frame must be static; root remains
nonstatic. Initial native exit1 incorrectly required a nonstatic child; fixed to
STRICT true from source mutability, not allow-both. Source/oracle values remained
unchanged and raw failedv1 is retained. False static flag/panic tail/stale catch
bytes, wrong branch, swallowed timeout/stuck, raw reset/cleanup, false rollback,
wrong length/source/poststate, equal-return wrong frame/world/state and producer/
receipt/catalog drift fail closed. All781JS+2Python pass. Previous sealed40call
reference was not rerun as fresh compiler evidence. Original fixture/oracle hashes
remain untouched.

Separate independent read-only finder/skeptic reviews accepted source and strict
static correction; both found a no-op prestate test mutant assigning marker7 when
success already stored7. Fixed the mutant to0, not the oracle, before full tests;
no failed test run was fabricated. Rereview accepted with no remaining finding,
no Lean/server/build/edits. Private9cc86ee418a700936b30595a38734705a32a6bac is an
ancestor of b65e9d776eb1e168cacbdc8be649d9fab4511c23; only owned consumer/driver
and one private root import were added. Main standalone import support is not
claimed. Joint gate exits0: actual Lean4.24.0 commit797c613, Lake5.0.0-src+797c613;
KeySort2jobs; library1226/TestSuite262jobs;377taclets/131annotations;193core/
0elaborator;1241reachable/0orphan; strict491automatic/61budgeted/0manual/
11refuted/0pending; trust1256sources/252sites/0findings. All28 scoped signatures/
transitive axioms show standard axioms or subsets; no new axiom/sorry. Final MCP
consumer/driver/root success=true/partial=false/no errors; nonfatal async shutdown
warnings remain raw. Failed diagnostics from generic result case reduction and
state-alias rewrite, native static guard and a Python setup syntax error remain
recorded; all corrected without budget/semantic-value changes. Historical docs/
G03 exit1 remain failures with exact-base equality, never global passes.

Existing writer lock and bounded runner remain unchanged: serial-j1/
LEAN_NUM_THREADS=1, hard12GiB/no swap, OS-headroom and all proof/fuel/node/test
limits. Disk is measured, not declared a new passing gate; no guard/floor is
lowered and no protected cache/evidence deleted. Only new stopped metadata-only
VFS copies are retired after retaining/verifying inspect/logs/directory metadata
and preserving image/mounts. Incremental source archive avoids re-exporting old
source packages. No hidden resource stop occurred.

Work1/Work3 and Work2/BackfillA/B remain PARTIAL. All24 original Y01–Y09/Y10/
G48–G51 obligations and six full Source combinations remain pending. Missing:
general raw Source try selection/byte allocation/binding, ordinary operators,
function/session hooks, physical-world journal/log/G01 and actual compiler/world/
V16 adequacy. LIB1/unchecked-add remain unanswered. Original blocked goal stays
untouched; get_goal unavailable. No new goal/reset/reactivation/status change,
producer retrieval/export turn, push/merge/PR or service. Reviewed exact
patch/bundles/interface/handoff/evidence/checksums are versioned at
`/workspace/vy5-composition/attempt-20261101/final/`.

### Typed heap allocation of captured bytes — 2026-11-01

[HeapCatchPhysical](../../Solidity/Yul/Composition/HeapCatchPhysical.lean) consumes
actual Source.allocRef/alloc, bytesOfRV/heapBytes and Heap.alloc. No replacement
allocator/state/dispatcher is introduced.38component laws are distinct from the24
ORIGINAL full obligations, all still pending. Universal allocateRead_run proves,
for arbitrary typed Source environment/callee locals/state and bytes, the exact
memory-typed Val.memRef at old heap.next, FULL returned bytes, unchanged callee
locals and full Source.St with ONLY the actual allocated heap substituted. It
uses existing Source.Hoare.run_bind and Heap.alloc_get; allocRef_run is the actual
operation, not an assumed agreement. The actual first EM.attempt captured result
selects allocation via afterCaptured; success skips allocation, timeout/stuck
propagate, panic retains the entire assert revert payload. No caller raw values
are converted to old Locals or reinitialized. Explicit old callee locals remain
separate from the raw companion, as in the previous consumer.

The actual input is AttemptPhysical.input (existing CatchFunction raw1793 and
complete caller Source.St). Captured poststate retains Source99/55; allocation
then creates logical heap object1, advances next1→2 and retains object0 AABB.
Typed full contents, exact length, freshness, old-object/frame/source/raw retention
and actual capture/allocation state agreement are proved. EMPTY bytes still
allocate a typed empty object. The actual readback pair drives the existing raw
continuation, yielding2307/2305/2341 for2/0/36bytes, retaining nonword alias0 and
raw bits, refusing runClean, with completed-horizon uniqueness. This allocates and
reads a typed Source value; it does NOT yet bind a named catch declaration into a
Source local scope or implement Source.tryStmt selection/general raw sessions.

Refusal controls use actual APIs: allocRef of bool data allocates first, then
halts stuck("memory reference type"); the new bool cell is RETAINED. heapBytes
of it refuses "not a bytes object"; reading index2 after valid allocation refuses
"dangling memory reference". Neither refusal is converted to empty bytes or
assumed atomic/rolled back. Source heap/frame modification is distinct from
physical/world journal rollback. The physical_window consumer retains genuine
Placement of the NEW heap, data-length bound, ReservedOK, strict selected window
and target-address fit premises. No placement witness/refinement is fabricated;
logical index1 is NOT an EVM pointer. General G01 allocation refinement and full
joint source/physical/compiler adequacy remain pending.

[Driver](../../tests/yul-composition/HeapCatchDriver.lean) executes actual capture,
allocation/reference/readback and continuation, recording all six outcomes,
logical-reference type/index, full object contents/length/next, old alias/raw/logs
and refusals. Independently frozen [expectations](../../tests/yul-composition/heap-catch-expectations.json)
predate this execution. [Reader](../../scripts/yul-composition/heap-catch-source.mjs)
binds actual private/main Source.State/Machine/Eval/Hoare and parent Attempt→peer
bodies, current own sources/oracle/catalog, selected ledger and actual Lean
stdout/stderr/command/exit. It SHA-binds and fully revalidates the immutable old
attempt/native-v2 report (all24calls/four legacy/viaIR optimizer profiles), then
checks16full successful/revert/empty/panic byte comparisons against NEW Source
execution. Native evidence is explicitly historical-replay-only, not a fresh
compiler/EVM run. Logical references are recorded solely on the Source side;
no native pointer equality or whole Source correspondence is inferred. Full
panic tail and empty allocation remain distinguished.

148focused JS tests pass (new module plus affected parent Attempt tests), including
wrong reference/type/content/length/alias/next/raw/state/branch/refusal mutations,
equal-return corruption, fake pointer/native-execution/adequacy, stale actual
producer/private bodies/reference/receipts and missing selected catalog/evidence.
No unrelated broad reference/781JS+2Python suite was rerun or relabelled: those
prior results remain attributed to their sealed tree. Focused checks avoid its
roughly80MB output regeneration under327426048byte initial disk headroom.
Mandatory joint Lean gates still ran. Independent read-only finder/skeptic
reviews accepted source/reader/mutations with no findings and no Lean/server/
build/edits. Generic allocation proofs and physical conditional premises were
reviewed distinctly from finite old native evidence.

Privateb65e9d776eb1e168cacbdc8be649d9fab4511c23 is preserved as ancestor of
652278430074592f092f65ff78195fb6f3b27387; only owned consumer/driver and one private
root import were added. Main standalone import support is not claimed. Actual
joint gate exits0: Lean4.24.0 commit797c613/Lake5.0.0-src+797c613; KeySort2jobs;
library1227/TestSuite262jobs;377taclets/131annotations;194core/0elaborator;
1242reachable/0orphan; strict491automatic/61budgeted/0manual/11refuted/0pending;
trust1257sources/252sites/0findings. All38 scoped signatures/transitive axioms
use standard axioms or subsets, no new axiom/sorry. Final MCP consumer/driver/root
success=true/partial=false/no errors; nonfatal async shutdown warnings retained.
Earlier failed diagnostics (dependent type/Except layer/monad reduction/state
unfolding) are raw, corrected with existing laws rather than altered budgets or
outcomes. Docs/G03 historical exit1 remain failures with exact-base equality,
never global passes.

Existing lock/serial Lean-j1/LEAN_NUM_THREADS=1/hard12GiB/no swap/OS-headroom
and proof/fuel/node/test guards remain unchanged. Actual disk/RAM and expected
output were measured; one container at a time, incremental source/evidence and
focused cached reads fit. Only NEW stopped VFS metadata-only copies were retired
after preserving/verifying inspect/logs/directory metadata, immutable image and
all mounts. All older caches/artifacts/checkouts/manifests remain intact. No
hidden resource stop or new/reduced guard occurred.

Work1/Work3 and Work2/BackfillA/B remain PARTIAL. All24 original Y01–Y09/Y10/
G48–G51 obligations and six full Source combinations remain pending. Missing:
general catch selection/local-scope binding/raw Source operators/function/session/
frame hooks; concrete physical placement/allocation refinement; physical-world
journal/log/G01 and actual compiler/world/V16 adequacy. LIB1/unchecked-add remain
unanswered. Original blocked goal untouched; get_goal unavailable. No producer
retrieval, owner edits, goal reset/reactivation/completion, push/merge/PR/service.
Reviewed incremental patch/bundles/interface/handoff/evidence/checksums are at
`/workspace/vy5-composition/heap-catch-20261101/final/`.


## Typed catch-local scope consumer (2026-11-01)

This checkpoint consumes ACTUAL `EM.attempt`/`allocRef` results from
HeapCatchPhysical, binds the returned memory reference into actual indexed
`Source.Locals.cons`, then executes `EM.sub`, `readLoc (.local .here)` and
`bytesOfRV`. [ScopeCatchPhysical](../../Solidity/Yul/Composition/ScopeCatchPhysical.lean)
contains28 component laws, not a full Source try theorem. Generic `sub_run`
proves the concrete operation for arbitrary typed computations/inputs: outer
locals are restored on success and ANY halt, returned inner locals are retained
on success, and post-Source.St is retained. Generic `bound_read_run` and
`scoped_read_run` require the real heap.get bytes-object premise and prove exact
full bytes, bound memory-reference type/index, arbitrary outer-local tail and
restoration with unchanged state (`[ref1, oldAlias0]` is the concrete instance). No arbitrary supplied execution oracle appears.

Actual `run` takes the captured result/allocated state, reads the actual new
reference through its local (ignoring previously returned bytes), and preserves
the existing indexed RAW caller companion. Nonempty/empty/panic bind ref1 ahead
of oldalias0; success skips catch allocation/scope, timeout/stuck propagate.
All raw dirty words1793 and nonword alias0 remain; subsequent raw continuation
uses the actual local-read bytes and produces2307/2305/2341 without clean
resumption. `mutatedHalt` really changes inner locals to `[0,2]` and prepends
log77: actual sub restores caller alias0 on nonempty/empty/panic revert,
timeout/stuck while preserving postlogs77/99/55 and raw words. This is NOT
rollback. Same-type wrong index reads AABB rather than DEAD despite equal
length2; dynamic wrong-type lookup refuses with `local type`, and empty-context
indices are uninhabited. Parent allocRef invalid-type AFTER-allocation behavior
and refusal controls remain unchanged.

`resolved_rethrow` additionally executes the EXISTING canonical resolved
`RStmt.rethrow` at positive fuel32 over a bound typed local, with an explicit
found heap-object premise, returning the exact revert bytes/state. This is the
pre-existing exception, NOT a general Source try selector/catch-name resolver.
Parsed Syntax.tryStmt/catch alone supplies no resolved/evaluated selector;
resolved/evaluated general catch selection/error decoding remains missing.
Raw companion and typed Source scope have distinct contexts; no raw-to-clean
conversion or ordinary Source raw operator/function/session/frame adequacy is
inferred. Physical rollback remains the earlier actual coupled journals, not
EM.sub/attempt; no new placement/refinement/world theorem is claimed.

[Driver](../../tests/yul-composition/ScopeCatchDriver.lean) executes six capture
outcomes, three actual readback continuations, five mutated scoped halts and
wrong-index/type controls. [Expectations](../../tests/yul-composition/scope-catch-expectations.json)
were frozen BEFORE its execution from these operations. [Reader](../../scripts/yul-composition/scope-catch-source.mjs)
and [mutations](../../scripts/yul-composition/scope-catch-source.test.mjs) bind
actual private/main State/Machine/Eval/Resolved/Hoare, parent Heap→Attempt→peer
hashes, selected catalog, current sources/oracle and actual Lean execution.
All24 ordered calls/four legacy/viaIR optimizer-off/on profiles of the sealed
native report are revalidated transitively, then16 full-byte comparisons link
NEW actual local readback to historical evidence. `nativeExecution` remains
historical-replay-only/fullProofGate pending. Logical heap references are not
EVM pointers. No fresh solc/EVM execution or80MB old-suite regeneration occurred.
123 new/affected JS tests pass; prior broad781JS+2Python and earlier148focused
results stay attributed to their old tested trees. Wrong scope/ref/order/bytes/
full-tail/restoration/raw/post-state and stale producer/private/report/receipt/
selection/fake-adequacy controls fail closed. Both independent read-only finder
and skeptic accepted source/driver/reader/tests with no findings; neither used
Lean/server/build or edited files.

Mandatory joint gate exits0: Lean4.24.0 commit797c613 and Lake5.0.0-src+797c613;
KeySort2jobs; library1228/TestSuite262jobs;377taclets/131annotations;
195core/0elaborator;1243reachable/0orphan; strict491automatic/61budgeted/
0manual/11refuted/0pending; trust1258sources/252sites/0findings. All28 scoped
signatures/transitive axiom reports use only standard axioms/subsets, no new
axiom/sorry. Failed per-file proof-reduction attempts are retained separately
and corrected using actual APIs, not raised budgets or changed verdicts.
Final MCP consumer/driver/root diagnostics all success=true/partial=false/no
errors (nonfatal async shutdown warning retained). Exact committed heads/commands/resources are recorded
in the versioned handoff. Main's standalone producer closure is not claimed;
only private root receives the one owned import over sealed inputs.

Initial321298432byte disk headroom and incremental output were measured before
work. Existing guards, writer lock, serial-j1/LEAN_NUM_THREADS=1, enforced12GiB/
no swap and OS headroom remain unchanged. New stopped zero-write VFS mount
metadata copies alone are verified/logged/retired; all protected caches/images/
mounts/old artifacts/manifests remain. New exports contain only increments and
reference sealed parents. Docs/G03 historical EXIT1 remain FAILURES; exact-base
same findings establish zero regression only. No unchanged failing heavy retry.

Work1/Work3/Work2/BackfillA/B remain PARTIAL, all24 original obligations and six
full Source combinations pending. Still missing: general Source catch selection/
error decoding/raw operators/function/session/frame hooks; physical placement/
allocation refinement/G01; concrete source/compiler/world/V16 adequacy and full
joint closure. LIB1/unchecked-add questions remain unanswered. Actual typed
scope binding/readback is now proved as a consumer component; frontend catch
name resolution/dispatch is not. Original blocked goal untouched; get_goal is
unavailable, no reset/reactivation/completion or publication. Main8a901437 and
private65227843 preserved as ancestors. Immutable incremental handoff/patch/
bundles/interface/evidence/checksums:
`/workspace/vy5-composition/scope-catch-20261101/final/`.


## Captured typed scope to canonical rethrow (2026-11-01)

[RethrowPhysical](../../Solidity/Yul/Composition/RethrowPhysical.lean) consumes the
ACTUAL returned `ScopeCatchPhysical.run` inner locals, whose head is the captured
allocated memory reference, in ACTUAL `Source.execS (.rethrow .here)`. No local
rebuild, allocator/evaluator replacement or raw-to-clean resume occurs. Actual
`EM.sub .nil` transports the evaluator's empty local carrier through the restored
outer typed scope, and actual `attempt` records the resulting halt/post-state
beside the unchanged raw caller. This is the pre-existing canonical rethrow
exception composed with an owned consumer router, NOT general Source.tryStmt
selection, catch-name resolution/error decoding or raw Source assembly dispatch.

20 kernel laws include arbitrary E/typed contexts/Glob/frame/index/locals/state
`exec_rethrow_succ` and `scope_succ`. They require the actual indexed local.get
reference equality and heap.get full-byte object premise; they compute the
actual evaluator/sub operation at EVERY positive fuel (`fuel+1`), without an
assumed execution agreement or supplied desired result. `scope_zero` proves
actual timeout at zero before any dereference. `captured_rethrow` discharges
reference/object premises using the actual prior capture/allocation/scope laws,
for arbitrary bytes and arbitrary Glob, and returns the exact complete result,
restored outer locals and allocated Source.St/raw companion. `positive_unique`
relates any two positive horizons. Full state preservation is relative to the
already captured/allocated post-state, including caller-prefix logs/heap; no
frame/world rollback is inferred. At zero the catch object is ALREADY allocated
and retained even though the rethrow statement times out. Inner evaluator locals
remain nil; actual returned catch locals remain the input argument to execS.

DEAD, empty and full panic payload laws expose exact halts/bytes. Wrong same-type
`.there .here` rethrows old AABB instead of DEAD, despite both length2; dangling
ref2 yields `dangling memory reference` at positive fuel and timeout at zero.
Success bypasses rethrow even at zero, while original timeout/stuck propagate
unchanged. Full raw1793/nonword alias and Source state retention/no-clean-resume
are proved; logical heap indices are never identified with physical EVM addresses. Earlier
coupled physical journals remain their actual owner operations; this module adds
no rollback semantics or pointer placement/refinement premise discharge.

[Driver](../../tests/yul-composition/RethrowDriver.lean) executes12composed cases
and6controls: caught DEAD/empty/panic at0/1/32, success/timeout/stuck and wrong-index/
dangling at0/1/32. Its inhabited empty-program Glob is ONLY a Source fixture;
all laws quantify arbitrary Glob, and no calls/hash/compiler behavior is replaced.
[Expectations](../../tests/yul-composition/rethrow-expectations.json) were frozen
before execution from the actual operations. Every row checks complete captured
bytes/ref/inner order, pre/post raw words, heap next/object/old alias/logs, exact
outcome/fuel and restored typed local. Generic kernel laws establish full St
preservation; finite serialization is not a total-world observation theorem.

[Reader](../../scripts/yul-composition/rethrow-source.mjs) and
[mutations](../../scripts/yul-composition/rethrow-source.test.mjs) fail closed on
missing/malformed/reordered evidence, wrong same-length bytes/panic tail, wrong
scope/reference/raw/state/fuel, stale actual main/private producer/consumer/ledger/
oracle/command/receipt and missing selected catalog. 129 new/affected JS tests
pass. Transitive Scope→Heap→Attempt provenance fully validates the sealed native
report ALL24 ordered calls/four legacy/viaIR optimizer profiles, preserving all
original touched-state/frame/journal/refusal observations and strict-static good().
That native evidence covers PRIOR caught calls, NOT this NEW rethrow path.
Reader requires `rows=[]` AND `nativeComparisons=[]` and the explicit prior-caught
regression role; mutations reject any claimed new native rethrow comparison or
fresh execution/full adequacy. Historical replay is not compiler correspondence.
No new solc/EVM fixture or roughly80MB old-native regeneration occurred. Earlier
781JS+2Python/123focused/148focused results retain their tested-tree attribution.

Joint policy gate exits0: actual Lean4.24.0 commit797c613/Lake5.0.0-src+797c613;
KeySort2jobs; library1229/TestSuite262;377taclets/131annotations;196core/
0elaborator;1244reachable/0orphan; strict491automatic/61budgeted/11refuted/
0pending; trust1259sources/252sites/0findings. All20 exact scoped signatures/
transitive axiom reports use only standard axioms/subsets, no new axiom/sorry.
Module/driver/private root final MCP all success=true/partial=false/no errors;
nonfatal async shutdown warning retained. Committed identities and exact commands/
exits/resources are in the sealed handoff. Main standalone
producer closure is not claimed; one private import over sealed bodies is used.
Independent read-only finder/skeptic accepted source/reader/driver/mutations with
no actionable findings and no Lean/server/build/edit. Initial syntax/proof and
driver failures are retained, fixed without altered verdicts or budgets.

Initial disk314376192bytes and comparable incremental178450432byte cost were
measured. An implementation mistake copied a historical container-name prefix:
the metadata helper refused on a protected old container, but a subsequent
check still ran, temporarily leaving TWO new copies and availableBytes0. Its
wrapper EXIT1/ENOSPC writing the exit receipt is explicitly retained, never a
pass. Recovery preserved inspect/logs/verified directory metadata and retired
ONLY the TWO current stopped SizeRw0 copies; historical containers/images/mounts/
file caches/evidence stayed intact. New unique scope-rethrow prefix and checked
sequential retirement avoid that collision. No guard/capacity floor or proof/
fuel/node/test budget was changed, no protected data deleted. Existing writer
lock, serial-j1/LEAN_NUM_THREADS=1, hard12GiB/no swap and OS-headroom monitoring
remain. Incremental exports avoid large native regeneration. Docs/G03 historic
EXIT1 remain failures with exact-base equality, not global passes.

Work1/Work3/Work2/BackfillA/B remain PARTIAL: all24 original full obligations and
six Source combinations remain pending. Missing general Source selector/error
decoding/raw operator/function/session/frame hooks, physical placement/allocation
refinement/G01, concrete compiler/source/world/V16 adequacy and final joint
composition. LIB1/unchecked-add remain unanswered. Original blocked goal untouched;
get_goal absent; no goal creation/reset/reactivation/completion or publication.
Prior mainb43389dc and privatea2e7ed9a preserved as ancestors. Incremental immutable
patch/bundles/interface/handoff/evidence/checksums:
`/workspace/vy5-composition/rethrow-20261101/final/`.


## Fresh finite native canonical rethrow (2026-11-01)

[NativeRethrowControls](../../tests/yul-composition/NativeRethrowControls.sol)
implements actual Solidity `try this.child(...)` / `catch(bytes memory data)` /
canonical memory-safe `revert(add(data,32),mload(data))`. [Original expectations](../../tests/yul-composition/native-rethrow-expectations.json)
were frozen BEFORE compiler/VM execution: DEAD, empty, full36-byte assert panic,
same-length AABB negative, successful BEEF try branch, getter/dead/getter after
successful marker7, and an actual always-revert negative. Four profiles are
explicitly legacy/viaIR optimizer-off/on, pinned solc0.8.38 commit1835d247 and
Osaka. No original sources/verdicts/old oracle hashes were changed.

A REAL failure remains: the strict original journal oracle expects persistent
writes7→99→8, but viaIR optimized removes the child99/catch8 stores before
unconditional revert. Original-v3 records ALL36 ordered calls/four profiles and
five strict persistent-journal mismatches (calls0,1,2,3,6 in viaIR optimized),
then exits1. Other three profiles have no call-check errors. Full return/revert
bytes and final touched state match the original expected outcomes; the strict
whole-report gate nevertheless remains FAIL. This is not relabelled green,
excluded, or used to claim source/compiler correspondence. Earlier v1 failed a
reader API assumption (partial frame array where compareState requires complete
array); fixed by checking the complete independent root+child frame array,
without removing fields or changing expected semantics. Raw failures/captures/
compiler outputs and the pre-refactor checker snapshot are retained.

The ADDITIVE [ObservedNativeRethrowControls](../../tests/yul-composition/ObservedNativeRethrowControls.sol)
adds actual external view `checkMarker(99)` in child and `checkMarker(8)` in
catch. These reads make the writes observable before rethrow. Its SEPARATE
[expectations](../../tests/yul-composition/observed-native-rethrow-expectations.json)
were also frozen BEFORE its compiler/VM execution, derived from the new source;
it does not replace the original failed fixture. Failed paths have exactly four
frames: root0/child1/audit99frame2depth2/audit8frame3depth1. Audit pre/post reads
must see marker99/transient33 and marker8/transient22. Audits return empty bytes:
root final returndata buffer is therefore EMPTY, while allocated catch memory
still retains the original complete payload for canonical rethrow. Relative
REVERT windows check full data, including empty and panic tail; compiler memory
addresses/final arbitrary memory are not equated across pipelines (YQ3).

Final hardened observed-v2 passes actual36calls/four profiles. All nine calls
per profile preserve exact ordinal/selector/caller/owner/code/static/depth/value,
success/failure/exception/full bytes, ordered logs, complete declared API-touched
pre/post account balances/nonces/code and persistent/transient slot maps. Slot0
is independently derived from marker storage layout; CREATE address from caller
and nonce0, code from compiler output rather than observed VM state. Ordered
persistent/transient writes, child/outer rollback, frame prefix restoration,
audit states, child/root buffers and semantic RETURN/REVERT/LOG windows are
checked. Successful BEEF/marker7 followed by later reverted DEAD/getter detects
lost caller-prefix state. Wrong AABB and actual always-revert must NOT match the
selected Source DEAD and success outcomes. These are genuine executed negatives,
not changed expected verdicts. runCall and its host cleanup remain distinct from
runTx/finalization; untouched-world/total-state/source adequacy is not asserted.

[Core adapter](../../scripts/yul-composition/native-rethrow-core.mjs) reuses the
UNCHANGED shared machine/capture/compiler primitives, with two lane-owned
[original](../../scripts/yul-composition/native-rethrow.mjs) /
[audited](../../scripts/yul-composition/observed-native-rethrow.mjs) configurations.
It binds pinned source/compiler/settings/input/output/code/runtime/ABI/layout,
current core/wrapper/shared-engine/dependency-lock hashes, actual capture files,
ordered matrix and execution receipt. A passing report requires exact empty
row.errors as well as recomputed call checks; independent skeptic found this
consistency gap and it is fixed, tested and re-executed with hardened hashes.
No shared engine, dependency lock, instruction/gas limit or producer body changed.
Advisory AST policy checks are not VY1 Lean admission/importer proofs.

Full prior actual RethrowDriver Source execution is SHA-bound and revalidated,
including all24 historical caught calls transitively. NEW native result links
compare only failure and FULL bytes against actual completed Source cases:
20 positive comparisons and eight intended negative comparisons across four
profiles. Native state is independently checked; it is NOT equated to the
different logical Source companion heap/logs/journals. Source zero-fuel timeout
cases remain unlinked controls, never native execution evidence. Source success
case9 is explicitly a bypass with NO rethrow executed; its fuel0 is unused and
not identified with native gas. No new kernel theorem, general Source catch
selector/error decoding/raw dispatch or compiler/world/V16 adequacy follows.

138 new/affected JS tests pass, including coherent same-length payload/panic-tail/
always-revert mutations, equal-return wrong world/storage/transient/audit/journal/
window, missing/reordered/stale profile/source/receipt/core/engine/model evidence,
required registry removal and pass+error consistency. They explicitly assert
original36-call strict failure and unchanged original freeze hashes. Both
independent read-only finder/skeptic accepted source/factory/additive distinction
and tests; no builds/Lean/server/edit by reviewers. Their report-consistency
finding is repaired. Prior eight mutants/227working/21fork blocks and all sealed
reference observations remain attributed to their original tested trees.

No Lean file/import/signature/axiom or private dependency body changed. Existing
RethrowPhysical20laws and joint1229/TestSuite262/KeySort2/strict/trust/MCP results
remain attributed to mainf827c43d/private33b48a30, with Lean4.24.0/Lake5.0.0-src+
797c613 and standard scoped axioms; no new kernel pass inferred from JS/solc/EVM.
Unchanged expensive Lean/full-corpus gates were not rerun. Current focused script
checks, exact unchanged kernel-file comparison, preserved signature artifacts
and source-body validation cover the actual change. Docs/G03 EXIT1 with exact
pinned-base equality remain FAILED global gates, not passes.

Initial308588544byte measured headroom minus comparable178450432byte container
cost and16MiB output estimate left113360896bytes projected. Actual small outputs
were measured before each next operation; cached serial runs fit. Unique empty
native-rethrow prefix and checked metadata retirement before the next container
avoid the prior collision. All protected images/mounts/caches/evidence/history
are preserved; only current stopped SizeRw0 directory-only metadata copies are
verified/logged/retired. Existing writer lock, enforced12GiB/no swap, OSheadroom,
serialLEAN_NUM_THREADS=1 and gas100000000/step5000000/proof/test budgets remain
unchanged. No broad80MB native corpus regeneration, guard relaxation or ENOSPC.

Work1/Work3 remain PARTIAL: all24 full obligations/six Source combinations and
actual general selector/raw hooks/physical placement/refinement/G01/compiler/
world/V16/joint closure pending. Work2/BackfillA/B advance fresh finite selected
rethrow evidence but remain PARTIAL, including the ORIGINAL strict native journal
mismatch and remaining corpus/state-source obligations. LIB1/unchecked-add stay
unanswered. Original blocked goal unchanged/get_goal unavailable; no goal status
mutation, producer retrieval, push/merge/PR or service. Reviewed immutable
incremental patch/bundle/interface/handoff/evidence/checksums:
`/workspace/vy5-composition/native-rethrow-20261101/final/`.


## Actual Source runtime block and ABI-error consumers (2026-11-02)

The latest inventory had direct canonical rethrow but NO runtime local declaration/
block composition. [RuntimeBlockPhysical](../../Solidity/Yul/Composition/RuntimeBlockPhysical.lean)
adds28 kernel laws in the owned namespace, consuming existing intrinsic Source
constructors/semantics only. `aliasDecl` is ACTUAL resolved `.declInit (.local i)`;
`declare_run` executes `evalE`/identity `convRV`/`getV`, returning the new indexed
local followed by original locals. `aliasItems`/`aliasBlock` execute actual
`execItems`/`execS`, then rethrow through the NEW alias head. Generic Env/Glob/
frame/contexts/local-reference and heap.get premises are exact. Full error bytes
and complete Source.St propagate for EVERY horizon `fuel+4`;0–3 are real runtime
timeouts. This is not another fixed counter sample or a supplied execution oracle.

The next independently ready leaf also advances: ACTUAL `Source.reraise` /
`EM.attempt` / `allocRef`+full readback / runtime declaration-block rethrow.
`outcome_revert` computes this complete chain for arbitrary bytes and typed
caller state. `allocatedState` merely names the actual `Heap.alloc` post-state,
not a replacement allocator. All Source.St fields except the real heap allocation
are retained, and typed outer locals restored around the evaluator's empty local
carrier. `runtime_actual` exposes an arbitrary actual action.run result AND its
post-state, with NO desired execution premise; it does NOT claim arbitrary
actions restore their prior locals/state. Successful `reraise` bypasses allocation;
timeout/stuck propagate. `stuck_post` executes real modSt+halt and retains the
actual prefix update, never inventing rollback.

ACTUAL `Source.extReturn` is an UNFUELLED helper taking returns/outcome (no invented
frame/fuel arguments). `ext_return_revert` proves full reverted bytes propagate
BEFORE any length/ABI decoding, for any return signature. `externalResult` is an
explicit consumer that discards a successful decoded value only AFTER running
the real helper. `external_revert` composes its full nonempty error with actual
allocation/declaration/rethrow; `short_return_caught` contrasts an explicit DEAD
revert with a successful two-byte DEAD payload for bool returns: the latter
really triggers EMPTY revert before allocation. No favorable decoder oracle,
new Source hook, catch selector or reserved Source implementation is introduced.

Inhabited sample uses the SAME actual raw caller from the previous physical catch
witness: seven exact dirty cells including bool2/small1793/function fields,
nonword alias0/AABB and caller-prefix log55. The complete actual result/typed locals/
newheap are proved; full DEAD, empty and panic payloads, old alias and raw refusal
are retained. Wrong alias initialization picks old AABB instead of new DEAD even
though both length2. No ofClean/runClean resume is used on actual dirty cells;
no_clean_resume is proved. Logical indices are never identified with physical
EVM pointers. Real physical placement/MemOK/allocation refinement/G01 and separate
physical journals remain premises/open; local scope restoration is not world or
frame rollback. Ordinary raw Source operators/functions/sessions remain missing.

[Driver](../../tests/yul-composition/RuntimeBlockDriver.lean) executes actual
Source declaration and extracts refs[1,1,0],12 runtime outcomes and wrong-alias
readback. [Expectations](../../tests/yul-composition/runtime-block-expectations.json)
were frozen before execution. [Reader](../../scripts/yul-composition/runtime-block-source.mjs)
and [mutations](../../scripts/yul-composition/runtime-block-source.test.mjs) bind
actual main/private Source Types/Value/Elaborated/Machine/Eval/Resolved/State/Hoare,
parent producer/consumer provenance, exact own bodies/ledger/oracle, actual Lean
command/stdout/stderr/exit and selected registration.130 new/affected JS tests
pass. Full bytes/panic tail, declared alias/order, low-fuel allocation, wrong
ABI branch, prefix/nonword/raw/scope/state and stale/missing evidence controls
are discriminating. Driver serialization is finite; generic kernel laws establish
full Source.St equality. ZERO new native comparisons/execution are claimed; prior
24call historical evidence and ORIGINAL five native strict journal FAILs are
SHA-bound and retained. No new native fixture substitutes for these kernel leaves.

Private joint gate exits0: actual Lean4.24.0 commit797c613/Lake5.0.0-src+797c613;
KeySort2jobs; library1230/TestSuite262;377taclets/131annotations;197core/
0elaborator;1245reachable/0orphan; strict491automatic/61budgeted/11refuted/
0pending; trust1260sources/252sites/0findings. All28 exact signatures/transitive
axioms standard propext/Classical.choice/Quot.sound or subsets, no new axiom/sorry/
native proof shortcut. Final MCP consumer/driver/private root success=true,
partial=false/no errors; async shutdown warnings retained. Failed initial typing/
constructor reduction/actual API signature/dependent-layout inference diagnostics
are preserved separately; fixed by real constructors, explicit intrinsic indices
and actual laws, without changed premises/outcomes/budgets. Main standalone
producer closure is not claimed. Only a narrow private root import is added.
Independent read-only finder/skeptic accepted kernel, driver, reader and mutations
with no findings and no Lean/server/build/edit.

EXACT pending VY4 consumer request (not an assumption/publication, no active peer
interruption): `/workspace/vy5-composition/runtime-block-20261102/producer-request.json`.
Existing declaration is `Source.callAddr G F n address value input static :
Source.EM E [] Solidity.Roadmap.Outcome`. Requested packet supplies actual module/
names/commit/source hashes, inhabited ordinary typed body/Env/Glob/frame/state/
request and kernel-checked NONEMPTY revert/full post-state execution, with real
caller-prefix/heap/frame premises. Source.reraise then feeds the proved generic
consumer; no ordinary typed-function execution or callAddr agreement is assumed.
Coordinator may relay the exact checked packet when ready. General Source try
selection/error decoding and raw function/frame/session hooks remain OPEN.

Initial291897344byte disk and comparable178450432byte metadata-copy growth were
measured; an8MiB incremental estimate fit. Actual process/container inventory was
idle before admission. Original supervisor/data unchanged; task-local supervisor
also monitors the actual repository12GiB AVAILABLE-memory reserve, alongside the
unchanged hard12GiB cgroup cap/memory=memorySwap/no swap/CPU1, explicit-j1,
LEAN_NUM_THREADS=1 and shared writer lock. All minimum available samples exceed
12GiB; no admission/resource stop, cleanup or hidden failure. Unique runtime-block
prefix and verified stopped SizeRw0 directory-only metadata retirement preserve
all protected caches/images/mounts/evidence. No host-wide imagined token across
other VMs. No representation refactor or raised proof/fuel/node/test budget.
Docs/G03 historical EXIT1 remain failed global gates with exact-base equality,
not passes. Old native failures and optional LIB1/unchecked-add/vendor holds
remain unchanged; approved SpecConstants correction is not imported or broadened.

Work1/Work3 advance these concrete runtime/heap/raw/ABI kernel consumers but remain
PARTIAL: all24 original obligations/six full Source combinations and final joint
Source/compiler/world/V16/G01 adequacy remain pending. Work2/BackfillA/B remain
PARTIAL with existing native journal failures and broader corpus/world/source
obligations. No whole-lane absence was used to block the two ready leaves. Original
blocked goal unchanged/get_goal unavailable; no reset/reactivation/completion,
new VM/thread/producer retrieval, push/merge/PR/service. Reviewed exact committed
heads/signatures/request/patch/bundles/raw evidence/checksums:
`/workspace/vy5-composition/runtime-block-20261102/final/`.


## Actual modifier and internal-call rethrow (2026-11-02)

[ModifierPhysical](../../Solidity/Yul/Composition/ModifierPhysical.lean) adds30
kernel laws consuming ACTUAL `Source.runMods`, `.placeholder`, `execItems` and
`callInternal`. No Source/** implementation, AST, frame evaluator or world/callAddr
semantics is copied or changed. `body` uses the already proved alias declaration/
rethrow items, parameters Γ.reverse, no returns, intrinsically indexed context Γ
and actual `RModInv`. `no_modifiers` proves its real runMods[] execution for
arbitrary appropriate typed locals and complete reverted bytes/state at fuel+4.
Only actual local.get-reference and heap.get-full-byte premises remain.

The actual `aroundBody` has ONE real typed placeholder. `withAround` supplies an
explicit resolved program lookup; `lookup_around` computes actual dispatch/body
lookup rather than assuming an execution result. `placeholder_revert` checks
BOTH actual pipeline branches: legacy uses current typed parameter locals;
viaIR runs real zeroInner0 on original locals. This selected function has ZERO
return slots, so no reset/return-value difference or unanswered library/unchecked
result is inferred. `one_modifier` executes actual argument evaluation, dispatch,
frame installation, placeholder/body entry, attempt/error capture, saved-frame
restoration and halt re-raise at EVERY fuel+7. The original saved fnLocals may be
ANY intrinsically typed sigma frame; complete Source.St, heap, source journals,
logs/events and full revert bytes are retained. Scope/frame-local restoration
is NOT world rollback. No desired execution outcome or assumed agreement appears.

The next ready leaf also advances: selected `callInternal` execution through
real function signature, dispatch/body lookup, zero return values, actual
parameter `.onto`, exact return/parameter frame equality and checked-frame entry.
Parameters are two bytes-memory references: arguments old/current become actual
locals current/old. `internal_revert` proves full bytes and complete state at
EVERY fuel+8.0–7 are actual timeouts, including cases AFTER temporary frame
installation; the saved frame is restored even then. `parameters_onto` and
`function_frame` prove exact order/type equality, not a fabricated frame oracle.
No callAddr/world implementation or external ordinary-function packet is assumed.

These are explicit SELECTED RESOLVED runtime program inputs, not a theorem that
the frontend derived/admitted their declaration/body records. Source declaration
keys and runtime program lookup are provided as data; RBody.Derived, source
resolution/typing/admission and general modifier/assembly coverage remain open.
The selected runtime function/placeholder execution itself is concrete and uses
existing semantics. It does not close the original general modifier combination
or any G48–G51 obligation. Source.Resolved still has no general try selector;
none is invented. The VY4 callAddr packet request from the prior checkpoint
remains pending, and its active producer was not contacted or interrupted.

Inhabited `sample` reuses the actual prior physical/raw caller with seven dirty
cells (including bool2/small1793/function fields), nonword alias0/AABB and prefix
log55. Its heap already contains the complete caught bytes at logical index1.
Saved fnLocals is deliberately a DIFFERENT booltrue frame, unlike installed
function locals [current1,old0]. Full actual sample result/state/raw/frame are
proved, with no clean resumption. Wrong alias returns AABB instead of DEAD despite
equal length2; new heap object1 stays DEAD. Low-fuel, missing modifier/function
body, wrong modifier parameter metadata, bad call frame, placeholder outside a
modifier and invalid placeholder frame are real existing API guards. Deliberately
incoherent API-input controls are not claimed to be admitted source programs.
Logical indices never identify physical EVM addresses; actual physical placement/
MemOK/refinement/G01/compiler/world premises remain open.

[Driver](../../tests/yul-composition/ModifierDriver.lean) executes42 actual Source
cases across legacy/viaIR and two direct-placeholder controls. An alternate saved
ONE-memory-reference frame must also be restored, preventing hardcoded boolframe
restoration. The direct placeholder leaves the installed TWO-reference frame on
error; outer runMods is what actually restores the saved frame. Full bytes,
panic tail, wrong alias, all0–7 horizons, raw/nonword/heap/prefix and exact frame
shape/value/reference order are frozen independently in
[expectations](../../tests/yul-composition/modifier-expectations.json) BEFORE
execution. Generic kernel laws prove complete Source.St equality; finite driver
serialization does not claim whole-world enumeration or source/compiler adequacy.

[Reader](../../scripts/yul-composition/modifier-source.mjs) and
[mutations](../../scripts/yul-composition/modifier-source.test.mjs) bind exact
current main/private Source Decls/Syntax/Types/Value/Elaborated/Machine/Eval/
Resolved/State/Hoare, prior producer/consumer chain, current module/driver/ledger/
oracle, selected registration and actual Lean command/output/exit.138 new/affected
JS tests pass, including same-length full-byte, frame type/value/order, alternate
versus installed frame, low-fuel finally restoration, missing/invalid APIs,
raw/high-bit/nonword/heap/prefix and stale/missing/reordered evidence. ZERO new
native comparisons/execution; old24call historical evidence remains historical,
and the five strict original optimized-viaIR native journal FAILs are SHA-bound
unchanged, pending their separate decision. Prior expected outputs/profiles are
not changed. No new native fixture is used instead of kernel composition.

Actual joint policy gate exits0: Lean4.24.0 commit797c613/Lake5.0.0-src+797c613;
KeySort2jobs; library1231/TestSuite262;377taclets/131annotations;198core/
0elaborator;1246reachable/0orphan; strict491automatic/61budgeted/11refuted/
0pending; trust1261sources/252sites/0findings. All30 exact signatures/scoped
transitive axiom reports use standard axioms/subsets, no new axiom/sorry/admit/
native-proof shortcut or raised budget. Final per-file MCP and exact committed
identities are recorded in the handoff. All failed proof-reduction/name/typing
attempts are retained and corrected with real equations, not new assumptions.
Both independent read-only finder/skeptic accepted kernel/sample/driver/reader/
mutations with no findings and no Lean/server/build/edit. Main standalone producer
closure is not claimed; private root gets only the narrow new import.

Initial285388800byte disk was measured against178450432byte comparable container
layer and8MiB conservative source/build/Git/evidence allowance (~98.5MB remainder).
No surviving job existed. One combined edit/retirement/check action was REJECTED
by automatic approval review BEFORE execution when current free space was110MB
with an exited current-step layer still present. No bypass/indirect heavy check
ran. Read-only probes established stopped/SizeRw0/directory-only changes and
retained receipts; separate review APPROVED the already user-authorized current
metadata-only retirement after preservation. Disk returned to285MB before any
heavy retry. Subsequent operations separately retire/measure then admit checks.
No old container/cache/image/mount/history/evidence was deleted; no guard lowered.
Exact rejection/probes/recovery are in approval-capacity-receipt.json. All heavy
checks preserve the real writer lock, hard12GiB/no-swap/CPU1,12GiB available reserve,
serial-j1/LEAN_NUM_THREADS=1 and original proof/fuel/node/test limits. No resource
stop occurred. No broad native regeneration or foreign package/branch adoption.

Historical docs/G03 EXIT1 and exact pinned-base equality remain FAILURES; unchanged
failing global gates are not rerun for activity. New handoff links are checked
separately. All Work1/2/3 and BackfillA/B remain PARTIAL: all24 original obligations
and six general Source combinations, frontend derivation/general modifiers, raw
Source hooks, real Source try selection, physical placement/refinement/G01 and
concrete compiler/world/V16/final joint adequacy remain open. LIB1/library-viaIR1834,
unchecked-add and optional-vendor decisions remain unanswered. Original blocked
goal unchanged/get_goal unavailable; no reset/reactivation/completion, replacement
VM/thread, cross-thread message, push/merge/PR or service. Reviewed immutable
patch/bundles/interface/full signatures/request references/evidence/checksums:
`/workspace/vy5-composition/modifier-body-20261102/final/`.

## Actual selected returning CALL/STATICCALL decoder (2026-11-02)

VY5 consumes the immutable VY4 private producer
`fd3da385f5e4ada7aa889821d3ae59a34833d235` from
`/workspace/shared/parallel-vy4-general-returning-4d6b5b8d`.
The bundle/archive hashes and exact 183-module actual import closure are recorded
in `/workspace/vy5-composition/return-consumer-20261102/producer-provenance.json`.
Existing producer bodies matched byte-for-byte; only missing imports were staged
in the existing private tree. The producer's different Solidity.lean was NOT
adopted. No Source owner bodies, other checkout or branch were modified.

[ReturningPhysical](../../Solidity/Yul/Composition/ReturningPhysical.lean) adds19
kernel laws. `call_decode` and `static_decode` execute the actual selected physical
call via `GeneralReturning.call_actual`/`static_call`, then actual `Source.extReturn`
for `[uint256]`. Full32byte data decodes to
`0x11223344 * 2^224 + 0x55`; same-length encoded value+1 decodes differently, short
success data becomes empty revert, and all revert bytes propagate unchanged.
The exact returned physical completion is retained alongside actual decoder
post-state, including source locals/St, heap, fnLocals, events/logs, ordered
supplied trace and residual/Bool journals. No second state semantics is defined.
`call_decode_encoded` discharges input loading from actual VY2 Placement,
HeapByteEntry membership/Nodup and encoding. `copied_decoder` separately consumes
actual bounded `copyOutput` on the selected success completion, then decodes the
unchanged full returndata with the entire copied source heap retained. It is an
output-copy/decoder component, not a new universal call/copy sequencer theorem.
Its required shared-execution premise is explicit and definitionally discharged
for that actual success completion; initial failed diagnostic is preserved.

`sample_run`/`static_sample` inhabit the actual two-object encoded heap, two memory
aliases/saved fnLocals, caller event/log prefix and source/residual/Bool carriers.
Theorems quantify any supplied Glob, hence both actual pipelines. Actual transfer
failure is consumed as empty revert; actual horizon6 timeout keeps the dirty
transferred execution and OLD return buffer rather than rollback/normal EVM
failure. Missing registration and invalid physical input are adapter None, not
EVM halt. Nonempty revert decoder transport DOES NOT supply the still-requested
ordinary-function nonempty-revert producer packet. The existing immutable request
remains `/workspace/vy5-composition/runtime-block-20261102/final/producer-request.json`;
no active producer was contacted/interrupted and no packet was assumed.

Real premises remain: selected Finite/answer typed runtime program, receiver64
code0, owner48, CALL value7 or STATICCALL value0, actual transfer equality,
Fixed-derived selector, depth1/horizon10, observation execution sharing, complete
SUPPLIED prefix, physical load or layout/ownership/bounds. Supplied observations
are not Source emit/G01 adequacy. No gas/resource adequacy, arbitrary callee,
frontend derivation/admission, logical-index/EVM-pointer identity, raw-to-clean
resumption or missing Source try selector is inferred.

[returning-ledger.json](../../tests/yul-composition/returning-ledger.json) and
[returning-source.mjs](../../scripts/yul-composition/returning-source.mjs) fail closed
on source/signature/producer identity/body/closure/path drift and false coverage,
fresh native evidence or erased original failures. Finder and skeptic both found
a coordinated mutable-provenance/hash vulnerability in the first guard. Exact
verified provenance record/path are now pinned, with coordinated body+claimed-hash,
transitive omission and redirect controls. Final23JS tests pass. No fresh native
or solc/EVM suite was run; historical complete observations and five strict native
optimized-viaIR journal mismatches/EXIT1 remain untouched.

Per-file MCP after edits and affected closure pass. Actual versions are
Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b and
Lake5.0.0-src+797c613. Required joint command ran KeySort2jobs, full1283jobs,
TestSuite262jobs, exact19 signatures/scoped standard axioms, orphan1298/0/0 and
strict491automatic/61budgeted/0manual/11refuted/0pending successfully, then EXIT1
because VY5 supplied an incomplete trust stdin list. Corrected complete-list trust
passed separately:1313sources/252sites/0findings. The original combined EXIT1
is retained, not relabelled a pass. First unsupported Lake -j flag EXIT1 is also
retained; corrected supported wrapper uses explicit Lean -j1 in existing TOML.
No proof/fuel/heartbeat/node/test budget or semantic change.

Resources: initial276529152free bytes; compatible source staging left275947520.
Producer build cache grew approximately36.8MiB, exceeding the initial25MiB
incremental estimate; post-closure capacity was remeasured239153152 before the
next gate (178450432comparable layer plus8MiB remaining allowance). Existing hard
12GiB/no-swap/CPU1, serial LEAN_NUM_THREADS1/-j1,12GiB OS-available reserve,
writer lock and all capacity guards remain unchanged. Only current verified
exited SizeRw0 directory-only metadata containers were retired AFTER preserving
inspect/log/directory receipts. All images/caches/mounts/sealed history retained;
no resource stop or hidden cleanup. Exact receipts/raw failures live under
`/workspace/vy5-composition/return-consumer-20261102` and its final seal.

All Work1/2/3 and BackfillA/B remain PARTIAL; all24 original obligations/six general
Source combinations/fullProofGate remain pending. General Source try selection,
raw operators/functions/sessions, G01/allocation/world/compiler/V16 adequacy and
final joint closure remain open. LIB1/library-viaIR1834, frozen unchecked-add,
strict journal and optional-vendor questions remain unanswered. Original blocked
goal unchanged; get_goal unavailable, no reset/reactivation/completion. Historical
docs/G03 EXIT1 exact-base equality is zero regression ONLY and not rerun for
activity. Immutable checkpoint/peer-input/signatures/evidence/checksums:
`/workspace/vy5-composition/return-consumer-20261102/final/`.

## Actual unchecked and while constructors (2026-11-02)

[UncheckedLoopPhysical](../../Solidity/Yul/Composition/UncheckedLoopPhysical.lean)
adds24 kernel component laws over the actual existing Source evaluator; these
are NOT the24 original full Y10 obligations, which all remain pending. No owner
Source bodies, intrinsic AST/state, arithmetic policy, admission or interpreter
were changed. The existing alias body has SCtx false/false, while unchecked and
loop bodies require different intrinsic indices. `items` builds the SAME
`.declInit (.local index)` / `.rethrow .here` leaves at their actual R/M/SCtx/RCtx
indices; `existing_items` proves equality with RuntimeBlockPhysical.aliasItems
at its original specialization. No untyped recontextualization is introduced.

`unchecked_run` executes actual Source.execItems.unchecked at fuel+4 for arbitrary
well-typed rest, nps/ph, Globals/frame, return/modifier types, input locals and
Source.St. Real reference equality and exact bytes heap lookup are explicit.
Inner evaluation uses the actual frame with checked=false; actual full-byte
revert stops arbitrary rest. Exact evaluator locals and entire Source.St are
retained, including heap/fnLocals/log/world/journal fields. `unchecked_decl_rest`
separately proves the real NORMAL path restores the old local context and runs
arbitrary rest under ORIGINAL F, using a constructive dependent Locals.restore
law. It does not decide frozen unchecked-add compiler behavior.

Actual Source.EM.sub and EM.attempt then transport that execution to arbitrary
outer typed locals and existing raw LocalValues, WITHOUT runClean/ofClean or
cleaning/resuming dirty locals. `carry_run` retains exact raw companion plus
supplied residual and Bool journals. Those journals are explicit boundary data,
not a new world rollback operation. The inhabited sample uses the actual
LocalPhysicalControls.firstPhysical represented source action and BOTH its real
journals, existing raw1793/dirtybool2/function-field cells, real Heap.alloc
post-state, old nonword heap alias0 and caller-prefix55. DEAD, empty, full assert
panic, poison-rest and same-length wrong old-alias AABB controls preserve full
payload distinctions. Source rethrow here retains state; frame rollback is not
inferred from this canonical-rethrow constructor.

The independently ready while child is also implemented: `while_false` evaluates
actual `.bool false`/EM.sub/getV and exits normally at fuel+2, before body access.
`while_true` evaluates actual true and executes the contextual alias/rethrow
block at fuel+5. `while_break` executes the real break branch and preserves
locals/state. `while_continue_step` proves the real literal-true/continue loop
consumes one horizon; induction proves timeout at EVERY horizon with identical
locals/state. This is not divergence for arbitrary loops or generic assembly
coverage. Low unchecked horizons0..3 and true-loop horizons0..4 are exact
state-preserving timeouts. No fuel/heartbeat/node/test budget was raised.

[UncheckedLoopDriver](../../tests/yul-composition/UncheckedLoopDriver.lean) runs44
ordered ACTUAL SOURCE cases (22per Source pipeline) against
[expectations frozen before execution](../../tests/yul-composition/unchecked-loop-expectations.json).
Full selected observations include return/revert/panic/stuck/timeout bytes,
raw words, both byte objects, heap extent, saved fnLocals, restored outer alias,
caller prefix, reconstructed persistent word2868903938 and full selected
residual/owned journals. The whole Source.St/carrier preservation theorem is
kernel evidence; finite JSON observations do not enumerate the entire world.
Actual bad logical reference99 is stuck, not silently empty; no logical heap
index is identified with an EVM pointer. Both legacy/viaIR Source settings match;
this is ZERO fresh solc/EVM/native comparisons, not four native compiler profiles.
All original ordered native observations and five strict optimized-viaIR journal
FAILs/original EXIT1 remain unchanged.

[unchecked-loop-source.mjs](../../scripts/yul-composition/unchecked-loop-source.mjs)
pins module/driver/oracle/ledger and actual private bodies; prior modifier/runtime
and complete verified producer closures remain validated. It checks exact
command/dependency/exit/stdout/stderr and actual execution receipt, full selected
case/profile ordering, every expected field and selected registration. Final56
JS tests pass, including44-case receipt replay, wrong full bytes/old alias/panic
tail, false branch/continue, dirty reset/nonword/frame/outer restore, prefix and
journal/high-bit/owner/slot loss despite equal return bytes, stale bindings and
missing/malformed receipt/output. Finder and skeptic found no actionable issue;
optional runner-SHA traceability is covered by the sealed artifact identity,
not claimed as an existing original execution-receipt field.

Per-file MCP after module/driver edits passes. One initial repeated recursive
expression hit default200000 heartbeats; factored ACTUAL condition/getV/body
execution fixed it without increasing budgets. Explicit type inference, scope
restore and Pipeline namespace failures remain in raw logs. Required final
joint command EXIT0: Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613, KeySort2jobs, library1284jobs/TestSuite262, scoped24 exact
signatures/standard axiom sets, core200/0elaborator,1299reachable/0orphan/0notallowed,
strict491automatic/61budgeted/0manual/11refuted/0pending and correct COMPLETE-input
trust1314sources/252sites/0findings. The previous Returning joint EXIT1 and separate
corrected trust pass remain their original outcomes. Historical docs/G03 EXIT1
with exact-base equality remains global FAILURE, not rerun for activity; only new
handoff links are checked. No axiom/sorry/admit/native-proof shortcut or semantic
weakening. Full gate commands/raw failures/resources are sealed separately.

Resource plan:233070592initialfree -178450432comparable container layer -8388608
conservative incremental allowance =46231552projected remainder. No new dependency
closure, native archive regeneration, quota/guard reduction or protected-data
cleanup. Existing writer lock, serial Lean-j1/LEAN_NUM_THREADS1, hard12GiB/no-swap,
CPU1/12GiB OS-available reserve and caches unchanged. Before each check, only this
step's verified exited SizeRw0 directory-only mount metadata containers were
retired after retaining logs/inspect/directory receipts; images/mounts/evidence/
history protected. No resource stop or ENOSPC; final measurements in handoff.

Work1/2/3 and BackfillA/B remain PARTIAL. All24 original obligations/six general
Source combinations/fullProofGate remain pending: frontend derivation/admission,
general raw operators/functions/sessions, Source try selector and ordinary
nonempty-revert producer, allocation/refinement/G01/compiler/world/V16 and final
whole-tree adequacy. Existing immutable producer request is unchanged at
`/workspace/vy5-composition/runtime-block-20261102/final/producer-request.json`.
No new packet or active-producer contact assumed. LIB1/library-viaIR1834, frozen
unchecked-add, strict journal and optional-vendor decisions remain unanswered.
Original BLOCKED goal identity/objective/status unchanged; get_goal not exposed,
no reset/reactivation/completion. Reviewed incremental source/signatures/patch/
bundles/provenance/evidence/checksums:
`/workspace/vy5-composition/unchecked-loop-20261102/final/`.

## Actual Source for-loop composition (2026-11-02)

[ForPhysical](../../Solidity/Yul/Composition/ForPhysical.lean) adds30 component
kernel laws using existing Source.execS.forLoop/forIter, not LoopPhysical's Yul
`.for_` runner. These30 laws do not discharge the24 ORIGINAL full obligations
or six general Source combinations, all still pending. No Source producer,
Yul interpreter/AST, expected compiler result, admission or resource/proof budget
was changed. Existing private committed inputs were reused; no active VY4
checkout/package was inspected, fetched, contacted or assumed.

Actual initializer execution creates a fresh typed bool above arbitrary clean
callee locals. Actual indexed condition evaluation and getV read that local.
`for_false` proves normal exit at fuel+3 for arbitrary typed body/post and
removes the initializer scope using the real Locals.restore. `for_revert` at
fuel+6 runs init/first condition and the existing contextual alias/rethrow leaves
with exact reference and heap lookup premises; arbitrary post is unreached.
`revert_skips_rest` at fuel+7 also suppresses arbitrary AFTER-loop items on the
full-byte halt. Entire Source.St and evaluator locals are retained, not projected
bytes/length alone. No desired execution result is a theorem premise.

`for_break` at fuel+3 skips arbitrary post; `for_break_body` at fuel+5 executes
actual block/items BREAK and skips remaining BODY items as well. Importantly,
`break_runs_after_loop` executes statements AFTER the loop: a body BREAK is not
a function revert. The concrete poison post indexes byte100 of length2 and,
when actually reached by CONTINUE, emits the full existing panic.index0x32 data.
Its refusal is checked separately, not supplied as an outcome premise.

`post_run` executes real nested Source.assign operations: fresh loop condition
and existing CLEAN callee flag both become false. `for_continue` at fuel+5
executes CONTINUE, this post, and the NEXT actual false test, then removes only
the init local and returns changed clean callee locals. Missing post is not a
vacuous variant: actual forIter horizon-step and induction prove timeout at
EVERY finite horizon, including full init/forLoop execution. Exact low rethrow
horizons0..5 and continue horizons0..4, wrong init-control (`stuck for initializer`)
and dangling99 controls remain distinct. This is a deliberately selected runtime
initializer negative, not a claimed frontend-admitted program.

Actual EM.sub restores arbitrary old evaluator/caller locals while returning
changed clean loop locals as typed Out DATA; EM.attempt captures the real halt.
`carry_revert`/`carry_continue` retain existing raw LocalValues and BOTH residual/
Bool journals as explicit companions over identical full Source.St. Clean callee
bool changes are NOT written into the separate dirty raw caller, and no runClean,
ofClean resumption or missing raw Source hook is invented. Actual firstPhysical
represented source/journal execution plus real Heap.alloc supplies a nontrivial
inhabited sample with rawbool2/function fields/small1793/nonword alias0, prefix55
and full represented word0xab000002. Retention is not a new world/frame rollback.

[ForDriver](../../tests/yul-composition/ForDriver.lean) executes56 ordered SOURCE
cases (28per actual Source pipeline), matched against
[expectations frozen before execution](../../tests/yul-composition/for-expectations.json).
Full selected observations include complete DEAD/empty/assert/index panic bytes,
AABB same-length wrong alias, clean input/result scopes, inittrue/false values,
changed clean bool, restored EM outer reference, all dirty/function/nonword cells,
heap byte objects/extent, saved fnLocals, prefix, reconstructed word and selected
complete residual/owned journal lists. Whole Source.St equality is kernel evidence;
finite observations are not world enumeration or source/EVM correspondence.
Normal false condition does not read an invalid body reference. After-loop AABB
rethrow runs after break but is suppressed by the actual DEAD body revert.

[for-source.mjs](../../scripts/yul-composition/for-source.mjs) binds actual module,
driver, oracle, ledger, transitive immutable producer/private bodies AND current
runner SHA before execution. Exact command/dependency/exit/stdout/stderr/execution
receipt/fieldsets/ordered profiles/cases and summary are checked fail closed.
72JS tests pass: post/next-test omission, skipped body/outside-rest confusion,
full panic tail/wrong bytes, scope and refs, clean/raw flag confusion, same-type
function aliasing, prefix/frame/high physical bits/owner/slot/journal loss despite
equal return bytes, stale identities and missing/malformed actual evidence.
Finder/skeptic read-only reviews accepted all proofs/controls without findings.
ZERO fresh native/compiler/EVM comparisons; original complete ordered native
observations and all five strict optimized-viaIR journal FAILs/EXIT1 unchanged.
No LIB1/library-viaIR1834, frozen unchecked-add, journal or optional-vendor semantic
question was answered.

Per-file MCP after module/driver edits and affected build pass. Raw equation,
joinpoint/bind/guard failures and one default200000-heartbeat no-post reflexivity
failure are preserved. Exact actual condition/getV/pure/continue transitions fixed
that proof without budget increases; no sorry/admit/axiom/native shortcut.
Final JOINT command EXIT0: Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613; KeySort2jobs then ./run-lean.sh library1285/TestSuite262,
scoped30 signatures/standard axiom sets; core201/0elaborator,1300reachable/0orphan/
0notallowed, strict491automatic/61budgeted/0manual/11refuted/0pending, correct
complete-file-list trust1315sources/252sites/0findings and72tests. This validates
the exact private staged tree, not publication or a default-branch build. Prior
Returning combined EXIT1 and separate corrected trust pass remain their actual
outcomes. Historical docs/G03 EXIT1 exact-base equality is zero regression ONLY;
unchanged failing gates were not rerun. New links are checked separately.

Resources:225857536initialfree -178450432comparable layer -8388608conservative
incremental allowance =39018496projected remaining bytes. Before joint check,
222347264free with3510272actualincrementalbytes measured; no new dependency closure
or broad native output. Unchanged writer lock, serial-j1/LEAN_NUM_THREADS1, hard
12GiB/no-swap/CPU1 and12GiB OS-available reserve. Only current exited verified
SizeRw0 directory metadata was retired AFTER inspect/log/directory receipts;
images/caches/mounts/history/evidence protected. No resource stop, ENOSPC or guard
reduction. Exact final measurements/raw commands and all failures are sealed.

Work1/2/3 and BackfillA/B remain PARTIAL. All24 original full obligations and six
general combinations/fullProofGate stay pending: frontend derivation/admission,
general loops/raw operators/functions/sessions, Source try selector and ordinary
nonempty-revert producer, allocation/refinement/G01/compiler/world/V16/final joint
adequacy. The original immutable producer request remains unchanged at
`/workspace/vy5-composition/runtime-block-20261102/final/producer-request.json`.
No new VY4 packet is assumed. Original BLOCKED goal identity/status/objective/
counters unchanged; get_goal read support absent, no reset/reactivation/completion.
Reviewed incremental patch/bundles/exact source/signatures/evidence/checksums:
`/workspace/vy5-composition/for-loop-20261102/final/`.


### VY5 selected ordinary failure consumer (2026-11-02)

The immutable VY4 private checkpoint `5a4678a0733702d5b74abffce9c7c6a2c3e45c28`
resolves the selected ordinary nonempty-revert producer request. Its actual
GeneralFailure CALL/STATICCALL execution is now consumed by
`Solidity/Yul/Composition/FailurePhysical.lean`: actual extReturn/attempt,
allocRef/full readback, typed alias declaration/block/rethrow and caller-local
restoration. The 29 checked laws retain the entire 36-byte Denied(uint256)
selector/payload, Source state, saved fnLocals, raw dirty companion and both
residual/owned-byte journals. An inhabited caller has a nonempty four-observation
mixed prefix, saved heap aliases and persistent journal. Actual source refusal,
missing-code/static guards, entered-child timeout with dirty transferred state
and OLD returndata, and later consumer timeout are distinguished.

The real code registration, Fixed selectors, transfer/address/static/horizon,
shared execution/load and copy placement/ownership/bounds premises remain in the
signatures. The selected actual CALL reaches the completion used by the two-byte
payload copy; the subsequent catch rethrows the FULL buffer. This is a reachable
selected composition, not universal copy sequencing. Fresh logical catch heap
indices are not physical pointers. Represented-view retention does not establish
arbitrary initial representation validity. The prefix is supplied boundary data,
not a new emit/G01 theorem. Child rollback is distinct from the later catch heap
allocation; outer-frame rollback is not inferred. Raw values never resume through
runClean/ofClean. Known-payload decoding is not general Source try/error selection.

The independent frozen oracle checks 30 ordered actual Source cases in the two
Source pipeline contexts, two copy windows and full selected fields: bytes,
accounts/journals, heap/fnLocals, residual/owned bytes, raw/nonword aliases and
ordered observations. Decoder-boundary mutations are explicitly separate from
actual reached producer cases. There are ZERO fresh native comparisons. The
original native report retains four profiles/36 calls/five optimized-viaIR strict
journal mismatches and EXIT1, verified unchanged by hash only. Prior native
semantic replay is not claimed here. All prior expectations and holds remain.

Final joint EXIT0: Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613, actual KeySort2jobs before ./run-lean.sh library1292 and
TestSuite262; 202 core/0 elaborator,1307 reachable/0 orphan/0 not allowed;
strict491automatic/61budgeted/0manual/11refuted/0pending; complete-input trust
1322sources/252sites/0findings. All29 scoped signatures use only standard
propext/Classical.choice/Quot.sound axioms; 107 focused mutation tests pass.
Earlier failed diagnostics remain raw failures. Independent finder and skeptic
read-only reviews used no Lean/server/build. Historical docs/G03 EXIT1 remain
failures with exact-base zero-regression evidence, not global passes.

Resource admission retained the original writer lock, serial-j1/LEAN_NUM_THREADS1,
hard12GiB/no-swap and OS reserve. The measured dependency cache increment was
4993024bytes; the consumer conservative engineering allowance was10MiB, not a
guard change. Before final joint207527936bytes were free with7114752bytes of that
allowance remaining; after178450432 comparable container overhead the projected
remainder was21962752bytes. Only verified exited current-step SizeRw0 directory
metadata was retired after receipts; caches/images/mounts/evidence were retained.
No resource stop or guard reduction occurred. Full commands/resources/failures
and source provenance are in `/workspace/vy5-composition/failure-consumer-20261102/`.

Work1/2/3 and BackfillA/B remain PARTIAL; all24 ORIGINAL full obligations and six
general Source combinations/fullProofGate remain pending. Selected nonempty
producer input is resolved, but frontend/Yul admission, general Source try/error
selector, raw operators/function/session hooks, allocation/refinement/G01,
compiler/world/V16 and final adequacy remain open. LIB1, unchecked-add and strict
optimized-viaIR journal decisions remain unanswered. Original BLOCKED goal is
unchanged; no get_goal read tool is exposed and no goal mutation was attempted.
Sealed incremental artifacts: `/workspace/vy5-composition/failure-consumer-20261102/final/`.


### VY5 actual Source doWhile consumer (2026-11-02)

`Solidity/Yul/Composition/DoWhilePhysical.lean` adds20 actual Source constructor
and transport laws, not20 original full obligations. Existing typed alias/body
rethrow executes BEFORE an arbitrary condition: DEAD/empty/fullpanic propagate
at fuel+5 even when the condition is false or poison. Actual break and return
skip the condition; return remains ret. Continue reaches the real assignment
condition and changes a clean typed caller flag, while normal declaration
extends then restores the actual local scope before that assignment. Selected
literal-true/continue diverges at every horizon by induction. Low do fuel0..4
and assignment-continue fuel0..2 preserve the exact pending Source state.

Actual EM.sub/attempt transport retains the original outer evaluator locals,
complete Source.St, raw LocalValues/nonword aliases, fnLocals, heap, log prefix
and represented/residual/owned-byte journal companions. It returns changed clean
Out locals separately; raw values are never passed through runClean/ofClean.
An inhabited firstPhysical carrier plus actual allocated byte object supplies
DEAD/empty/panic and same-length AABB wrong-alias controls. Reference equality
and actual heap lookup are explicit generic premises, not desired execution
oracles. Companion retention is not a new rollback, representation-validity,
physical-placement/allocation-refinement or raw Source-resumption theorem.

Frozen BEFORE execution, the independent source-derived oracle defines50 ordered
Source cases under legacy/viaIR Source contexts. The actual driver matched all
selected fields: full bytes, flow/changed local indices, heap extent/contents,
fnLocals, raw dirty/function/nonword cells, outer scope, log prefix and physical
word/source/residual/owned journals. Positive and negative controls distinguish
body-first false condition, poison conditions skipped/reached, break then outer
rest versus revert suppressing it, timeout and dangling references.74 mutation
and provenance tests pass, rejecting stale module/driver/oracle/ledger/runner,
missing/reordered evidence, wrong full payload/scope/journals/high bits and
malformed raw execution receipts. No fresh native comparisons are claimed.

Final registered joint EXIT0: actual Lean4.24.0 commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b and Lake5.0.0-src+797c613;
KeySort2jobs precedes ./run-lean.sh library1293/TestSuite262.203core/0elaborator,
1308reachable/0orphan/0notallowed, strict491automatic/61budgeted/0manual/11refuted/
0pending; complete-input trust1323sources/252sites/0findings.20 complete scoped
signatures/axiom reports use standard propext/Classical.choice/Quot.sound only.
Initial diagnostic EXIT1 (implicit declaration type and wrongly qualified
sub_run) remains retained, separately from corrected passing diagnostics. MCP
shutdown RuntimeError after a successful result is retained as stderr, not a
Source proof failure or suppressed diagnostic. Separate finder/skeptic read-only
reviews run no Lean/server/build; final results and raw commands are sealed.

Resource preflight202248192bytesfree -178450432 comparable mounted container
layer -10485760 conservative COMPLETE incremental allowance leaves13312000bytes.
Before joint200540160bytesfree; after verified exited metadata retirement,
199491584bytesfree. The20-law olean is333200bytes; no new dependency closure,
image or broad native archive. Engineering allowance is not a changed guard.
Writer lock, serial-j1/LEAN_NUM_THREADS1, hard12GiB/no-swap/CPU1 and12GiB OS
reserve remained unchanged. Only current-step exited SizeRw0 directory metadata
was retired AFTER inspect/log/directory receipts. Protected caches/images/
mounts/history/evidence remain intact; no resource stop or ENOSPC occurred.

All Work1/2/3 and BackfillA/B remain PARTIAL. All24 ORIGINAL full obligations and
six general Source combinations/fullProofGate remain pending. This closes only
the selected actual Source doWhile child. The selected ordinary nonempty-revert
producer is already resolved and consumed by FailurePhysical; it is NOT listed
as missing again. Frontend/Yul admission, general raw/function/session/operator
hooks, Source try/error selector, allocation/refinement/G01/compiler/world/V16
and final adequacy remain open. LIB1, unchecked-add and original optimized-viaIR
strict-journal human holds remain unanswered. Original native report
`c0e8e6cd7f2f62865135b57ab395b3d256f3d0b474d20c17f88957e8d702f660`
retains four profiles/36calls/five failures(calls0,1,2,3,6)/EXIT1; hash preservation
only, not fresh replay. Historical docs/G03 EXIT1 and exact-base equality remain
failed global gates with zero new regressions. No unchanged failing global
command was rerun. Original BLOCKED goal unchanged; get_goal read tool remains
unavailable, no goal mutation. Incremental artifacts/signatures/evidence:
`/workspace/vy5-composition/do-while-20261102/final/`.


### VY5 actual modifier argument and postlude consumer (2026-11-02)

Inspection found the requested real single-placeholder branch already proved by
`ModifierPhysical.one_modifier`/`internal_revert`; it was not repeated as a new
milestone. `Solidity/Yul/Composition/ModifierPostPhysical.lean` instead adds the
missing selected bytes-parameter/alias-prefix/placeholder/rethrow-postlude leaf.
Actual evalConvArgs, dispatchMod/body lookup and parameter equality install the
function frame, execute the modifier and restore the arbitrary saved fnLocals
through attempt, including errors. A body revert skips the entire postlude even
when its argument is dangling. Actual normal OR return completion of the body
makes the placeholder normal, so the postlude really rethrows its own full byte
buffer. A real empty .nil modifier suppresses the body altogether. The prefix is
an actual local alias declaration; no heap allocation or hidden postlude omission
is assumed. Missing body, wrong parameters and low horizons are distinguished.

37 checked component facts include short actual placeholder-entry/timeout stages
and the original generic eight-horizon timeout law. Initial whole-list reduction
hit unchanged200000heartbeats; a later per-file45s partial result also remains a
failure. Both are retained. Factoring into direct typed execution stages checked
without budget increases, axioms/sorry/native shortcuts or weaker statements.
The new nonempty modifier-local placeholder transport does not change Source.

A constructive firstPhysical Source carrier retains complete Source.St, saved
boolean fnLocals, heap aliases, dirty raw/function/nonword LocalValues and real
Source/residual/owned-byte journal companions. Source outer evaluator scope is
restored through actual EM.sub/attempt. Complete retention is not new world
rollback, representation validity, physical placement or clean raw resumption.
The selected actual code has explicit reference/heap lookup/frame premises,
not a supplied desired execution. The supplied resolved runtime body contains
alias/postlude while its declaration syntax record identifies the placeholder;
no frontend Derived/admission claim is made. Pipeline uses rs=[] only, without
answering any return-slot/library/unchecked semantic hold.

Frozen BEFORE execution, the independent oracle matched48 ordered Source cases
under both actual Source pipeline contexts. Full error bytes, same-length AABB
versus DEAD, panic tail, empty failure, reachable/unreachable dangling references,
normal/return postludes, empty modifiers, missing/wrong frames and fuels0..7 are
checked. Every selected field is compared: input/returned local references,
heap extents/full objects, saved frame/outer scope, dirty raw words, log prefix,
ordered supplied credit1:9 then1:17, the whole Source journal entry LIST with
explicitly selected old account/c-path fields, current account/transient c-path,
and residual/owned journals/full physical word. These finite storage views do
not enumerate the infinite world; complete Source state equality is a separate
kernel law. Supplied credits/log prefix are not a new G01/log-emit theorem.

80 focused mutation/provenance tests pass, including equal-return wrong journal
owner/old nonce/storage/current/transient, high bits, aliases, prefix order and
missing/stale/malformed exact execution evidence. The reader binds the direct
ModifierPhysical body and transitive existing private producer closure as well
as new source/oracle/ledger/current runner. Initial readback-v1 EXIT1 from an
unused-variable warning before JSON remains raw. The variable was fixed instead
of filtering stdout; separate readback-v2 EXIT0 matched the UNCHANGED oracle.
There are ZERO fresh native/compiler/EVM comparisons.

Final registered joint EXIT0: actual Lean4.24.0 commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Lake5.0.0-src+797c613;
KeySort2jobs then ./run-lean.sh library1294/TestSuite262;204core/0elaborator,
1309reachable/0orphan/0notallowed; strict491automatic/61budgeted/0manual/11refuted/
0pending; complete-input trust1324sources/252sites/0findings.37 exact signatures
and scoped axiom reports use only propext/Classical.choice/Quot.sound. Separate
read-only finder/skeptic reviews found no findings and ran no Lean/server/build.
All earlier diagnostic exits, partial output and MCP shutdown stderr are kept.

Initial measured195403776bytesfree -178450432 comparable container layer
-10485760 complete conservative allowance =6467584projected bytes remaining.
Before joint190500864bytesfree; after verified metadata retirement189407232.
No new dependency closure or broad native runs. Existing hard12GiB/no-swap/CPU1,
serial-j1/LEAN_NUM_THREADS1,12GiBOSreserve/writerlock and all proof/test budgets
remain unchanged. Only current exited SizeRw0 directory metadata was retired
AFTER receipts; images/caches/mounts/history/evidence protected. No resource stop
or ENOSPC. The incremental seal references exact prior bundles and compresses
the full original patch rather than duplicating large historical data; no old
artifact is changed. Final capacity receipts state actual growth separately.

Work1/2/3 and BackfillA/B remain PARTIAL; all24 ORIGINAL obligations and six full
Source combinations/fullProofGate remain pending. Frontend/admission, general
modifiers/loops/functions/raw sessions/operators, Source try/error selector,
allocation/refinement/G01/compiler/world/V16/final adequacy remain open. The
specific ordinary nonempty-revert producer is already resolved and consumed,
not reopened as missing. LIB1, unchecked-add and optimized-viaIR strict-journal
holds remain unanswered. Original native SHA
`c0e8e6cd7f2f62865135b57ab395b3d256f3d0b474d20c17f88957e8d702f660`
retains all36calls/four profiles/five mismatches(calls0,1,2,3,6)/EXIT1; this turn
checks preservation hash only. Historical docs/G03 EXIT1 with exact-base-equal
findings remains failed global gates/zero regression only, not rerun for activity.
Original BLOCKED goal identity/status/objective/counters unchanged; no get_goal
read tool exposed and no goal mutation. Exact incremental source/signatures/
patch/bundles/raw evidence/checksums:
`/workspace/vy5-composition/modifier-post-20261102/final/`.


### VY5 H1 resource recovery and H3 per-pipeline traces (2026-11-02)

Human H1 **“Free disk + 4 GiB reserve”** resolves VY5-DISK1. Removed99 own
exited vy5-* containers after retaining inspect/exit/log/hash receipts; recovered
20808921088bytes (188014592→20996935680available). No active container, image,
mounted cache, evidence file or Git commit was removed. All prior sealed
handoffs remain. Both cgroup memory.reclaim and drop_caches are read-only here;
no bypass attempted, and MemAvailable after attempts exceeded17decimalGB (about16.6GiB). H1 changes
OS-available admission reserve to4GiB; hard12GiB memory/no-swap, CPU1, serial
-j1/LEAN_NUM_THREADS1, writer lock and every proof/fuel/gas/step budget remain.
Old resource receipts describe their actual old reserve; only new wrapper uses4.

Human H3 **“Per-pipeline”** resolves the optimized-rethrow-journal question for
this pinned finite fixture. BEFORE fresh execution, froze and independently
reviewed `tests/yul-composition/rethrow-trace-contract.json`. The original strict
native-rethrow-core/source/oracle/report remain byte-identical. A separate
versioned VY5 finite harness `pipeline-rethrow-core.mjs` reuses unchanged shared
compiler/EVM/capture APIs; it does not copy/rewrite the shared EVM engine. Diff
confines trace changes to exact per-profile persistent-write expectations:
legacy off/on and viaIR off require7/99/8, optimized viaIR requires7 only. Exact
transient17/51/34, rollback1/0, all full bytes/world/log/frame/memory/buffer checks
remain. This is an external compiler-aware diagnostic contract, not new source
observations or G01/compiler/refinement adequacy. Source/refusal semantics,
fixture sources, gas100000000 and step5000000 limits are unchanged.

Final fresh native-v2 EXIT0 runs actual pinned solc0.8.38 commit1835d247/Osaka
in all4profiles and all36ordered calls, with actual code/compile/input/source
hashes, runtime installation and full capture receipts.20 existing kernel-Source
failure/full-byte projections match and8 executed negative projections remain
mismatches. Native state is independently checked; the Source projection does
not equate different logical/physical worlds or native gas with Source fuel.
The first freshnative-v1 also passed; it is retained with its exact source
snapshot. Added direct-helper contract-hash protection after174passing tests,
then ran finalnative-v2 against that guarded final code, keeping the SAME frozen
contract. No unexpected mismatch was relabelled a pass. The original strict
original-v3 report retains its exactSHA
`c0e8e6cd7f2f62865135b57ab395b3d256f3d0b474d20c17f88957e8d702f660`,
original EXIT1 and five errors(calls0,1,2,3,6); unchanged regression tests assert
those failures. New H3 pass is a separate approved contract/version.

Final175tests pass, including exact optimized-only7, rejection of extra99/8 or
missing7, required stores in other profiles, transient/rollback/world/memory
corruption with equal bytes, missing/malformed/mislabelled profiles, stale
source/compiler/core/contract and exact receipt/report evidence. Existing
same-length payload/fullpanic/always-revert controls and all8negative projections
remain. Actual pinned runtime code hashes are identical to the original in all
four profiles. Independent read-only finder/skeptic accepted BEFORE execution
and reviewed final guards/tests/docs; neither used Lean/server/build/tests.

No Lean/import/state representation changed. Rechecked the unchanged private
kernel tree519dbb40fb5056b51350113419c1815c5bdb66e0 under new H1 resource policy:
actual Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b and
Lake5.0.0-src+797c613; KeySort2jobs, ./run-lean.sh library1294/TestSuite262,
204core/0elaborator,1309reachable/0orphan/0notallowed, strict491automatic/
61budgeted/0manual/11refuted/0pending, complete-input trust1324sources/252sites/
0findings; final combined EXIT0. This is unchanged-kernel regression evidence,
not a new Lean theorem or a kernel proof inferred from fresh EVM testing.
Historical docs/G03 EXIT1 and exact-base equality remain failed global gates/
zero new regressions, not rerun unchanged. New links are checked separately.

Work1/2/3 and BackfillA/B remain PARTIAL. All24 ORIGINAL obligations/six full
Source combinations/fullProofGate are pending. Remaining frontend/admission,
general raw operators/function/session/selection, allocation/refinement/G01,
compiler/world/V16/final composition facts remain mandatory. The selected
nonempty ordinary-function producer is already resolved. LIB1 and unchecked-add
holds remain unanswered; H1/H3 answer neither. Original goal identity/status/
objective/counters remain unchanged; get_goal read tool unavailable, no mutation.
New evidence/cleanup/immutable contract, source and incremental artifacts:
`/workspace/vy5-composition/pipeline-contract-20261102/final-v2/`.
