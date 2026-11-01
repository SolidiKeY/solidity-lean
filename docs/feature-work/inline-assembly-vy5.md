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
