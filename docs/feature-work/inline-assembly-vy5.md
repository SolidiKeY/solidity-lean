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
