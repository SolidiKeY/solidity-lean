# H62 item 2: ABI-world empty-statement audit

Owner: `solidity-h62-2-20261106/audit-abi-world`. Frozen base:
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Assigned branch:
`codex/solidity-h62-2-20261106/audit-abi-world`.
Repository: `/workspace/solidity-lean`.

## Current status

The assignment is unfinished. Inventory, simultaneous witnesses and the independent
statement-fidelity census now cover all 177 frozen declarations across all 24
mapped modules. There are zero uncovered mapped statements. Of these, 54 have
proposition premises, 53 have data/type/instance binders only, and 70 have no input
binders. The 70 empty packages are explicit census accounting, not additional
semantic feasibility coverage. The success/runtime phase and matched after timings now also pass. Full normal
repository validation remains unfinished. The later coordinator instruction explicitly
reactivated this same worker and authorized merging origin/master and continuing.
The retirement section below is historical; no goal was created or reset.

| Checkpoint | Result |
|---|---|
| 1. Frozen signatures, ownership, premise classification | Complete source inventory; elaborated binders now also exported. |
| 2. Simultaneous hypotheses | 177 exact-type packages pass complete Lean diagnostics and reviews. |
| 3. Success/totality and behavioral controls | Seven formal theorems and ten provenance-bound external programs pass; proof/runtime boundary below. |
| 4. Witness and statement-fidelity census | 177 independent type comparisons pass; 439 binders, 113 proposition binders. Full final gate rerun remains required after checkpoint 3. |

The accounting tool explicitly reports `witness_gate_complete=true` and
`assignment_complete=false`. All original Solidity sources, generated roots,
central maps, axiom pins, producer interfaces and the frozen root Lake config are
unchanged. No theorem statement, premise, exclusion or observation was weakened.
There are no new axioms, unproved proof placeholders, native_decide shortcuts or
heartbeat increases. No mapped statement required a frozen repair or owner ticket.

## Inventory and ownership

`census.py` regenerates the exact frozen map and signatures from Git, including
section context, source/signature hashes and provenance. It includes unconditional
statements so a hypothesis heuristic cannot silently omit an interface. It is a
reviewed scanner for this frozen grammar, not a general Lean parser. `coverage.py`
requires exact equality with canonical regeneration of all 24 modules/177 rows.

The verified ownership snapshot identifies
`H30-WRITER-solidity-v12-v17-20261031--v13-abi-world`, owner
`solidity-v12-v17-20261031/v13-abi-world`, status `coordination-only`, covering
`Solidity/Backend/AbiWorld/**`. Snapshot SHA256:
`7f5d40d46d386ed17731db55ed87f0564f5c9e667bddee00c0f12b28772f9cce`.
Git authorship is recorded separately and is not ownership authority. No original
owned file was edited; the audit's exclusive additive scope was sufficient.

Four directory files are absent from the frozen map: `MutatingByteLoad.lean`,
`MutatingByteLoadControls.lean`, `TypedPacketMaterialize.lean`, and
`TypedPacketMaterializeControls.lean`, under `Solidity/Backend/AbiWorld/`.
The census reports this map drift explicitly. These files are not counted among
the 177 or declared audited. Their Producer premises are not attributed to the
mapped statements.

## Global premises versus fixed-input feasibility

Independent finder and skeptic traces found no direct global Producer,
Admission or compiler-correctness oracle premise among the mapped signatures.
Seven statements assume fixed-input representation structures:

| Frozen suffix under `Solidity.Backend.AbiWorld` | Structures |
|---|---|
| `CallerWordBytes.recovered` | WordFrame |
| `CallerWordBytes.typed` | StateRepr, WordFrame |
| `NativeParentWord.represented_counter` | StateRepr |
| `NativeParentWord.native_parent` | InterfaceV1.Entry |
| `MutatingEntryWords.represented_element` | StateRepr |
| `MutatingEntryWords.observed_activation` | StateRepr, StructAllocatorRepr |
| `MutatingWritePhysical.write_prefix` | StateRepr, WordFrame |

Definition evidence: `RuntimeFrameInterfaceV1.lean:28`,
`Evm/MemorySource.lean:26`, `PhysicalWordFrame.lean:23`,
`Evm/MemoryStructAlloc.lean:16`. StateRepr's nested payment-oracle compatibility
(`Evm/Sim.lean:225`) quantifies address/amount pairs for the same supplied
transaction and machine. It is jointly witnessed, not replaced by an isolated
inhabitant. CheckedAddArtifact's universal fit condition concerns references in
one artifact. Widths is bounded metadata (`L → Fin 33`); tag_bound also needs its
DecidableEq instance. Fits is three independent local inequalities. The remaining
170 signatures have data/type/instance inputs, local feasibility, or no binders.

## Additive proof modules

| Audit module under `H62AbiWorld` | Mapped witness count |
|---|---|
| CodecWitnesses | 19: ErrorLayout and ErrorRoundtrip. |
| WindowWitnesses | 27: Error/Panic windows, heterogeneous results and return words. |
| ControlWitnesses | 93: every mapped control declaration; 70 have no input binders. |
| BasicWitnesses | 29: packet prefixes, layout/assembly and remaining plain data cases. |
| RepresentationWitnesses | 9: actual call/frame/heap/byte fixtures, including all seven representation statements. |

WitnessSchema reads each unchanged theorem's elaborated type. It existentially
packages every leading forall binder in dependency order, including unused proof
binders, and replaces only the conclusion with True. The original theorem's proof
and conclusion do not establish feasibility. This checks one simultaneous input
for each statement, not total compiler success over all programs.

The schema has two public controls and two private fixture theorems: a feasible
shared input and rejection of incompatible premises on one input. The witness/schema modules contain 181 theorem declarations: 177 mapped
witnesses plus those four schema fixtures/controls. SuccessContracts adds seven,
for 188 new theorem declarations in total. Of the 177 witnesses, 157 report no axioms; the remaining 20 use
only combinations of propext, Classical.choice and Quot.sound. No new axiom was
introduced. The generic assembler packages choose concrete labels/items and
library type Empty without assuming an impossible Empty value.

Fidelity uses a separate direct recursion over Expr.forallE, rather than reusing
the schema's forallTelescope function. It preserves dependent domains, fails closed
on exhausted traversal fuel and checks definitional equality against the actual
witness type. Its 177 records export complete original and witness types and all
439 binders, including 113 proposition binders. Every original/witness pair occurs
exactly once. Definition unfolding inside arbitrary conclusions is deliberately
outside both leading-spine checks; the frozen statements were reviewed for this
boundary. No required premise is hidden or discarded in these 177 statements.

## Gates and reproducibility

Run from the repository root:

```sh
python3 -B scripts/h62/item2/audit-abi-world/test_census.py
python3 scripts/h62/item2/audit-abi-world/census.py --output /workspace/audit-abi-world-evidence/census.json
python3 -B scripts/h62/item2/audit-abi-world/coverage.py --evidence /workspace/audit-abi-world-evidence --require-complete
python3 -B scripts/h62/item2/audit-abi-world/test_coverage.py --evidence /workspace/audit-abi-world-evidence
python3 -B scripts/h62/item2/audit-abi-world/test_bounded.py --evidence /workspace/audit-abi-world-evidence
```

All pass at this milestone. Four scanner tests pass. Seven accounting rejection
controls reject shrunk census, stale schema, unapproved axiom report, wrong tool,
fidelity mismatch, stale guard and unbound proof output. Five lifecycle controls
exercise normal completion, orphan cleanup, timeout, cancellation and parallel
fake compiler rejection; they use no Lean. Deterministic regeneration of the
control/basic/fidelity modules and isolated TOML reproduces identical hashes.

Each of the six proof modules and Fidelity passes complete per-file MCP diagnostics:
success=true, partial=false, timed_out=false, no failed dependencies or errors.
The guard owns proof stdout and records its path/SHA256 after verified cleanup.
Accounting checks that exact proof/resource pair, file/source/support hashes,
expected Lean build, tool identity and full-file noninteractive arguments. Fidelity
also binds every local audit Lean source before and after checking. Only the three
standard axioms above are permitted by the accounting gate.

For a per-file check, substitute the module and evidence names:

```sh
python3 -B scripts/h62/item2/audit-abi-world/bounded.py --receipt /workspace/audit-abi-world-evidence/CodecWitnesses-resource.json --output /workspace/audit-abi-world-evidence/CodecWitnesses.json --timeout 180 -- .venv/bin/python -B scripts/h62/item2/audit-abi-world/mcp_call.py lean_diagnostic_messages '{"file_path":"tests/h62/item2/audit-abi-world/H62AbiWorld/CodecWitnesses.lean","interactive":false,"timeout_s":120}'
```

For Fidelity, use fidelity_call.py as the guarded command; it binds all local
Lean dependencies. Regeneration scripts and exact commands are in the handoff.
Adding/changing audit Lean sources requires refreshing Fidelity's dependency-bound
receipt before the coverage gate can pass again.

## Runtime and measurement boundaries

Actual Lean: 4.24.0, x86_64 Linux, Release, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`. Lake:
5.0.0-src+797c613. The official preinstalled binaries are under
`/workspace/.setup/tools/lean-4.24.0-linux/bin/`. Current bounded KeySort diagnostics
pass. The verified coordinator 4.35.0 archive pin remains in coordinator inputs;
the latest instruction scopes that requirement to migration lanes. This additive
audit does not migrate the frozen base or use a v4.24 per-master remote cache.

prepare_config.py reproduces the frozen target configuration in the audit's
isolated TOML, adding explicit --tstack=131072/-j1 to every library/executable and
only the audit test library. Original defaults/dependencies/target settings are
preserved. No central registration or generated-root edit was made.

The launcher holds the writer lock, rereads tracked changes, uses one open MCP
file and LEAN_NUM_THREADS=1, and enforces timeout/no active swap. Linux subreaping,
retained PID/start-time identity and pidfd signaling keep cleanup within the task's
own descendants. Catchable cancellation is recorded rather than raised during
spawn; finally cleanup handles survivors before accepting success.

The VM cgroup hard limit is 16 GiB. Virtual address reservations are not
capped; they are distinct from resident memory. The worker-added RLIMIT_AS ceiling
was removed after it produced a baseline PowerBounds std::bad_alloc at low RSS;
the unchanged batch then checked PowerBounds successfully in 153 seconds. Aggregate task
RSS ≤12 GiB and available memory ≥4 GiB are sampled every 0.2 seconds; those are
sampling checks, not an additional hard cgroup. The seven current checks observed
maximum task RSS 1501900800 bytes, minimum available memory 15264714752 bytes,
maximum one heavy Lean job, no active swap, and complete cleanup. No systemd-run
was called. An initial dependency check in the first checkpoint omitted explicit
-j1 and was excluded from accepted resource gates; current checks were rerun after
fixes. Occasional MCP event-loop shutdown warnings do not replace structured
results, command exits or source/output hashes.

The resident-policy matched timing pair passed: 1.236054186 → 1.226892517
seconds (−0.7412%), seven warm samples plus discarded warmup. That pair is retained
as timings-before-cache-advice-{before,after}; it does not measure the subsequent
cache-maintenance policy. Under the reviewed generated-cache policy, a new baseline
is 1.244709138 seconds; the corresponding after measurement remains pending.
Source/config/toolchain/guard/resource identities are bound by measure.py, which
fails above 10% slowdown. This is a warm per-file comparison, not a general speed claim.

The normal resident-policy full run stopped at target 787/5994 after 1640.762 s
when its strict 4 GiB reserve was crossed (minimum 4263129088 bytes). There were no
Lean errors in the log. After verified cleanup, read-only POSIX_FADV_DONTNEED on
clean generated .lake/build files reduced cgroup memory from 3.420 to 1.867 GB;
files and all limits were preserved. Both reviewers accepted this housekeeping.
The unchanged retry reached 5281/6117 without Lean errors, then stopped on the
same reserve after 7676.810 s (minimum 4284727296 bytes, peak task RSS 8759885824,
no swap, one heavy Lean job, complete cleanup). This is not a passing gate.

Cache_advice.py holds the writer lock, rejects live Lean/Lake jobs and symlinked
cache roots, uses read-only nofollow regular-file descriptors, and records advised
bytes/errors and before/after cgroup statistics. Advice does not guarantee eviction;
dirty pages are ignored. A second run advised 5.714 GB across 43459 files and observed
cgroup memory fall from 9.855 to 5.882 GB, with zero errors. A further unchanged
full retry will reuse completed artifacts. No global cache drop, budget increase,
source edit, swapped memory or reserve-accounting relaxation is used.
The current bounded KeySort diagnostics also pass under this resident policy.

H82 standing agreements supersede earlier exact-file agreement requirements for
statement-preserving edits. There are no pending owner requests or changed frozen
statements. Active work remains final validation; resource-stopped attempts are
retained, never counted as passes.

## Supported success and observable runtime boundaries

SuccessContracts defines an Option-valued ReturnContract: every independently
bounded packet and stack-safe machine must yield actual compiler output and exact
successful Slice execution. compileReturn satisfies it. A shared nonempty [0,255]
fixture refutes both reject-all and an actual emit-custom always-revert compiler.
Neither success nor compilation is assumed as a premise. Additional theorems prove
actual complete typed Panic-handler success for every bounded full-word code and
suffix, and retain zero-receiver failure. Checked-add assembly totality remains
explicitly structural; it does not claim branch execution from nonempty layout.

RuntimeVectors exports actual Backend.encode bytes. Six packet programs initialize
a nonzero stack tail and two sentinel bytes before the real emitter; four checked-
add artifacts use actual assembly with the 66-byte operand prefix relocation.
The external pinned EthereumJS interpreter checks:

| Program | Result | Exact gas including initialization |
|---|---|---:|
| return_two / return_suffix | success 00ff, stack tail 77 | 48 |
| return_word300 | complete 32-byte word, tail 77 | 321 |
| empty_revert | revert with empty data | 30 |
| panic300 | complete Panic(300) packet | 357 |
| error_two | complete Error byte payload | 939 |
| add_small / add_zero / add_max_no_overflow | success with exact sum stack | 42 |
| add_overflow | revert with Panic(17) | 373 |

Every case passes high gas, exactly measured required gas, one-below out-of-gas,
and zero-gas out-of-gas checks on fresh equivalent frame state. Packet sentinels
and stack tails are exact. The unreachable suffix consumes no gas/steps. Raw
Homestead REVERT is invalid opcode; Byzantium and Osaka revert with exact data.
Always-revert and always-STOP alternatives fail the positive return fixture.

These are isolated-frame external tests, not Lean gas/fork or whole-world bridge
proofs. High gas is a frame budget, not a transaction-cap assertion. Failure.Slice
continues to omit gas/world semantics. The formal contract covers the real bounded
packet-emitter program family, not a replacement H55/general compiler contract.

The interpreter uses repository-pinned evm10.1.3/common10.1.2/util10.1.2 outside
Git. Extraction reuses complete receipt validation and binds all local Lean imports.
Replay verifies source/support/diagnostic/resource/provenance hashes and compares
vectors directly with the checked #eval output before executing. Final acceptance
checks seven formal theorem axiom reports and all ten result/resource/code bindings.
Two additional mutation controls reject altered vectors and stale imported source.
Both independent reviewers accepted this chain and its proof/external boundaries.

## Reviews and handoff

Read-only census_finder and census_skeptic used neither Lean server nor builds.
Both accepted the exact 177 mappings, complete dependent packages, independent
fidelity traversal, final isolated configuration and seven proof/resource pairs.
They found and had fixed result-let signature truncation, owner attribution,
fail-open diagnostics, canonical-census/helper binding, axiom/receipt identity
checks, orphan/PID/cancellation cleanup, and proof/resource pairing. Current
negative controls exercise those rejection paths. No residual checkpoint finding
remains. The later component-success/runtime review is recorded above; full
normal validation and final review remain pending.

Bulk proof/census/fidelity/resource evidence stays outside Git under
`/workspace/audit-abi-world-evidence/`. The committed evidence manifest points at
an immutable witness-milestone snapshot under its checkpoints directory. Latest
original.patch, handoff.md and sha256-manifest.txt are exported at the evidence
root with the full committed head. Registration proposals remain task-owned.

This milestone hands off after five useful items: continuous resource enforcement,
93 control packages, 29 basic packages, nine joint representation packages, and
the independent fidelity/accounting gate. Resume this same VM/branch/base and
existing persistent goal. get_goal is not exposed, which the coordinator explicitly
made nonblocking. Do not reset/create a goal or launch a replacement.

Next: finish full ./run-lean.sh on the isolated branch, inspect actual final
sort-check output and resource evidence, run final read-only reviews, refresh the
final immutable manifest and export the exact head/patch/handoff. The first full
attempt was deliberately cancelled with verified cleanup to fix the provenance
finding; its completed cache artifacts are retained and it is not a passing gate.
No residual proof/runtime review finding remains. Do not merge, push, publish,
pre-gate or mark the persistent goal complete before full final validation passes.

## H82 stop-and-handoff (final worker state)

Human retirement overrides local continuation. Implementation and validation are
stopped. The active full retry was cancelled through its owned guard after
89.268 seconds; exit −15, reason cancelled, cleanup_complete=true, no swap,
maximum one heavy Lean job. This is not a passing gate. The prior full retry
reached 5281/6117 before its reserve stop. No source/proof failure was observed.

Handoff goes to `solidity-parallel-20261103/abi-entry`, which integrates the final
head. No scope takeover precedes this final stopped/head acknowledgement. No
push was made: H71 push permission is unavailable in this worker, while its
original instruction explicitly prohibits pushing. Original branch/VM/evidence
remain intact. No Claude-owned source was edited or message sent.

The goal tool catalogue exposes only stop_goal with outcomes complete/blocked.
There is no pause operation or PAUSED parameter. Consequently the existing goal
was neither completed nor falsely blocked, created or reset. PAUSED could not be
set through the exposed tools. This worker must not resume automatically.

Original assignment, complete original work/backfill queues and exact frozen
scope are committed under tests/h62/item2/audit-abi-world/handoff/. The full
thread-copy prompt hash is distinguished from the historical coordinator-only
goal-rendering hash; unavailable bytes are not claimed authenticated by that hash.
The exported cumulative patch/bundle contain those files, with SHA256SUMS.

Open obligations transferred: complete normal ./run-lean.sh plus final SolKey sort
output under unchanged bounds; cache-policy matched after timing (current before
1.244709138 s); final full-gate review/acceptance; coordinator registration and
integration of the supplied fragment. Inventory177, witnesses177, fidelity177,
seven success theorems, ten external programs, seven accounting negatives, two
provenance negatives, five guard controls and four scanner tests already pass.
Scanner/fixture/reproduction backfill is implemented; no additional candidate
was assigned. No theorem repair ticket or vacuity escalation is outstanding.
Full validation/resource wait is retained; retirement prevents further local work.
No RUNTIME_GATE_PASS or full-assignment completion is claimed.

## Reactivated post-merge validation (2026-11-06)

The coordinator reported audit head e55d46407e merged into master20e492ee9 with
touched gate/Bridge build/reviews passing, and explicitly instructed this worker
to merge origin/master and continue. Fetch verified originalbase, e55d46407 and
20e492ee9 ancestors of d96f2406d352de7e0b72ba6ac4ab29dc457582c6. The clean assigned
branch fast-forwarded to d96; no local work was discarded, and no push was made.
Existing goal get/resume operations are not exposed; no replacement/reset goal
was created. User reactivation authorizes the remaining original work.

All24 mapped source files and the frozen module map remain byte-identical to
c6f550e. Other upstream files/config changed. Frozen proof/runtime receipts and
retirement exports remain preserved. New resume tooling produces separately
labelled integration-tree receipts, never relabels old records or weakens their
checks. A separate deterministic TOML preserves current root target metadata and
defaults while adding explicit stack131072/-j1 on every target and the auditlib.
The current upstream policy removed solkeycheck from default targets/gates; this
worker retains the explicitly required KeySort diagnostic prerequisite and uses
the current unchanged ./run-lean.sh for full confirmation.

Resume sources are pinned to all7592 canonical integration Lean paths (including
generated roots/vendor), exact current path set and SHA256 bytes before/after.
Unexpected sources, changed upstream inputs or changed frozen map/files fail
closed. Support binds driver/helper/config/scanner bytes and all9 local Lean
files before/after. The original evidence manifest is read from integration Git
bytes before reusing archived external fixture hashes. It stays untouched; new
evidence uses a separate resume-evidence.sha256 manifest.

All9 audit modules and KeySort passed fresh complete MCP diagnostics, bound
output/resource/source checks, exit0 and verified cleanup. Acceptance confirms
177 unique fidelity rows,439 binders, seven success theorems and exactly10
encoded fixtures identical to the authenticated archived external-test inputs.
This reuses those external observations for identical code, and claims neither
a new EVM run nor a Lean gas/fork/general compiler bridge proof. No Lean source,
frozen statement, axiom, exclusion or proof budget changed.

Actual tools remain Lean4.24.0 Release797c613eb9b6d4ec95db23e3e00af9ac6657f24b
and Lake5.0.0-src+797c613. Existing16GiBhardVM/12GiBtaskRSS/4GiBreserve/noSwap/
oneheavyjob/-j1 resource policy is unchanged. Under identical documented cache
conditioning, the seven-sample warm before/after medians are1.527788517s and
1.541366676s (+0.888746%, within10%). This comparison uses the new integration
identity and is not compared to the earlier frozen-tree baseline.

Both independent reviewers found and had fixed before-only imported-source
checking/untracked omission and unpinned archive-manifest authority. They then
accepted fresh9+KeySort receipts, complete177/439/7/10 accounting, resource limits
and timing. Three post-merge receipt controls pass (validchain, replaced archive
authority rejected, forged upstream digest with rebound outer hash rejected);
all four scanner tests pass. Neither reviewer used Lean/server/builds or edited.

Remaining: complete current normal full ./run-lean.sh under these bounds, record
its actual outcome, obtain final read-only review and export the exact committed
head/evidence. The coordinator's reported touched/Bridge passes are reported
evidence, not a substitute for an unrun local full gate. No RUNTIME_GATE_PASS or
full assignment completion is claimed at this checkpoint.

### Full-gate resource recovery on the integration tree

First current full attempt stopped at375/6053 after335.149s when its strict
4GiB reserve was crossed (minimum4273532928bytes); noLeanerrors,cleanuptrue,
noSwap,oneheavyjob. PowerBounds passed170s. Generated-build advice reclaimed
only90MB; retry stopped at the same dependency after21.358s, not a passing gate.

The installed Lake uses /home/agent/.cache/lake/artifacts, a separate local
cache (not a downloaded per-master cache). It held16010 regular artifacts,
5.308GB. A new additive cache_artifact_advice.py uses the same writer lock,
rejects liveLean/Lake and symlinked roots, anchors traversal with directoryFDs,
opens nofollow/nonblocking/read-only, and advises current-UID regular files only.
It writes/removes no artifacts, changes no budget or reserve accounting, and
uses no network/globalcache drop. Both independent reviewers accepted it after
requiring the nonblocking-open safeguard. No source/proof edits were made.

Its first run advised5.308GB with zero errors/skips and observed cgroup current
fall from5991899136 to500625408bytes. Advice is not guaranteed eviction. The
previous timing pair remains valid only for its documented generated-build-cache
conditioning; this artifact advice is separate full-gate memory housekeeping.
The unchanged full gate will resume using retained completed artifacts and the
same16hard/12RSS/4reserve/noSwap/onejob policy. Both failed attempts are retained.

## Second authorized master update and portable evidence

The coordinator reported ac9d8db2a merged our reviewed head and requested another
fetch/continue, with a minor on VM-only artifact pins. At the next safe resource
checkpoint, origin/master was706e36825929d6d0084dc08b88de9349abcd25aa; originalbase,
ac9d and8354a254 ancestry verified, clean assignedbranch fast-forwarded. New
upstream changes affect445 validation inputs, but all24 frozen ABI files/map
remain byte-identical. No own Lean statement/proof/budget change was made.

Old d96 receipts and failed full attempts are preserved separately. New input
pinning covers7713 Lean files at706. All9 local modules+KeySort pass fresh full
MCP checks; acceptance177/439/7/10, three adversarial/valid controls pass. New
matched medians1.581863012→1.548157993s (−2.130717%, within10%) under identical
recorded generated+artifact-cache conditioning. This replaces neither earlier
comparison nor the outstanding full gate.

Original frozen evidence.sha256 stays unchanged as Git-pinned legacy authority.
New resume-evidence.sha256 and portable-evidence.sha256 use paths relative to the
unpacked evidence root. portable-evidence-index.json commits the actual archive
SHA and verification command. H44 bulk remains in the supplied archive off Git.
portable_evidence.py pack deterministically creates the archive+relative manifest;
verify streams all members, rejects unsafe/nonregular/duplicate/unexpected/missing
entries or changed bytes, and requires neither Lean nor the original VM paths.
Four controls pass. This verifies byte integrity, not theorem truth. Actual VM
paths inside diagnostic records remain historical execution provenance.

Legacy fixture lookup can use --frozen-evidence at a relocated archive path; its
hashes still come from the unique original retirement-final manifest entries in
the integration Git object, never an editable replacement authority. Both
reviewers accepted this design and current accounting. No scope questions.

The d96 full run reached all library/examples and TestSuite.Derived20 before a
reserve stop at2088.577s, peak taskRSS9174859776bytes, noLeanerrors, noSwap,
oneheavyjob, cleanuptrue. OpenLoops passed unchanged. The new706 full gate remains
to run with retained artifacts; no failed attempt is counted as a pass.
