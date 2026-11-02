# V17 whole-pipeline validation preparation

Task: `solidity-v12-v17-20261031/v17-validation-release`.
Assigned base: `2fe1f8932f96be15b00df03ba2cde46f64a87758`.
Repository: `/workspace/solidity-lean`; branch:
`codex/solidity-v12-v17-20261031/v17-validation-release`.
The starting checkout was clean on `work`, exactly at the base. The assigned
branch was created there; no existing worker branch was fetched or integrated.

**Lane status: blocked, preparation only.** Core semantics, representations,
profiles, assertions, verdicts and proof budgets are unchanged. Later checkpoints
add above-core declaration extraction and authenticated fixture observations.
Every output retains `releaseClosed: false`. The original producer-only closure
mode checks supplied claims; separate checked-declaration consumers authenticate
narrow executions and retain exact types/axioms. Neither mode discharges semantic
coverage obligations merely from theorem names or dependency graphs.

## Queue and ownership

| Work item | State and precise remaining obligation |
|---|---|
| G52 | Partial preparation: a same-revision retained-report consumer checks the existing generated runner's four pipeline/optimizer settings, ten grammar families, deployment, ABI return/revert bytes, initial/final state, raw storage and rollback observations. It invokes the published generator and comparator; it never replaces either. Actual fresh same-revision execution is pending. Callbacks and wider combinations are unsupported by that published grammar and remain open, not excluded. |
| G53 | Partial preparation: snapshot/verify binds exact revision, corpus verdict table, SolKey pin, TestSuite report, runner inputs and actual Lean/Lake binary hashes/versions. Bounded read-only strict/parity probes retain discrepancies. Actual integrated re-pin/migration/strict correspondence and suite closure remain with their owners. No pin or Derived file is edited. |
| G54.01 | Pending: clean default/compiler/frontend proof targets with serial workers, actual resource measurements, and same-revision clean/cache provenance. The inherited cache is unverified, not a clean build. |
| G54.02 | Pending: same-revision full suite/corpus kernel closure, unchanged process budgets including the configured 300s automation bound. No whole-suite build has been claimed. |
| G54.03 | Pending until .01/.02 pass: scoped headline axiom checks, trust, joint public kernel imports, executable artifacts, clean/cache equivalence. Textual inventory and a trust probe are preparation only. No duplicate build/cache export. |
| G55 | Blocked: final independent evidence audit waits for actual integrated V11→V12→V13→V14→V15→V16 proofs and all G/S child gates. G03 currently supplies 118 work packages, 175 feature rows, 41 combinations, 98 symbol combinations and 25 decisions: 457 accounting requirements. None is silently marked discharged. |
| Backfill A | Implemented preparation: revision-bound nonempty log/checksum aggregation; corrupt/missing logs, false pass/exit labels, wrong revisions, duplicate records, mislabeled known commands and path escapes are rejected. Missing/failed gates remain incomplete. Full runtime/clean/cache provenance and combined release audit remain pending. |
| Backfill B | Implemented preparation: ledger-bound all-row inventory; explicit theorem kind, module, axiom list, observations and acyclic named premise accounting; lexical core public-import inventory reuses the existing repository script. Missing rows, wrong revisions, contradictory/parameterized-only claims, unmatched observations, cycles and unapproved axioms fail. Kernel extraction of exact theorem types/axioms and Bridge/joint import closure remain pending. |

Reserved prerequisites are read only: Source/admission (S00–S05), lowering
(G16–G23 and V07–V11), G24 foundation, storage/layout/hash, scalar,
environment, failure, creation, assembler/control, precompiles, stipend,
fixed point, existing EVM/Bridge workers, copy recovery, generated-differential
and SolKey re-pin/TestSuite repairs. Their component documents distinguish
local component theorems from missing parent composition. This lane makes no
replacement theorem, new final premise, or inferred preservation claim.
No scope decision is requested; integration is the coordinator's prerequisite.

Proposed ledger reconciliation: retain G52, G53, G54.01/.02/.03 and G55 open;
attach these preparation controls without changing any feature verdict.
The full 457-row pending accounting inventory is exported in the handoff.
Specific exercised observation anchors include `returnStatement`,
`revertBuiltin`, `requireBuiltin`, `assertBuiltin`, `tryStatement`,
`constructors`, `creationCode`, `runtimeCode`; tests add no coverage claim.

## Runtime and bounds

Read AGENTS, module map, documentation index, intrinsic Gate G0, parallelism,
contributing, local lean-verify, matching typing/derivation/soundness conventions,
G01 contracts, G03 ledger, G04 restrictions, G06 pin, G02 measurements, actual
scope/decision tables, and the reserved component documents before consumers.
The repository writer lock is
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`.

Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
Lake: 5.0.0-src+797c613 (Lean 4.24.0).
VM cgroup: 17,179,869,184 bytes; host swap: 0. Initial disk available: 30 GiB.
No Lean MCP is exposed by the attached tool inventory; no Lean file is edited.
No Lean server or concurrent heavy check is started.

The system/user systemd scope attempts fail (PID 1 is not systemd, user bus
absent). The supported Docker fallback was verified with Debian bookworm-slim
image digest `sha256:99c0b25c46d0214d5a2091092e7908907dcaecd6a962cde0ac700acee222b6f3`.
The actual child reports `memory.max=12884901888`, `memory.swap.max=0`.
One CPU, `LEAN_NUM_THREADS=1`, a temporary alternate TOML adding Lean `-j1`
without changing tracked lakefile settings, network disabled, writer lock held.
The temporary config was removed after the run. No proof budget increased.

Command: `lake -f roadmap-v17-runtime.lakefile.toml build Solidity.KeySort`.
Outcome: exit 0, `Build completed successfully (2 jobs).`
Cgroup peak: 25,579,520 bytes. This is a warm runtime/toolchain check only.
`RUNTIME_GATE_PASS` applies to that check; it says nothing about G54 closure.
Raw output: `/workspace/scratch/v17-evidence/keysort.log`. This earlier warm check ran at the assigned base before the first V17 commit, with untracked V17 scripts and unchanged Lean sources; the raw log has no embedded Git revision and is not attributed to a later head.

## Reproduction and evidence contracts

From a clean committed checkout with the actual Lean/Lake binaries on PATH:

```sh
python3 scripts/roadmap-v17-evidence.py snapshot
python3 scripts/roadmap-v17-evidence.py verify-snapshot --report /absolute/snapshot.json
python3 scripts/roadmap-v17-evidence.py inventory
python3 scripts/roadmap-v17-evidence.py aggregate --report /absolute/gates.json --evidence-root /absolute/logs
python3 scripts/roadmap-v17-evidence.py closure --report /absolute/closure-claims.json
python3 scripts/roadmap-v17-evidence.py differential --report /absolute/generated-report.json
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/roadmap-v17 -v
```

JSON duplicate keys are rejected. Gate records require schema/revision, stable
ID, argv command, exact exit/status, relative log path and SHA256. Closure
records require canonical ledger hash, exact lexical core import list, every
ledger-derived row, theorem names/modules/kinds/axioms/premises/observations.
A missing record never becomes a pass. Theorems are producer claims until actual
kernel gates and independent evidence audits verify them. No automatic path
from `accountingComplete` to release closure exists.

The differential consumer requires the exact current executable/input hashes,
regenerates the existing enumeration (60s published generator bound), and calls
the existing `compare` export. The thin adapter separately checks retained
observation schemas and compiler input/settings hashes; these are serialization
checks, not duplicate source/EVM semantics. Use a capped runtime to consume a
fresh report. Node dependencies come from the existing lockfile, installed
with `npm ci --ignore-scripts --no-audit --no-fund`; no dependency enters Lean.
The historical 640-agreement fixture is used only as an inhabited parser/
comparator test. Its revision is `016184b5564044d22d1d387dfb88d1209d8ea190`,
so it is rejected as present-revision evidence. The current `solcases` binary
is absent and the installed 0.8.34 compiler is not the pinned 0.8.38 witness.
Fresh differential execution is therefore pending; no wrong compiler is run.

`roadmap-v17-probe.py` acquires the repository writer lock internally and runs only existing read-only lightweight checks plus the
new lexical import inventory, serially, with a 60s host bound. It requires a
clean commit and a new external output directory, records external SolKey and
checker hashes, raw exits, elapsed time and sampled aggregate process-group RSS.
A nonzero probe remains a failure even when inherited. It does not invoke Lean,
repair a pin, or assert a full corpus/suite proof. Raw checker failures and an
explicitly separate exact-base docs no-new comparison are retained externally.

## Independent preparation reviews

Separate read-only finder and skeptic agents reviewed the actual files without
Lean/server/build/test calls. Confirmed findings and fixes:

- Observation presence alone admitted malformed or contradictory agreement:
  now check object shapes and reuse the published comparator; mutation controls
  corrupt ABI bytes, rollback words, initial observations, settings and nulls.
- Missing operation families and enumeration identity: require all ten families,
  every settings pair, exact generated enumeration and source/input hashes.
- Unclosed theorem inventory ignored by completeness: any unclosed theorem
  prevents complete accounting; regression includes an extra conditional entry.
- Missing import accounting: use the repository's exported import graph and
  check exact public lexical inventory plus every claimed theorem's module.
- Declared toolchain alone was insufficient: bind actual binary bytes/versions.
- A probe reporting a changed checkout could still be aggregated: explicitly reject it, hold the writer lock through all probes, and double-check snapshot cleanliness.
- Retained host metrics and exception consistency now have explicit checks.
- Known gate labels accepted arbitrary argv: check canonical command mappings;
  unregistered gate labels remain producer claims, documented as such.

The checkpoint includes no headline kernel theorem; theorem names/premises added:
none. Exact types and scoped axiom output for all final integrated headline
proofs remain an open G55 obligation. Synthetic acyclic premise controls and
historical external observations are never counted as those proofs.

## Preparation checkpoint handoff

The separate finder and skeptic re-reviewed the actual final preparation diff,
including hypotheses/non-vacuity, ownership and handoff; neither found a
remaining blocker to this preparation checkpoint. This is not G55's final
integrated review. All confirmed findings above were fixed.

Validation: 36 Python unit/control tests pass (including actual Node comparator
mutations). `git diff --cached --check` passes. The full docs path checker exits
1 with 46 findings, retained in `docs-head-initial.log`; an exact-base
source-only worktree reproduces the identical raw output in `docs-base.log`.
The separate byte-for-byte no-new-findings comparison passes. No Lean imports
were changed; per-file diagnostics are inapplicable. Heavy full, clean, suite,
corpus and Bridge checks remain pending, not waived by these controls.

## Read-only gate collection checkpoint

At committed preparation revision `f18f3815ea0c718dc06b5381149802596eb14c9f`,
the internally locked probe reports `unchangedCheckout: true`.
The first setup-copy probe fails because `/workspace/.setup/solkey.pin.json`
is absent; that raw failure is retained. Selecting the actual published
`tests/migration/solkey` snapshot resolves the input-path error without editing
or re-pinning anything. The new bounded run has these actual outcomes:

| Gate | Outcome and decisive evidence |
|---|---|
| Layers | Pass: 172 core modules, 0 reach the elaborator |
| Orphans | Pass: 996 reachable, 0 orphaned |
| Trust inventory | Pass: 1011 sources, 246 inventoried sites, 0 findings |
| Complete TestSuite inventory/parity | Pass: 564 functions = 552 derived + 11 refuted + 0 pending + 0 divergent + 1 excluded; 2 skip. No Lean is run by this check. |
| Strict automation inventory | Pass: 491 automatic, 61 with a step budget, 0 manual; 11 refuted; 0 pending |
| Existing sort-check executable | Pass: 377 taclets parsed, 131 read-bearing annotations, table covers 131. Binary and snapshot inputs hashed. This is not a clean rebuilt-executable gate. |
| Full documentation paths | **Fail**, 46 findings; separate exact-base no-new comparison passes |
| G03 generated inventory freshness | **Fail**, stale generated Markdown/JSON. Exact base reproduces identical failure. Reserved outputs remain untouched. |
| Lexical public-import inventory | Pass as textual preparation only; joint kernel/Bridge imports pending |
| Historical differential report | **Rejected**, exit 2: historical differential revision |

Raw logs and argv/exit/provenance/RSS records are in
`/workspace/scratch/v17-evidence/probes-frozen-f18f3815`; the earlier failed
setup-copy run remains in `probes-f18f3815`. Sampled peak aggregate probe RSS
is 270,479,360 bytes (trust scan). These are lightweight process-group samples,
not a heavy proof build bound. Outer cgroup observed peak after collection:
678,776,832 bytes. Disk remains 30 GiB available; evidence is under 1 MiB
before final exports. The temporary exact-base source worktree is task-owned,
155 MiB, with no copied build tree or cache.

The final export includes an exact-head snapshot, all 457 pending accounting
rows, failing aggregate output, raw gate logs, reviews, handoff, original patch,
git bundle and SHA256 manifest. Every runtime/gate result retains its actual
revision. Earlier preparation output is never relabeled as final integrated
proof evidence. No prerequisite branch is imported, pushed, merged or published.

Final missing prerequisites: actual integrated source/admission/lowering and
V11–V16 composition proofs; fresh supported differential combinations including
callbacks; final re-pin/corpus strict kernel closure; clean default/compiler/
frontend/suite/corpus/Bridge builds; theorem type/premise and scoped axiom
extraction; executable reproducibility and clean/cache equivalence; independent
all-child G55 evidence review. The lane cannot complete with these open.

The attached tool inventory exposes `stop_goal` but no `get_goal`; no second
goal was created and no completion transition is requested. The existing goal
must be blocked on the concrete integration/validation prerequisites above.

Second checkpoint finder/skeptic evidence reviews independently confirmed all
reported gate counts/statuses and raw-log checksums, append-only registration,
owned diff, exact-base failure equality and open proof boundaries. Both requested
precise revision attribution for the earlier warm KeySort log; the runtime
section now explicitly records its pre-commit base working state. No remaining
preparation blocker was reported. This is not an integrated G55 closure review.

## Auditor recovery: executable clean/cache provenance

Recovery continues the same VM, branch, goal and frozen base from clean head
`a219f1dbac901e1d12024131b985e50bd48e0295`. Prior artifacts in
`/workspace/scratch/v17-evidence` remain untouched. New evidence is retained in
`/workspace/scratch/v17-recovery`. No integration configuration exists and no
source branch is imported. All 457 rows and V11–V16 premises remain open.

The auditor identified a real accounting gap: a warm build log with a clean
label could previously satisfy a clean gate. The new owned
`scripts/roadmap-v17-provenance.py` collects and validates executable provenance.
Aggregation now requires that provenance for every non-pending clean/warm build
row; ordinary logs, missing attachments and mismatches cannot count as clean.
Snapshots explicitly bind the repository, committed tree, exact input hashes,
actual Lean/Lake executable paths/bytes/versions and deterministic serial
configuration hash, together with the existing source/toolchain key.

The collector holds the repository writer lock, requires a clean committed
checkout, inventories the actual build directory and one source/toolchain-keyed
cache at start/end, and never deletes or copies either. Clean collection refuses
an existing populated build or cache. Warm state cannot be relabeled clean.
Before/after source/tool snapshots and configuration bytes must agree. Exact
canonical build/cache paths, complete output maps, required target artifacts,
log checksums and same-target clean/warm continuity are checked. Attachments use
the same duplicate-key-rejecting parser as the primary evidence reader.

Actual execution uses the published `lake build` targets through a temporary
serial TOML and an exact checked execution script. Every Lean subprocess enters
a shared OS file lock and receives `-j1`; `LEAN_NUM_THREADS=1` is observed inside
the child. The child is network-disabled, one CPU, hard 12 GiB/no-swap capped,
and checks its actual cgroup limits. It records binary hashes/versions, cgroup
peak, sampled aggregate RSS/Lean worker count, available memory and disk.
The unchanged 300s bounded process ceiling is enforced both by the child timeout
and the host deadline; Docker RPCs and cleanup have bounded timeouts. This
conservative preparation bound does not replace the repository's final full
build policy or increase any process, proof or TestSuite module budget.

The toolchain is mounted read-only at a second path preserving Lean's library
layout; bytes are not duplicated or edited. Only the child overlay supplies the
serialization launcher. Configuration is removed even after execution/cleanup
failure. Raw Docker errors and after-snapshot failures remain structured
provenance failures. An unresolved task-container marker prevents another
collection until the previous container is confirmed stopped/removed, preserving
aggregate resource serialization after uncertain cleanup.

A scoped pair result identifies its target and always has `releaseClosed:false`.
It cannot satisfy the final `cache-equivalence` gate: aggregation explicitly
refuses that substitution. Actual G54.03 still waits for the requisite proof
leaves and complete same-revision target/artifact audit. These are producer
consistency controls, not an independently authenticated execution or kernel
proof engine. Kernel theorem/premise/axiom extraction remains pending.

Preparation invocation, from a clean committed checkout and the actual toolchain
on PATH (evidence output must be outside the checkout):

```sh
python3 scripts/roadmap-v17-provenance.py collect --gate generator-solcases --out /absolute/new-collection
python3 scripts/roadmap-v17-provenance.py validate --report /absolute/new-collection/provenance.json --evidence-root /absolute/new-collection
python3 scripts/roadmap-v17-provenance.py pair --report /absolute/pair.json --evidence-root /absolute/collections
```

The 66 controls include inhabited synthetic clean/warm pairs and rejection of
warm-as-clean, nonempty clean caches, missing provenance/gates, nonzero mandatory
gates, changed source/tool/input/config/budget, wrong cache roots, corrupt or
duplicate attachments, truncated/unmatched artifacts, missing cap/swap/metrics,
parallel/invalid worker counts, commented or appended execution commands, narrow
pair misuse, and unresolved-container overlap. Mocked execution controls cover
Docker timeout, cleanup failure and changed-source failure retention. They are
explicitly synthetic, not actual clean proof validation.

Separate independent read-only finder/skeptic reviews found and prompted fixes
for canonical paths, loader layout, Docker deadlines/lifecycle, cleanup/error
retention, exact inventory equality, strict JSON/worker schemas, exact execution
script bytes and unresolved-container overlap. Reviewers run no builds, tests or
Lean server. Final confirmation and any actual collection outcomes are retained
with their exact revision in the updated handoff.

For G52, the existing acquisition path in `docs/solidity-upstream-tests.md` was
inspected along with the published compiler table/runner and earlier failures.
The documented ethereum/solc-bin URL downloaded the exact approved
`soljson-v0.8.38+commit.1835d247.js` into the ignored `.lake/soljson` cache.
Its SHA256 is `6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`;
the published runner's `compiler()` accepts its full version and checksum.
No upgrade, re-pin, replacement generator, fixture/assertion change or callback
exclusion occurred. The next bounded actual operation is the published
`solcases` target; its outcome and any subsequent same-revision published runner
execution must remain separate from synthetic controls and all universal proofs.

The first actual collector smoke at `d64ec9c63aa4cfd8dee82b6c577e037ce71f97e8`
retained exit 125 before the build began: Docker rejected monitor output without
a PID column (`Couldn't find PID field in ps output`). Its raw structured
failure remains in `/workspace/scratch/v17-recovery/generator-build`. Container
and configuration cleanup completed. The monitor now requests PID/command/RSS,
with an added created→running→exited lifecycle regression. Retrying this changed
collector is not repeating an unchanged failed Lean operation. No build failure
was relabeled or erased.

## Preventive native-job serialization checkpoint

Continuation starts from clean `04a9fe8540bbfcff8db426f35d67fd29aceb0c55`
on the same assigned branch and VM. This is useful independent G54.01/backfill
preparation; G54.02/.03 and G55 remain closed to premature execution. Prior
artifacts, the approved compiler and the 640-comparison witness retain their
original revision and are not relabeled or needlessly rerun.

Inspection found the preceding admission wrapper covers Lean but not Lake's
C compilation, native linking and archive jobs. Process polling can observe
these jobs but cannot prevent short overlaps. The new schema-2 collector uses
child-only read-only overlays for the installed `lean`, `clang`, `llvm-ar`,
`ld.lld` and `leanc` entrypoints, sharing one inherited descriptor lock. The
original toolchain is mounted read-only at its alias with library layout intact;
no bytes are changed or copied into a second toolchain. Snapshots/cache keys now
also bind all five original tool binaries. Exact canonical Docker argv/mounts,
all canonical mounted-launcher paths/bytes and observed default-entrypoint hashes are validated, beside
raw-tool hashes, before/after source/configuration state and full inventories.

The approved spawn boundaries were inspected in Lake's installed
`Config/InstallPath` and `Build/Common`, plus the installed `Leanc` source.
`LEAN_CC` is deliberately not overridden: doing so would select custom-compiler
flags in Lake/Leanc and drop bundled internal flags. The overlays preserve the
existing native command arguments and only retain the already-required Lean
`-j1`. No tracked lakefile, core, source semantics, reserved repair, proof budget,
assertion, profile or verdict changes. The matching G02/history entries were
inspected. Serializing C/link jobs may slow a build; the 300s preparation process
ceiling and original suite-module budget are unchanged, and cannot be raised
through this harness. A failure or timeout will remain a failure.

The shell supervisor opens descriptor 9 on the absolute shared lock, acquires it
with the descriptor-only `flock -x 9` form, and holds it while the original tool
runs. An inherited family token is accepted only with the matching descriptor;
a stripped or forged descriptor fails closed rather than deadlocking or bypassing
admission. This serializes independent job families. Synchronous nested helpers
belong to the same family; it does not claim every nested OS process is globally
exclusive. All descendants remain in the hard 12 GiB/no-swap child scope and
one-CPU ceiling. Existing telemetry is observation evidence, not the admission
mechanism or a kernel proof. Unsupported execution patterns are not assumed safe
or counted as final proof closure.

Independent reviews caught an important initial defect: `flock -x 9 COMMAND`
locks a filename named `9`, rather than the descriptor. The initial same-directory
controls missed that. The new cross-directory control reproduced independent
family overlap (peak 2), retained in
`/workspace/scratch/v17-spawn/fd-form-failure.log`. The empty task-generated
untracked file was attributed and hashed in `stray-lock-file.json`, then removed
to restore the verified starting checkout state. No unexpected preexisting work
was removed. The corrected controls now check the intended lock inode and absence
of cwd files. Review also required binding actual Docker mount configuration and
observed wrapper bytes, so storing unused launchers cannot satisfy provenance.

The 82 controls include concurrent very short synthetic Lean/C/link/archive jobs,
an unwrapped overlapping negative control, cross-working-directory admission,
intended-inode blocking, inherited synchronous children, stripped/forged family
failure, native nonzero exits, killed waiters and owner-group timeout/recovery.
Synthetic tool-prefix/lock paths are substituted; no Lean proof or build is run
by these process controls. Existing provenance corruption controls remain in
force. Separate finder/skeptic re-review and any bounded real target outcomes
will be exported at `/workspace/scratch/v17-spawn`, without overwriting prior
`v17-evidence` or `v17-recovery` handoffs/checksums.

Default/compiler/frontend targets remain independently selectable through the
published `lake build` commands. Clean target collection still requires genuinely
empty observed build/cache state; this checkpoint neither deletes inherited
materializations nor labels a warm target clean. Actual final clean proof closure,
all 457 child/feature rows, V11–V16 premises, kernel extraction, full corpus/suite
closure and complete clean/cache equivalence remain open.

The actual warm compiler target at `94c20fda787687c79338965fe657b40425b04f7a`
completed 135 jobs in 296.48s under the unchanged 300s bound, with cgroup peak
979,652,608 bytes and sampled aggregate RSS peak 1,216,532,480 bytes. Before/after
snapshots agree. Its original comm-only sampler counted the waiting shell
supervisor and actual native Lean process as two workers, so its validator
correctly refused that recorded sample format. Build success and provenance
validation failure are retained separately in `v17-spawn/warm-compiler` and
`warm-compiler-validation.log`; neither the samples nor the old result is
rewritten or reclassified. No unchanged compiler retry is planned.

A small sampler correction now requests full-width PID/comm/RSS/args and counts
only the canonical native Lean executable. Waiting wrapper supervisors remain
explicit counts and their RSS stays included. Unknown Lean commands prevent
validation; they are never silently dropped. An explicit sample-format field
prevents the previous comm-only records being interpreted with new semantics.
The preventive family lock remains the admission mechanism. Focused controls
cover the original supervisor/native ambiguity, unknown processes and old-format
rejection. Any next actual check uses a distinct focused target and retains its
own source revision and outcome. This does not establish clean validation.

Sampler review also added strict expected-header validation: empty/headerless
telemetry is rejected rather than silently becoming a zero-process sample.
A genuine header-only result is retained explicitly as empty. This leaves the
current checkpoint at 87 synthetic/control tests, separate from actual target
proof results and all final lane gates.

The distinct warm frontend target at
`95e3e2ffdd7a2f7da1b55f9d66736e50157402ed` completed 35 jobs in 202.45s
(cgroup peak 877,391,872 bytes; sampled aggregate RSS peak 1,083,969,536 bytes).
Its unchanged before/after snapshots and all mounted wrapper hashes were recorded,
but two unclassified samples kept provenance validation rejected. The old samples
lack command/state detail; their cause is not inferred and they are not relabeled.
Both the successful build and separate failed validation remain raw evidence.

The next sampler version retains process state and full diagnostic context for
unknown Lean commands. Explicit zero-RSS zombies and the two exact descriptor-lock
transition commands are retained in separate counters rather than counted as
running Lean. Unknown running commands still fail validation. Header validation
and sample-format versioning remain strict. These are observable OS lifecycle
categories, not a claim that ps snapshots are atomic or prove serialization.
The preventive admission lock is unchanged. A small runtime/KeySort smoke may
check this changed measurement boundary; neither compiler nor frontend will be
rerun merely to replace their failed validation records. The checkpoint has
89 synthetic/control tests and all original lane obligations remain open.

### Live kernel declaration preparation

The owned `scripts/roadmap-v17-kernel.py` consumer and
`scripts/roadmap-v17-kernel-query.lean` template add a separate live extraction
path; the existing closure reports remain producer-only accounting. Collection
freshly compiles a narrowly requested published repository import closure into a
new evidence directory using isolated `LEAN_PATH`, then queries checked Lean
constants. It records structural names, full closed type/value expressions,
binders, proposition-valued binder indices, direct constant/projection references
and installed Lean's transitive axiom inventory. An independent `#print axioms`
query must agree. Display text is supplemental. Unsupported or oversized
expressions fail rather than truncate. Installed standard-library/Lean artifacts
are hashed inputs, not a reproduced standard-library build.

The optional claim consumer checks revision/tree/tool/input/query/configuration
and retained artifacts, then always repeats fresh compilation and extraction.
A supplied manifest or log alone is insufficient. Semantic premises are never
marked discharged, even when a conditional declaration and its hypotheses match.
This does not promote any closure row or execute the prerequisite-dependent final
G54.03/G55 gates. KeySort's published conditional and concrete declarations are
the intended bounded nontrivial witness; full release validation remains blocked.
Focused template diagnostics retain two raw failures followed by the corrected
passing check. Synthetic wire/claim controls cover duplicate/truncated output,
unsupported namespaces, declaration kinds, forged types/axioms/hypotheses and
conditional-only closure claims. Live results and independent review findings
will be recorded in the new checkpoint handoff; prior sealed evidence is retained.

Independent read-only finder and skeptic reviews identified the same acceptance
bug: a successful raw query could bypass collection-time provenance validation.
The correction retains `commandExit` separately and requires complete integrity
and runtime validation for both collection and replay. Both reviews also required
resource headroom guards and valid positive test baselines. The collector now
records/checks memory headroom and free disk space. Fourteen kernel preparation
control methods include passing binding/runtime/output baselines followed by
specific mutation failures; earlier invalid-baseline test runs are retained.
A first live preflight failed for missing Lean on PATH and remains failed. The
explicit installed-toolchain run freshly compiled KeySort and extracted four
published declarations successfully at its historical committed revision.
Final same-head extraction, replay, actual declaration refusal controls, full
control-suite output and independent evidence review belong to the external
checkpoint handoff, avoiding a post-validation source-tree change.

A further finder pass required preserving the actually observed command exit
before cleanup can alter supervisory status, and explicitly comparing old/live
replay revision, tree, configuration and installed import-input snapshots even
when declaration rows coincide. Both were corrected; dedicated replay mutation
controls cover a matching baseline and changed bindings. These are provenance
checks, not additional semantic proof assumptions.

Final skeptic review found that host `MemAvailable` alone overstates availability
inside this VM. The owned collector now records host availability and enclosing
cgroup limit/current usage separately, uses their minimum remaining capacity,
and requires the full 12 GiB execution cap plus 2 GiB OS reserve before launch.
Unsupported cgroup layouts fail closed. Earlier host-only records remain raw
historical evidence; the corrected runtime path requires a fresh bound run.

### Shared build resource and raw-exit repair

The build and kernel collectors now share the narrowly owned
`scripts/roadmap-v17-resources.py` helper. Both require finite, strictly typed
host/cgroup measurements, effective availability sufficient for the 12 GiB cap
plus 2 GiB OS reserve, and the supported namespace-root cgroup-v2 layout.
Malformed/unlimited measurements fail closed. Build disk and cache requirements,
serial admission wrappers, no-swap cap and 300s bounds remain unchanged.

New build provenance uses schema 3; old records are never migrated or relabeled.
It distinguishes actual container `commandExit` from Docker client `attachExit`,
execution supervision, cleanup and validation outcomes. Collection success requires
complete provenance validation and no phase errors. Nonzero raw commands remain
nonzero when cleanup also fails. Config cleanup/runtime observation failures retain
the observed raw exit in failed records. Schema-2 records are unsupported by this
new consumer, while their original raw bytes and historical failed verdicts remain
sealed evidence.

Separate read-only finder and skeptic reviews required actual container exit
inspection (rather than attach status), guarded config cleanup and malformed
runtime measurements, and contradiction rejection for success with phase errors.
These findings were corrected with positive-baseline and collector failure controls.
The new external checkpoint handoff records the final control count and justified
warm compiler/frontend attempts after reviewed commit and resource preflight.
Warm observations never establish clean-start or full cache equivalence. This
repair closes no semantic premise or any of the 457 still-open feature rows;
all original G52–G55 and backfill limitations remain binding.

### Producer accounting joined to checked declarations

`scripts/roadmap-v17-join.py` adds a separate consumer without changing the
existing producer-only `closure` mode. It joins exact declaration metadata to
producer accounting only after retained kernel records and attachments validate,
fresh bounded extraction replays, and source/tree/toolchain/import/query bindings
match. Canonical JSON comparison distinguishes booleans from integer metadata.
Retained records and attachments are rechecked after replay and before output.

Matching declarations do not establish semantic feature correspondence. All ledger
rows remain open; feature `done` claims and semantic-discharge/release promotion
flags are rejected. Each theorem retains conditional proposition binders, any
unaccounted indices, named producer premises and unverified observations. Each
feature row separately exposes unmatched and unverified producer observations.
Acknowledging a binder never discharges it. Definitions/contracts and external
tests cannot be relabeled unconditional compiler correctness theorems.

The source-only catalog preserves the complete G03 ledger and prepares bounded
requests for 14 published declarations across `Solidity.Roadmap.Contracts` and
`Solidity.Evm.Compiler`. Its excerpts retain `Compilation.correct`'s explicit
`result.Input` hypothesis and the memory/array/object/construction input and
representation adapters. G01 certificate/refinement transfer laws retain their
actual premises. No theorem-to-feature mapping or observation sufficiency is
invented; current checked evidence stays missing until validated live extraction.
A full fresh Compiler closure is deliberately not launched by this preparation.

Separate independent read-only finder/skeptic reviews found missing retained-input
rechecks, per-feature observation/promotion accounting, and Python bool/int equality
in metadata comparisons. These were corrected with positive-baseline and mutation
controls. Historical KeySort metadata is explicitly test data, not current proof.
Mocked collector tests now supply synthetic resource measurements independently
of VM pressure; production resource guards are unchanged. Actual source-bound
catalog/join runs, extraction admission or resource refusal, final reviews and all
original queue limitations are retained in the new external checkpoint handoff.

### Resource-refusal evidence recovery

The shared resource sampler now attaches only actual raw and parsed observations
to a refusal exception. Its finite-measurement parser and `check_headroom` policy
are unchanged. Kernel preflight failure records retain those available resource
observations, disk availability, exact cap/reserve/disk thresholds and comparison
results, including explicit unknown values for unavailable telemetry. They retain
preflight exit 2, null command exit and `launched=false`; missing telemetry never
becomes invented capacity. Independent read-only finder and skeptic reviews
accepted the repair and its starvation, malformed/unavailable telemetry, disk
failure and no-container/no-process controls (129 total controls).

Any task-owned clean-file page-cache advice and actual subsequent extraction/join
belong to the new external handoff. Prior refusals and sealed sets stay unchanged.
Read-only cache advice changes no disk artifact and cannot substitute for the
unchanged production guard passing. Actual positive declaration matches, if
obtained, still discharge no semantic premise or feature row; all original
G52–G55, Backfill A/B and missing integrated source/V11–V16 obligations remain.

### Published direct-memory internal calls

Published component `91e94ab57305ca055127934fd9e68fe9ea5e6be3` is consumed
using its first-parent patch only, preserving producer files byte-for-byte and
all V17 commits. This supplies the checked `Compilation.memoryCalls` branch,
expanded frame and reached allocation cost. It does not close source lowering,
recursive target calls, external byte transport, gas or any parent feature row.

The owned above-core memory-call query reuses published examples and their
inhabited endpoint/negative-frame proofs, without editing private producer values.
It discovers their checked constant identities in the exact published module.
The existing kernel metadata encoder is reused for checked type/value,
dependency and axiom observations. The changed Compiler.correct retains its
complete type and axiom set, but its value and value dependencies are explicitly
omitted after the unchanged 100,000-node serialization limit refused the full
body. The focused view is metadata-incomplete; the original full extractor stays
strict by default, and the original full Compiler9 value audit remains open.
Finite source alias/target observations and wrong-code/alias/frame controls are
kernel checked; executable observations are retained separately. Source/program
constant, intrinsic instruction representation and fixture/profile hashes remain
bound. These are intrinsic instruction observations, not bytecode adequacy.

The existing bounded provenance runner gains two explicit warm targets: the
published example build and the owned observation query. Query bytes are checked
against the canonical owned source. These warm current-source checks do not
weaken or replace the fresh Compiler extractor that timed out. A replay must
match exact code/output/alias/frame/allocation observations. The producer's
optional external reference uses solc0.8.34; V17's approved differential pin
remains0.8.38, with no substitution or dependency change. Actual gate outcomes,
reviews and all still-open G52–G55/Backfill obligations are in the new handoff.


Read-only finder/skeptic review required successful producer and query receipts,
exact build/cache/installed-input continuity, constructor no-value handling,
strict headline axiom output, and an actual live replay comparing the complete
verified wrapper. All were corrected with targeted controls. A real compiler
import exposed Solidity.Name shadowing; the above-core query now uses Lean.Name
explicitly. The inhabited compile-result equation checks after explicit unfolding
of the exact published witness, without raising heartbeat limits. The retained
failed diagnostic includes its rejected implicit recovery term; it is not a gate
pass. Current successful focused diagnostics contain no such recovery axiom.

Checksum bookkeeping now uses read-only direct IO where supported, with unchanged
SHA-256 results and stable-file checks; unsupported direct IO falls back to
ordinary reads and the actual resource guard still decides admission. This avoids
repopulating inactive artifact pages during inventories. The potentially slower
bookkeeping was announced and hashing history inspected; byte-equivalence, tail,
fallback and changed-input controls pass. No proof, expression or time budget,
cache bytes, source semantics or global status was changed by this IO repair.


The producer/query/replay receipts form a strict input/output chain. Mutable cache
input logs may change during a query, so a past producer receipt is checked for
internal consistency, then every actual imported project artifact must still
match the producer's output hash. The next operation's full build/cache start
must match its predecessor's end. The ordinary provenance validator and all
original gate/aggregation callers retain live-output checks by default; no CLI
option weakens them. Installed input manifests and full verified wrappers must
match across the live replay. This is not clean/cache equivalence. Changed cache
logs encountered by resource advice are retained as discrepancies and skipped;
no stale hash is used to authorize advice or proof evidence.


## Published creation-try consumer preparation

Published master `4165de133bafd522ab18099e18cad489bb1aa7d6` is incorporated into the isolated V17 branch, preserving all V17 commits and prior seals. The owned consumer [roadmap-v17-creation-try.py](../../scripts/roadmap-v17-creation-try.py) and above-core [query](../../scripts/roadmap-v17-creation-try-query.lean) reuse the bounded kernel extractor, authenticated warm build/query/replay receipts and the published native creation-try adapter. Original extraction defaults and all node/depth/process/resource budgets remain unchanged.

The sixteen requested declarations include full statements/values for the legacy ordered output, bounded-to-ordinary correspondence, ordinary execution, wrong reason refusal, collision, rollback/installation and argument facts, the separate viaIR output, their actual observation definitions, the published ABI `expected` definition and native `replay`. Expected byte lists are obtained from the checked producer equality statements; observations execute the actual published programs and replay. Pipeline/settings/AST/source-header identities and explicit accounts/funding are retained. The local unpacked original Solidity file is absent. Its actual 847 bytes are independently read from the existing published upstream archive and checked against its pinned manifest and both fixture source hashes, without unpacking any source tree. Header, archive, manifest, full AST and settings identities are retained separately.

This is fixture-level preparation only. Native source replay, intrinsic kernel witnesses and external solc/EVM/gas/CREATE address-model equivalence are distinct. No entire profile exclusion or feature match follows. All 457 ledger rows, original Source/V11–V16, strict/corpus/TestSuite, default/full/clean-cache and final trust/release obligations remain open. The historical Compiler9 timeout and `Compilation.correct` omitted full value remain limitations. The first bounded producer build passed (81 jobs, 172 seconds, measured peak 2,091,098,112 bytes); a focused above-core query passed with sixteen complete type/value/dependency records. All eight printed theorem axiom sets are exactly `Classical.choice`, `Quot.sound`, `propext`; these fixture theorems have no proposition binders. They prove concrete inhabited fixture facts, not universal compiler coverage. The first consumer rejected actual multiline axiom formatting; its raw failure is retained and the owned parser now accepts only complete, exact wrapped prints. Initial controls (148), subsequent source/archive/forgery controls (151 total) and all 15 published adapter controls passed. Both early independent read-only reviews found no source blocker. Final same-source authenticated receipts and final independent evidence/handoff review are exported separately in the new evidence set. Their actual exits, source snapshot and replay equality govern acceptance; neither these preliminary successes nor the diagnostic log substitutes for them. New evidence goes to `/workspace/scratch/v17-creation-try`; prior seals remain untouched.


Creation-try review controls explicitly distinguish parser consistency from authentication: synchronously changing every expected/actual byte list can remain internally consistent, but must fail exact comparison against the independently executed live replay wrapper. Changed account, collision, rollback, argument, pipeline/AST/source/revision metadata, missing declarations and stale producer/query chains also remain rejection cases. The shared warm receipt/import validation was extracted from the existing memory-call consumer without changing its defaults or liveness requirements. No full Compiler extraction was repeated. The diagnostic query is marked dirty-source-only and is never promoted to final same-revision evidence.


## Published direct/scoped memory-loop consumers

Published master `5f6a75b6038371a3917dbe08b660d5f2d1207c58` is incorporated on the isolated task branch. Both compiler arms and all previous V17 code/seals are preserved. [Loop consumer](../../scripts/roadmap-v17-loops.py) builds separate direct/scoped, sixteen-declaration queries using the existing kernel extractor and capped authenticated warm query/live replay machinery. Full statements/values/dependencies/axioms are required; missing or bounded-out declarations stay incomplete. No Compiler9/full Compilation.correct retry, omission or node-count relaxation is introduced.

Each family retains all four actual source evaluations and complete ordered target cells, stack77, sentinel99, certificate need and prefix budget. Arrays have source4 and target `[131,128,128,2,4,2,3,4,99]`; records retain legacy `[130,128,128,128,3,99]` versus viaIR `[130,0,5,128,3,99]` with source3. The differing local cells are intentional. Room/Cost and need remain the published loop relations, never the legacy finite allocationCost. Actual code and empty-code negative observations are retained. This abstract compiler/kernel component is distinct from pinned solc/EVM execution.

[Timing consumer](../../scripts/roadmap-v17-timing.py) requires the published complete24-module fresh original Derived17 workload and one cumulative300s bound. It reuses the unchanged published Python driver and JavaScript validator, requires successful same-head prerequisite/setup evidence and every fresh output/source/log/argv, and refuses warm subsets, stale modules, duplicates, reordering and per-stage budget substitutions. The already-installed Python runtime is mounted read-only with isolated no-site/no-bytecode flags, and its non-site runtime inputs are bound before/after; no package is installed or compiler pin changed. Native Lean work remains in the same aggregate12GiB/no-swap serial scope with the unchanged OS reserve.

Independent early reviews found a real post-Python-input failure logging bug: phaseErrors could disagree with its retained attachment. A shared post-input observer now preserves raw command/cleanup/validation outcomes and synchronizes the error attachment for unavailable or changed Python/Lean inputs; focused mocked controls cover raw0/124 and cleanup125. Initial158 controls pass after correcting an overly broad template-inspection assertion; subsequent controls and actual gates are exported separately. Both independent final reviews must inspect actual receipts, hypotheses, ordered observations and handoff. All457 rows and the original whole Work/Backfill queues remain open/partial. Earlier CreationTry128-byte/16-declaration wrappers remain immutable historical evidence.

The first cold combined loop producer target hit the unchanged300s supervisor deadline before source examples (raw command completion unknown, executionExit124, cleanup0). That receipt remains failed and is not rerun or relabeled. Separate focused direct/scoped module checks are independent warm preparation under the same bounds, not a substitute for that aggregate/cold or original clean/full gate. Both reviews also identified unbounded/escaping post-run Python version errors; the metadata probe now uses the existing10s metadata limit and shared recording catches CalledProcessError/TimeoutExpired while preserving raw outcomes. These fixes do not increase any Lean/process/test/proof budget.

The first admitted direct query exited1 with two owned adapter errors (unqualified Out selected the source type; EvalOrder has no DecidableEq). Its error-recovery output is rejected, never proof evidence. The query now qualifies Evm.Out and retains all three actual evaluation-order booleans rather than assuming an equality instance. Repeated imported-private-name scans are reduced by typed above-core aliases; this does not change requested original declarations, their full repeated-node encodings or any proof/node/time limit. The earlier source/version logging fixes and both review findings remain recorded.

At checkpoint feac427b, both loop families passed full authenticated declaration/observation collection and independent live replay: 32 records (30 values plus two value-less Cost inductives), eight concrete simulation theorems and two conditional input adapters with proposition binder7. All three compiler arm dependencies (memoryLoops, memoryLoopScopes, memoryCalls) remain in the extracted compiler entry. The original24-module fresh workload did not run: its root prerequisite and focused helper each hit300s with raw completion unknown, and23 setups remain absent. Those failures remain failures.

Final independent reviews found an additional gap in the unrun timing consumer: consumption-time hashes alone did not bind producer outputs. The collector now captures workload/fresh-output hashes immediately after the command and binds that manifest into provenance; validation rejects corruption, missing/extra files and changed reports before consumption, and the consumer reconciles the exact raw24 driver rows. This is a timing-accounting repair, not a new proof result. Loop evidence remains stamped at feac427b, not silently promoted to the later accounting-only source revision. No failed command is repeated to validate this repair; the actual fresh-workload obligation remains pending.


## Published fresh24 setup recovery

The published repair source `5b3446c835a362dbd12e40314849f763136df17d` and integration `22073f4445e7cab7560812a5ef4e081bf8ff5e87` are already ancestors of this branch and freshly fetched origin/master. All original24 workload source bytes match that publication. No new prerequisite merge is necessary. External146.63s/240.084s receipts establish availability, not this VM's gate.

The owned [setup preparer](../../scripts/roadmap-v17-setups.py) invokes actual installed Lake `setup-file` for every original member, building its imports and retaining exact stdout/setup bytes, dependency artifacts, source/tool/config identities and capped per-stage receipts. Its selected Lake binary directory is explicitly first in the child PATH alongside its paired Lean. This preparation is separate from the unchanged complete fresh24 driver and cumulative300s proof workload. Later setup restoration uses only captured actual Lake stdout; final inventories may differ from the last stage only in these24 exact setup bytes. No populated cache is removed or moved.

Independent read-only finder and skeptic found producer-supplied dependency/setup bindings and post-preparation inventories insufficiently checked. Validation now reconstructs canonical paths, raw digests and complete dependency bindings from authenticated Lake stdout and binds each setup to the stage build end; final cache must equal the last stage end. Contradictory preparation flags/sourceAfter/failures are rejected. A full24 synthetic bookkeeping baseline and corruption controls supplement actual bounded execution, never substitute for it. New receipts belong in `/workspace/scratch/v17-derived17`; all earlier seals remain untouched, including loop evidence at feac427b. All457 rows, Source/V11–V16, G52–G55 and both original backfills remain open/partial; preparation does not discharge semantic premises or release closure.


## Supplemental Derived17 structural accounting

The own original24 fresh workload passed at `1f3278e7ef97b68c2aa681e289e0b83b07e00396` in265.9041353959983s/300s, followed by ten scoped printed types/standard axiom sets and exact24 imported-object matches. Its3077-file sealed set remains immutable at `/workspace/scratch/v17-warm-prerequisites`. Host-footer EACCES, resource refusals and every earlier failed exit remain failures.

The new [fixed supplemental consumer](../../scripts/roadmap-v17-derived17.py) admits only those ten original Solkey names and their two checked defining modules. It leaves the generic Solidity-only request validator unchanged and reuses the complete KernelQuery extractor, all values included in one batch, unchanged100000-node/512-depth limits. Checked identity discovery alone is never structural metadata success. A bounded failure remains incomplete; no values are omitted and no mandated batch is silently split. Successful use requires independent live replay equality.

Actual setup-selected artifacts, all250 transitive project sources/objects and installed inputs are checked before/after against the sealed producer and current source/tool/settings. The new consumer revision is distinct from historical proof provenance; supplemental metadata is neither a current fresh/cold collector result nor finalG54.03. Template findOLean output is labeled search-path lookup, not the actual frontend import selector. The actual unchanged Lake setup map binds the imported objects.

Both independent read-only design reviews required fixed name/module/kind fences, complete row/import accounting, sealed producer identity, source/tool/query/object continuity and mandatory full replay; those requirements govern this consumer. Actual collection, controls and final reviews are recorded in the next handoff. Empty sequent hypotheses do not remove formula conditions: this<2^160, wt(storage), values.length==3 and original invariant/decreases clauses remain intact. All457 feature rows and remaining original Work/Backfill obligations stay OPEN/partial; no semantic premise or release closure follows.


The first full supplemental batch at consumer `f98dbbff1fffb7a3166343751f317c59c1261c64` returned real native exit1: `Solkey.TestSuite.invariantForCountsArrayLength.proved value: expression node limit reached`. Checked identity discovery and ten standard axiom prints were emitted, but no full metadata frame. All ten structural rows remain incomplete; the unchanged failed batch is not rerun, split, or converted into type-only success. The original kernel proof workload at1f3278e7 remains distinct. The remaining budget blocker is the exact reserved theorem value in `Solidity/TestSuite/Derived17.lean`; its owner would need to publish a same-statement proof representation satisfying the existing encoder budget, without new premises/axioms or limit changes. No reserved proof edit is assigned here.

Independent failure accounting validates the actual failed native receipt, committed historical query/script, all input bindings at a later accounting snapshot (not an invented immediate historical postcheck), exact checked name/module/kind catalog and actual axiom prints. Its pass means accounting succeeded, never structural metadata/replay success. Successful and failed future collections both retain post-command input checks; raw execution failure stays primary. Actual-input controls require this VM's immutable3077-file producer and cache.

## Approved hidden-cache readiness correction

The sealed structural checkpoint's workspace-only compiler scan was incomplete:
its file search omitted the ignored `.lake/soljson` directory. That report remains
unchanged. The approved `soljson-v0.8.38+commit.1835d247.js` is present there
(10,798,266 bytes, SHA256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`).
The new owned runtime consumer checks this explicit path with the published
checker, including its actual full version, and binds the complete installed
Node dependency tree, lock, executable, source, revision and toolchain before
and after execution. Internal runtime symlinks bind both target and link bytes.

The consumer invokes the original generated runner with all 160 ordered seed-0
records and all four original pipeline/settings variants, then authenticates
the complete generator replay and existing observation comparator under the
original 60-second/16-MiB replay bounds. Native stdout binds all output hashes;
missing, corrupt, stale, partial or failed evidence cannot become agreement.
The separate original capped collector still owns execution/resource evidence.
Independent finder/skeptic review identified missing matrix checks, overwrite
protection, producer-time report hashes and phase preservation; these were added
with negative controls before the actual attempt. This is bounded external
compiler/EVM evidence only. Callback combinations remain absent from the
published grammar, and no whole-profile G52 or kernel closure follows.

The earlier 640-agreement report at `04a9fe8540bbfcff8db426f35d67fd29aceb0c55`
remains historical. The structural query's actual node-limit failure on
`Solkey.TestSuite.invariantForCountsArrayLength.proved` remains unchanged; all
ten full metadata rows are incomplete, selected pin `473da894` differs from
historical `048a74de`, and all 457 closure rows and original G52–G55 obligations
remain open. Current command/resource/review outcomes are recorded in the new
external handoff rather than rewriting any sealed set.

The first new runtime attempt stopped before generation with Git/GLIBC exit 2.
The separate compatibility request uses only the existing host Git and matching
loader/libc/pcre/zlib, read-only and local to that Git process; the pinned image
and Node/EVM dependencies remain unchanged. Its next preflight also stopped
before generation: the new consumer incorrectly rejected the original collector's
serial temporary Lake configuration. The consumer now permits only that exact
untracked filename with bytes reproduced from the original serial configuration
rule, binds its hash before/after, and rejects all other checkout changes. Both
raw failures remain failures. This is a collector compatibility repair, not a
clean build claim or permission to ignore dirty source.

## Parallel committed-component interface checkpoint

The human authorized exact committed peer packages in private development trees.
The task branch remains isolated; no peer refs, sources or reserved implementations
are imported into this checkout. Four supplied bundles were checked against the
coordinator's SHA256 index and staged with exact advertised head/tree, frozen-base
ancestry, every committed blob/mode and trusted lexical import inventories:
V13 `66c08fdefbbb53c0eee111b09d1baa6277fedff5`, V14
`74225bbe317f0983ee0e781d446a2f97c1cb807f`, V15
`c97bcab75406cc4d22614948ef29d67b375dba3a`, and V16
`bea6e0e334f448aebb6f7c7a68321b4e419b43d2`.
These are development inputs, not master publication or lane completion.

`scripts/roadmap-v17-components.py` exports `stage(bundle, expected, destination)`
and `aggregate(plan, stages)`. Staging requires a new canonical private directory,
exact bundle identity and supported module roots; it uses private Git storage,
executes no producer command/hook/filter, rejects symlinks/submodules and validates
raw checked-out bytes. Git commands have 60-second bounds and staging has a
300-second post-run acceptance bound; use the documented outer `timeout 300`
command for a hard process deadline. Whole private source worktrees and build caches are never copied into
an evidence export. Private source worktrees are reusable, cache-free development inputs.
Bridge inventories remain separate; no Bridge import enters the core or public
registration, and the existing core extraction request fence is unchanged.

Aggregation emits results for each concrete component without waiting for entire
lanes. It revalidates private ancestry, source/import identities, exact scope and
decision-file fingerprints, ordered artifact contracts and transitive dependency
readiness. It reuses the original provenance and complete kernel validators and
replay matcher. Exact full-row metadata hashes bind type, value, dependency and
axiom requirements; source-only declaration requests never become checked proofs.
Missing or failed children, missing observations, changed source/tool/config,
conditional premises, stale/corrupt attachments and joint source conflicts remain
explicit. Clean/warm comparison reuses the owned original receipt checks; the
extracted pure `pair_consistency` helper alone never reports gate accounting
complete. These changes add no proof or process budget.

The actual new client is [ParallelInterface.lean](../../tests/roadmap-v17/ParallelInterface.lean).
It imports the exact private V16 `TransportControls`: `twoPass` and
`combination_success` supply composed-certificate success, while `idPass`, `idCert`
and `revert_at_need` supply the identity-certificate revert. The original G01/G07
`Outcome` and execution semantics are reused unchanged. Its complete ordered
result is `[some (.success [7]), some (.revert [9])]`; kernel negative controls
reject swapping, erased revert bytes and a missing component. This inhabited
instance emits no events and proves no real source/compiler/bytecode agreement.

The clarified private candidate is
`f7f9ad2d663b0fd3e98f93f05c85e0dfa395438d`, based directly on the supplied V16
head, with one owned fixture added. Complete fresh eight-module extraction and
independent live replay passed in 16.55s and 16.72s under the original 300s,
12GiB/no-swap, `-j1`, 100000-node/depth512 limits. All five declaration types,
values, dependencies and printed axiom sets were retained; every set is exactly
`[propext]`. Scoped expectations are in
[parallel-interface.json](../../tests/roadmap-v17/requests/parallel-interface.json).
The earlier `52d693bf21bb19a18a9b0df6878f49ac91d294f2` candidate and its passing
records remain historical and unchanged. A missing-schema request refusal,
resource refusals and a private-worktree configuration compatibility failure are
retained separately. No old failure is relabeled.

Independent finder/skeptic review identified and fixed transitive readiness,
strict ancestry/schema checks, unsafe private Git configuration, contradictory
metadata status and the composed-success/identity-revert wording. Focused tests
include real unrelated-commit and no-execution configuration controls, plus
synthetic bookkeeping controls that are never counted as kernel proof. Final
command, checksum and review evidence lives in the external PARALLEL-INTERFACE
handoff. The original Derived17 representation hold, false-readiness human-review
hold, all 457 OPEN rows and every G52–G55/backfill obligation remain binding.


The next owned interface is `collect_target(source, request, out)` (CLI `collect`).
It requires a clean committed consumer, matches all loaded project helper bytes
against that commit, and retains launch/post consumer and private-target snapshots.
It runs the unchanged complete kernel collector and fresh live replay for one
concrete core module, each under the original bound. A timeout prevents replay;
raw initial/replay exits, consumer validation and post-input failures stay distinct.
Same-tree HEAD movement, helper drift and dirty consumers are rejected. This does
not relax the core-only request namespace or supply a Bridge extraction shortcut.
V14 byte-prefix and V13 ABI-entry transport are separate newly ready leaf requests;
their actual per-component outcomes remain in the next external handoff. No
reserved ABI/decoder implementation or previous failed full target is retried.


Source verification now computes Git-blob SHA1 and SHA256 together through the
existing stable-stat direct-I/O path. The previous buffered source inventory
could rewarm a complete private tree immediately before resource admission. The
change preserves both actual-byte checks and the original hash_file API; an
unsupported filesystem still falls back to ordinary reads, and only the actual
unchanged headroom guard determines admission. Speed-related history
`6405ce0b` was inspected before this I/O change; no Lean checking is refactored.
Exact timing/resource observations and all earlier refusals are retained.


The V14 byte-prefix leaf's first complete extraction passed in 22.19s, retaining
four full conditional declaration records. Its mandatory replay and one
never-launched replay continuation refused the unchanged effective-memory guard;
raw command exits are null and no Lean query/build/container launched in those
refusals; Lean/Lake version probes occurred before admission. This component is
incomplete, not a replay pass. The original successful extraction was not repeated.
V13's ready 13-file leaf remains queued while the same guard cannot admit it.
Aggregation retains failed mandatory kernel/replay records as per-component
pending obligations, including raw phases and numeric preflight observations;
it does not promote a partial extraction or suppress unrelated ready components.
No further unchanged replay attempt is scheduled.


### Bounded private packet intake (2026-11-02)

The owned `scripts/roadmap-v17-packets.py` accepts a separately authenticated
schema-1 request containing `packetSha256`, a full `producerHead` claim and an
exact `members` path-to-SHA256 map. It reads without extracting or executing
packet files. Its CLI enforces 16 MiB compressed, 32 MiB raw, 512 MiB address
space and a 60-second alarm; it spawns no subprocesses. Strict member-set,
regular-file, path, header, termination, checksum and duplicate checks protect
intake. Producer commit membership, complete imports, theorem signatures,
axioms and replay are explicitly **not verified by intake**. These remain
separate obligations in the existing private component validation workflow.

Fresh measurements for both queued V14 replay and V13 ABI entry returned
NONPASS: effective 14,750,191,616 bytes versus required 15,032,385,536. No
container or Lean query launched. No memory policy or cache was changed.
The announced V11 reference packet was absent at its supplied RAM path in
this executor, and its abbreviated producer object was unavailable locally.
This is missing input, not a source or kernel pass. No actual V11 dependency
inventory or draft proof is inferred. V09/V11 reference and draft packets can
be admitted individually when exact bytes and required dependencies arrive;
whole-lane publication is not required for provisional private diagnostics.
All 457 rows and final release obligations remain open.

The checkpoint's independent read-only finder and skeptic reviews found and
resolved missing TAR end blocks after a zero payload, concatenated gzip streams,
scalar request handling and dot paths. Sixteen controls pass. Both reviewers
confirmed the corrected narrow byte-intake boundary without Lean or builds.
The raw documentation checker still exits 1 (48 findings versus frozen-base
46); two new findings concern reserved inline-assembly paths, zero concern V17.
The exact-base no-new gate therefore remains failed. Source layers, orphan and
properly invoked source-only trust checks pass; an initial trust invocation
without its required NUL file-list input failed and is retained separately.
No current runtime, kernel, cache-equivalence or release gate follows.


### Exact V11 reference dependency intake (2026-11-02)

The missing RAM path was a tool-surface difference: sandboxed `exec_command`
used mount namespace `4026532207`, while an authorized exact-environment read
used `4026532201` on the same host. The latter read all three announced files
and matched their independent SHA256 values. Earlier ENOENT receipts remain
true for their sandbox surface. A NEW external incoming directory retains the
original 14,145-byte archive, manifest, coordinator verification and the
surface-resolution receipt; no checkout/source/index was changed by relay.
The strict intake accepted all four exact members as **source bytes only**.

`scripts/roadmap-v17-packet-dependencies.py` adds executable interface/request
linkage and recursive lexical project-import accounting. It reuses the original
kernel header comment handling, keeps core/Bridge boundaries, bounds nodes,
edges, depth and aggregate bytes, and uses the existing local writer lock.
The metadata-only CLI retains the 512 MiB/60-second bounds. Missing source,
missing producer hash, source mismatch, cyclic imports, unsupported headers and
unused source assertions cannot become a complete inventory. Full producer
head/base are claims until an independent committed anchor is available.
A source-byte receipt presented as a kernel/replay request is rejected.
Installed toolchain imports remain separately unbound.

The actual C74 packet is producer `e11335bb3405fe44e9cfe83af960e732d21e76a2`,
original base `fb379ae20f10e2c92113453ddd9d40d8f2efbe09`; this does not alter
V17's frozen base. Its `Solidity.Backend.MemoryOps` decrement/underflow and
bump-pair declarations retain initial SourceUintFixedAt, local alignment,
bounds, arithmetic range, Source.MemOK and Objects.StateRepr premises. Pair
proofs also retain AllocatorRepr, positive base and actual caller nps. The
inhabited `SourceUintFixedDecrementControls.reached_pair` is reference source,
not newly checked here. The future two-decrement late-underflow draft is absent
and unvalidated.

Exact reconciliation against the main tree and existing V13/V14/V16 private
source inventories found matching `Solidity/Evm/Correct.lean` and
`Solidity/Source/SemanticsExamples.lean`. The three absent direct prerequisites
are `Solidity.Backend.MemoryOps.IntervalOverwrite`,
`Solidity.Backend.MemoryOps.SourceUintFixedDeclareAliasControls` and
`Solidity.Backend.MemoryOps.SourceUintFixedIncrement`; their exact required
hashes are retained in external `COORDINATOR-DEPENDENCIES.json`.
The matched sources import Evm.Stmt and Source.Semantics/Examples/Ledger; their
producer hash bindings were not supplied, so those four transitive bindings
are explicitly requested. No source hash or producer ancestry is invented.
No native/Lean/container job launched, and no V11 theorem is treated as checked.
V14 replay and V13 remain queued under the unchanged headroom refusal; Derived17
metadata, all457 rows and the complete original release queue remain open.

Source lookup is hash-addressed across supplied directories, not a claim that
Lean would resolve a combined overlay identically. Commit membership, actual
import-path resolution and compiled kernel/replay evidence remain pending.
The skeptic identified a contradictory producer-base claim; interface base,
root set and all supplied direct-import hashes are now cross-checked against
the actual authenticated interface, with wrong-base and partial-root controls.

Both independent read-only reviews confirmed the corrected identity bindings
and metadata-only boundary; neither reviewer used Lean/builds. Thirty-six
controls pass, including six actual-packet cases and the real intrinsic
KeySort source-byte baseline. Layers, orphans and source-only trust checks pass.
Raw docs remain exit 1 (48 current versus 46 frozen-base findings), with two
reserved inline-assembly additions and zero new V17 findings. An earlier draft
doc run's three missing-module path citations were corrected to module names;
its raw 51-finding failure is retained separately. No final gate is waived.
