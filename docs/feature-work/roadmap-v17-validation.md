# V17 whole-pipeline validation preparation

Task: `solidity-v12-v17-20261031/v17-validation-release`.
Assigned base: `2fe1f8932f96be15b00df03ba2cde46f64a87758`.
Repository: `/workspace/solidity-lean`; branch:
`codex/solidity-v12-v17-20261031/v17-validation-release`.
The starting checkout was clean on `work`, exactly at the base. The assigned
branch was created there; no existing worker branch was fetched or integrated.

**Lane status: blocked, preparation only.** No new Lean declaration, theorem,
axiom, representation, semantics, profile, assertion, verdict or proof budget
is changed. Every output deliberately retains `releaseClosed: false`.
Successful report accounting means consistency of supplied claims and retained
bytes. It cannot authenticate a producer, inspect a theorem's meaning, or prove
that a named premise was actually discharged in the kernel.

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
