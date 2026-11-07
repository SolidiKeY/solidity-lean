# H127 serial slow-example runner: pre-use contract

Status: design and source-plan preparation, **not an executable measurement
runner or acceptance result**. The exact module-times intake at b3fb97985860dc154e377a959f6c1d9778be8cf9
has now arrived in the hash-pinned coordinator archive. It includes both
rejected drafts, their findings, latest result/waits and scope-binding scripts.
The drafts are historical inputs and are not executed. The older H82 handoff
is superseded for intake. H127 transfers this runner, not the whole H55–H58 lane.

H109 already has a non-default SoliditySlowExamples library containing fifteen
modules: DecisionGaps and its eleven example importers, OpenLoops, its explicit
RowsNine child and RevertData. Roots are regenerated from the source list;
existing theorem statements stay unchanged. Every module is
re-elaborated serially; cache admission or a cached root build cannot replace
these checks. CI and lane-end/full validation keep the slow root. Ordinary
checkpoint selection keeps its current exclusion. The delivered H116 intake
originally limited the 600-second CI calibration to cumulative Derived17 replay.
The later explicit H134 decision extends 600 seconds to the entire H109 slow
library in CI, including RowsNine. VM/local/default checks retain 300 seconds
and the existing 594-second default-path STOP. The slow-library CI deadline is
not multiplied by its fifteen members. Non-slow budgets and proof heartbeats
remain unchanged. No unchanged stopped timing workload is authorized here.

## Execution and trust boundary

The implementation must have separate controller, container worker and offline
receipt verifier. A plan cannot execute arbitrary argv. The only execution
recipe is the repository per-file gate with reviewed serial enforcement and
`LEAN_NUM_THREADS=1`/Lean `-j1`, followed by the slow-library/root and existing
required audit checks. Inspect the gate's current timeout before integration:
keep the existing300second default/VM module maximum and the explicit H109
slow-CI600 allowance; do not generalize the unrelated Derived17 calibration.
The actual pinned Lake5.0.0 help has no global-j1 option: a setup attempt with
that option failed before diagnostics. Lean-thread flags alone do not establish
Lake job serialism; the production runner must enforce external compiler
serialization or an otherwise proven serial fixed recipe.
Dependency preparation is a separately timed stage, never part of a fake
cached-verdict pass. Direct re-elaboration of each selected file is required.

The controller owns the global writer lock through snapshot preparation,
checks, verification and cleanup. It requires an explicitly authenticated
commit, clean tracked sources and complete regular-file source inventory.
prepare-plan.py binds bytes to Git blobs/tree and SHA256 without executing
anything. Unknown entries, target drift, source changes and unsupported root
syntax fail closed. The worker receives a sealed read-only source snapshot;
untracked and ignored source files cannot enter through the live checkout.
The raw Git materialization helper is available; production capacity enforcement
and read-only snapshot mount verification remain incomplete.
The snapshot must include isolated Git metadata because per-file gate.sh invokes
Git. Construct it from a pinned sealed bundle into a private clone, never by
pointing at live .git or a shared worktree common directory. Disable system and
global Git config, external hooks/filters and alternates; verify the exact
commit/tree and complete materialized snapshot. Mount that private Git metadata
read-only with the source. The preparer's descriptor-relative no-follow regular
file reads reject symlink ancestors/FIFOs/devices and bound reads by blob size;
this is still a non-atomic live observation, not a substitute for snapshot proof.

input-inventory.py supplies a full-tree content/metadata observation primitive
for source/cache/toolchain/package roots. It records xattrs, modes, ownership,
mtime and content, with device/inode/ctime separately. It refuses special files
and escaping/dangling links; atime and physical/page-cache equality are not
claimed. Verification CLI requires an external exact receipt SHA256. This is
not yet immutable snapshot creation, atomic observation, a copy-provenance
proof or a production runner: those obligations remain open.

Pin every Lake dependency/package tree and lake-manifest.json, including ignored
.lake/packages inputs, with exact source and resolved package identities. Reject
unlisted dependencies or packages not present in the sealed input inventory;
no network resolution during checking. Construct a minimal pinned environment rather than inherit LEAN_PATH, Lake or
Git configuration from the caller. Pin the Docker image by immutable digest, full Lean toolchain tree (binaries,
libraries and headers), version output/commit, Lake config, scripts and input
cache tree. Keep toolchain/source mounts read-only. Use a private cache with
recorded initial/final content and metadata; changed artifacts are outputs,
not evidence of unchanged initial state. Do not share a writable cache between
measurement arms or retain an unexplained cache hit as proof of checking.
Preparation also obeys the four-GiB headroom rule. No cache restoration is
called authenticated merely because the archive has a hash.

Use one container/module at a time with no Docker socket inside, no network,
no extra capabilities, a read-only filesystem and explicit writable output/
cache mounts. Worker limits remain 12 GiB, no swap, one CPU; no host H81 cap
increase flows into this VM. Verify actual cgroup-v2 memory.max,
memory.swap.max and cpu.max inside and via the host PID/cgroup mapping.
Record namespace identifiers, boot ID, Docker image/ID/mounts and parent limits.
Docker's declared flags alone are not kernel resource evidence. Reject an
unsupported/ambiguous cgroup layout. Sampling cannot prove the absence of a
short-lived competing Lean process: serial invocation follows from the fixed
trusted recipe and `-j1`; kernel/process observations are corroboration only.

## Lifecycle and measurement

States are prepared, created, kernel-verified, running, stopped, drained and
sealed. Only a drained, verified zero-exit module within its existing 300-second measurement budget is a pass.
Every failure records its stage; missing data is unknown/fail, never zero time.

Reserve an unguessable run name and ownership label before container creation.
Persist the intended identity before Docker starts; interrupted create still
has a known name to reconcile. Verify ownership before destructive cleanup.
Install signal handling before create. Timeout, exception, signal, output I/O
failure, OOM or reserve breach initiates whole-container kill/removal, including
setsid/double-fork descendants. Waiting for the launcher or killing its process
group is insufficient. Confirm the owned cgroup is empty/removed and reconcile
the Docker identity before declaring cleanup complete. Failure to establish
cleanup is a failed run that blocks the next module. The 300-second measurement
deadline stops new work and triggers termination; cleanup continues beyond it
until emptiness is established, but all excess time is recorded and cannot be
counted as a passing run or a renewed deadline. A separate cleanup watchdog
reports unresolved cleanup and prevents any subsequent worker; it never turns
a timeout into success. Cleanup must not delete
pre-existing or foreign containers. Never start a second worker speculatively.

Use monotonic_ns plus CLOCK_BOOTTIME for sub-second elapsed measurement and
detect disagreement/suspension. Start timing before the measured command;
enforce the 300-second module-measurement deadline independently of exits.
Each dependency preparation/check invocation has its own identified stage;
separate stage times may not be combined into a fictitious within-budget check.
VM/default invocations retain the 300-second policy. H134 permits 600 seconds
for the whole H109 slow-library CI invocation; Derived17 retains its separate
H116 cumulative CI600/local300 policy. Context and workload denominator must be
authenticated; neither allowance grants another module or this VM 600 seconds.
Source/toolchain preparation is recorded separately and runs no Lean. Report
setup, dependency preparation, check and cleanup separately. Record exact command,
exit/signal, compiler provenance, per-file logs and hashes; post-verify source,
toolchain and input identities before sealing an exclusive new output path.
Advance to the next module only after the current receipt is sealed.

Read kernel cgroup memory.peak/events before removal and retain its exact
meaning: charged cgroup memory, not aggregate process RSS. Record wait4 child
usage and sampled process RSS separately with their units and limitations;
neither is an exact sum of all overlapping process RSS. No synthetic RSS is
substituted. Effective parent resource constraints remain part of the record.
An offline verifier must recompute artifact hashes and refuse missing,
duplicate, unsafe or inconsistent fields, changed source/cache/toolchain,
wrong limits, unproven cleanup, timeout, incomplete coverage or hidden failures.

## Integration and release gates

Before production use, independent finder and skeptic inspect actual runner
code and adversarial controls, without Lean/server. Synthetic controls cover
escaped descendants, interruptions during create/inspect/wait, foreign identity,
timeouts, memory/swap/CPU drift, headroom loss, source/cache/toolchain mutation,
output-path collisions, truncated/missing logs and false cached success. They
are containment/validator tests, never Lean measurement acceptance.

Then run a bounded lightweight toolchain/KeySort prerequisite and one actual
slow module, inspect its full receipt, and proceed serially through all fifteen
and the root/audits only if it passes. CI and lane-end hooks require an explicit
integration patch and actual gate evidence; existing hooks alone do not prove
the new runner ran. Matched before/after measurements need identical source,
toolchain, cache content/metadata and execution conditions, at least three
rounds with raw distributions. Stop above ten-percent slowdown; no warm/cold
substitution or statement/budget change. H56 VM-specific requirements remain
external unless the latest transferred result explicitly includes them here.

## Axiom-pin relocation

No pin relocation or inventory/root regeneration is performed in this phase.
After authenticated latest intake and a reviewed exact mapping/preservation
patch are ready, request a coordinator quiet window naming base, touched files,
old/new key mapping, axiom/signature checks, rollback refs and expected duration.
Only then apply and measure the reviewed relocation in that window. Scanner
key coincidence and a lexical preview do not establish Lean equivalence.
Every pin/check is retained. A runner design review grants no relocation window.

## Implemented runtime rebuild helper (not the H127 runner)

The reviewed readbounds/serial-build.py component authenticates its current
Lean dependency inventory against Git and pins the explicit Lake shim, serial
configuration, lakefile, toolchain selection and actual Lean/Lake executables.
It handles canonical leading import headers, refuses the specified unsupported
forms, rechecks source/execution inputs and fails target invocations beyond
300 seconds even after a zero process exit. Four failure-control methods pass.

Its 344-target changed-runtime sequence completed in 226.16 seconds under the
existing bounded outer wrapper. Cached dependency admission is preparation,
not slow-example re-elaboration or matched A/B measurement. This helper does
not provide sealed snapshots, image/cache authentication, complete lifecycle
cleanup or whole-job RSS. The controller, worker, offline verifier and original
five-module A/B remain open. H134 retains 600 seconds for slow-library CI,
300 seconds for VM/default checks and the default RowsNine STOP.

## Durable intent and precise clock components

`lifecycle-journal.py` now provides one-time lease provisioning, descriptor-relative
private storage, an external locator pinning both directory and lease inodes plus
a random lease-content hash, and a nonblocking controller lease. Reservation and
intent publication use file/directory fsync with atomic replacement. Canonical
event records bind nonce, plan/image identifier syntax, boot identity and ordered
monotonic observations. Inherited-fork API leases and replaced/corrupt stores are
refused. Sixteen tests include real process death and controller contention.

Only an abort before any published create intent can release this component's
barrier, after its receipt is durable. Post-create states remain blocked, even
when a caller supplies apparent drain observations. This is not authenticated
Docker cleanup or hostile-host protection. The controller still must persist
the returned locator outside the store before creation, exclude other writers,
close journal descriptors before worker execution and integrate a real drain
verifier. No production worker is exposed or run by these components.

`measurement-clock.py` brackets BOOTTIME with MONOTONIC nanosecond reads and
compares conservative elapsed bounds against an already approved budget.
Deadline equality and overruns are ineligible regardless of a process exit.
Observable disagreement requires stopping and reports no remaining time.
Consistency does not prove an unsuspended host. Five tests and a read-only
actual Linux clock observation cover this arithmetic. It grants neither a
budget nor CI status, and does not enforce a running process deadline itself.

Both components passed independent read-only finder/skeptic source reviews.
The first review found a replaceable lease inode; one-time provisioning and
external inode/content pins fix it. The initial test-child quoting failure is
retained separately from the recovered controls. There are no new Lean files,
theorem/axiom changes, proof-budget changes or slow-proof runs. R1/R3/R5/R6
end-to-end obligations remain open: fixed controller/worker recipe, sealed source
and cache/image inputs, actual per-stage resources, deadline enforcement, whole
job measurement, verified cleanup, offline verification and the five-module A/B.
H134's slow-library CI allowance remains 600 seconds; VM/default remains 300.

## Kernel resource observation component

`kernel-resources.py` now reads a bounded cgroup-v2 hierarchy and identifies a
process by unique direct PID membership, rather than joining its namespace path
to a guessed mount root. It pins ancestor directory descriptors and records the
process start identity, namespace handles, leader affinity/scheduling policy and
mount identity before/after capture. Threaded or racing layouts, duplicate PID
membership, unsafe/oversized reads and changing resource settings fail closed.
Twelve controls include descriptor-leak, configuration-drift and process-identity
cases. Synthetic filesystem cases are not actual cgroup authentication.

CPU cpuset cardinality and configured sustained fair-class quota rate are
reported separately. Quota ratios are not short-interval concurrency guarantees;
period boundaries, burst credits and per-thread scheduling remain relevant.

These are non-atomic point-in-time kernel observations. Charged cgroup memory is
not aggregate process RSS. Complete host-lineage and Docker ownership flags are
explicitly false. The host observation is not an approved worker scope. Real
Docker probes are deferred until the owned creation/cleanup controller exists;
there is no worker, budget authorization, continuous monitor, cleanup or complete
measurement verdict here. The full runner and five-module A/B remain open.


## Raw Git source preparation

`source-snapshot.py` prepares regular raw Git blobs from an exact SHA1 commit,
ignoring checkout dirt, untracked files and archive export attributes. It refuses
symlinks and gitlinks. A fresh private shallow Git database contains the chosen
commit, trees and blobs, with no remotes, common directory or alternates. Parent
history is deliberately absent; a check needing it requires a separate explicit
input rather than an implicit live-repository fallback.

The external manifest hash pins file bytes/modes, directory membership and the
Git executable used by verification. Root/manifest links and extra or changed
entries fail verification. Preparation and verification assume exclusive private
writer control. They do not resist a malicious concurrent same-user writer or
prove a read-only mount. The disk preflight is a coarse estimate, not capacity
or inode reservation; production snapshots require the future controller capacity
monitor/reservation. Full-tree production preparation remains unqualified.

The source component is independent of toolchain, package, cache, image and CI
identity authentication, resource containment, deadline enforcement and cleanup.
It does not execute workers or authorize slow proof or timing replays. H127 needs
all of those layers and the five-module A/B before runner acceptance.


## Fixed Docker lifecycle diagnostic

`docker-probe.py` is a fixed sleep-only diagnostic, with no arbitrary worker
command or mount interface. The CLI holds the repository writer lock. It pins
its source dependencies and local Docker client/socket/boot/daemon identity,
uses an immutable local image ID without pulling, and checks the exact recipe
and full-ID/name/nonce/image/plan ownership before destructive operations.
The container has no network, bind mounts, extra capabilities or writable root;
its requested memory/swap and single-CPU affinity/quota are checked in the
PID-derived kernel hierarchy before a drain observation is eligible.

A bounded background collector pins visible ancestor descriptors and samples
reserve and configuration through cleanup. Recorded breaches or drift abort
foreground calls. Cleanup continues despite a reserve stop. Monitoring is
frozen, final-sampled and checked before a positive observation is recorded;
sampling does not prove the absence of pressure between samples or reveal
hidden ancestors. Docker calls have bounded output/time. One cleanup deadline
includes daemon identity checks, stop/removal and pinned cgroup disappearance.
A watchdog expiry is unresolved, never successful cleanup.

Ambiguous creation attempts an exact-name lookup followed by full-ID/nonce
ownership validation. An empty lookup does not prove no late creation. Signals,
malformed responses, unknown ownership or unavailable kernel pins retain the
active barrier. No name-only mutation, forced removal of unknown ownership or
approval override is exposed. A positive diagnostic records only removal of
this owned Docker identity and its pinned kernel group. The journal deliberately
retains its post-create barrier, including after this observation. Production
worker containment, authenticated cleanup/barrier release, sealed inputs,
measurement provenance, CI and five-module A/B remain separate obligations.


The diagnostic CLI also writes a one-shot reservation in the original checkout
before container creation. It never removes or replaces that reservation;
a different output directory cannot bypass an unresolved diagnostic. The
component exposes no next-worker or force-reset operation. Any recovery needs
its own reviewed protocol and cannot infer kernel drain from Docker command
success or current path absence alone. Failure diagnostics retain the last
kernel predicate facts when available; missing historical facts remain unknown.


The reserve collector registers every distinct worker ancestor as well as the
controller lineage and worker leaf. Shared directory identities retain both
roles and keep their outer-reserve obligation. Each worker registration must
match the earlier pinned kernel observation; a changed ancestor cannot become
a new unchecked baseline. Subsequent samples compare every registered group's
constraints. This remains bounded observation, with the existing hidden-ancestor,
inter-sample and unresolved-cleanup limitations.

## Offline journal structure intake

`offline-journal.py PATH --sha256 EXTERNAL_PIN` inspects a bounded canonical
lifecycle record through nofollow ancestor/file descriptors. It checks the
external byte pin, unaliased regular-file identity and existing lifecycle
schema/hash chain/transitions. It reads no lease token, executes no recorded
facts and writes no live-store files. Its output labels only the last recorded
state and structural validity; all fact, lease, cleanup, resource, measurement
and barrier acceptance fields remain false. A SHA256 supplied by an untrusted
record is not authentication. The caller must obtain its pin separately and
bind the reviewed inspector/dependency sources; this component does not attest
its own execution environment or hostile same-UID writers.

The saved failed-probe record can be inspected without interpreting its
`cleanup-unresolved` state as recovery. Empty/deactivated kernel observations,
Docker ownership and durable cleanup remain separate missing verification
layers. Neither this inspector nor the cgroup diagnostic clears the existing
reservation. The full sealed-input controller/worker, recovery/acceptance
verifier and five-module A/B remain unfinished.

## Worker input mount observation

`readonly-inputs.py` observes a dedicated non-root input directory through a
retained nofollow FD. It requires the FD mount ID and filesystem device to match
an exact mount point in the kernel mount table, both per-mount `ro` and kernel
`ST_RDONLY`, no nested/stacked mounts, and an unchanged mount table/namespace
through capture. A read-only bind mount may legitimately have a writable
superblock; the per-mount and kernel flags are required independently.

The component creates no mounts and runs no commands. It cannot establish that
another namespace lacks writable aliases, exclude later remounts, bind package
or source contents, authenticate the controller namespace or authorize worker
execution. Those output flags remain false. Synthetic positive controls and a
real writable-directory refusal are not production mount/sealing acceptance.
The controller must still bind the exact input pins and namespace ownership,
enforce isolation over the full invocation, and independently verify measured
resource, cleanup and output evidence. The old probe barrier is unchanged.

## Full-inventory input copy preparation

`input-copy.py` exposes a preparation API for toolchain/package/cache input
copies under the controllers exclusive writer lease and resource/deadline
supervision. It has no CLI or worker-launch interface. It requires a separately
pinned complete `input-inventory.py` receipt, checks the entire observed source,
and creates an exclusive new destination through nofollow descriptors. Source
and destination ancestors must also be disjoint by device/inode identities,
so an apparent external path through a bind alias cannot modify the source.

Regular file bytes are streamed and hashed; hard links are flattened. Modes,
ownership, nanosecond mtimes, xattrs and safe internal symlinks are preserved and
compared by complete destination inventory, with another full source comparison.
Insufficient privilege to preserve metadata fails rather than dropping fields.
An error leaves a partial destination that is never reused or silently deleted.
The copy keeps its final read-only modes until after xattr restoration. Failure
controls cover source drift, receipt substitution, special files, existing or
aliased destinations, resource stops and descriptor cleanup.

Disk/inode checks before creation and during copying are samples, not a
reservation or continuous capacity guarantee. The two-gigabyte preparation
reserve does not replace the workers four-GiB outer memory reserve. Passing
small filesystem fixtures supplies no production package/toolchain/cache pin,
immutable mount, hostile-host authentication, lifetime sealing or worker
execution authorization. Those output fields remain false. Integration into
the authenticated controller/worker and offline resource/measurement/recovery
verifier, production qualification and five-module A/B remain unfinished.

## Closed input set and worker environment

`input-set.py` binds exactly four independently pinned complete inventory
receipts: source, toolchain, packages and initial cache. It re-observes every
root, rejects overlapping directory identities and external hard links, and
matches tracked source bytes/modes against the pinned prepared Git plan. The
actual fifteen slow files, root imports and non-default library mapping must
remain present. This core-only job requires the existing empty Lake manifest,
no declared Lake requirements, and an empty package input; no dependency is
resolved implicitly. Bridge is a separate job.

The toolchain selection remains Lean 4.24.0. Executable hashes identify the
observed bytes; inert fixture bytes can satisfy the structural tests and do not
establish binary version, correctness or production readiness. Private Git
object semantics still require the snapshot verifier. Final re-observation is
non-atomic and does not establish input lifetime sealing.

The returned worker environment is a fresh fixed dictionary with input and
output mount paths. It inherits no Lean/Lake/Git paths, loader overrides, caller
home or CI variables. The controller must still bind those paths to actual
pinned mounts and an authenticated image, initialize the writable private cache,
provide network isolation, enforce budgets/resources and verify cleanup. Neither
this API nor an ambient CI flag authorizes the 600-second CI allowance. All
image, Git semantics, binary-version, cache-initialization, network, mount,
lifetime, CI-budget and worker-authorization claims remain false. No process,
mount or worker is launched by input binding.
