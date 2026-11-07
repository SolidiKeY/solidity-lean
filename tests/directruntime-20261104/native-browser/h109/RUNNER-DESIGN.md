# H127 serial slow-example runner: pre-use contract

Status: design and source-plan preparation, **not an executable measurement
runner or acceptance result**. Latest module-times result and rejected-draft
bytes are requested in intake-request.json. The available H82 handoff is older.
Existing repository documentation supplies failure observations, not delivery
of that latest result. H127 transfers this runner, not the whole H55–H58 lane.

H109 already has a non-default SoliditySlowExamples library containing fourteen
modules: DecisionGaps and its eleven example importers, OpenLoops and RevertData.
The current generated roots and statements stay unchanged. Every module is
re-elaborated serially; cache admission or a cached root build cannot replace
these checks. CI and lane-end/full validation keep the slow root. Ordinary
checkpoint selection keeps its current exclusion. Pending the exact H116 scope in the latest handoff, this candidate uses a conservative 600-second
runner deadline here (one total deadline, not 600 multiplied by fourteen); it changes no theorem heartbeat or other module budget.
No unchanged stopped timing workload is authorized by this plan.

## Execution and trust boundary

The implementation must have separate controller, container worker and offline
receipt verifier. A plan cannot execute arbitrary argv. The only execution
recipe is the repository per-file gate with a reviewed Lake shim enforcing
`-j1` and `LEAN_NUM_THREADS=1`, followed by the slow-library/root and existing
required audit checks. Inspect the gate's current timeout before integration:
a hidden 300-second wrapper cannot silently negate the candidate 600 seconds.
Dependency preparation is a separately timed stage, never part of a fake
cached-verdict pass. Direct re-elaboration of each selected file is required.

The controller owns the global writer lock through snapshot preparation,
checks, verification and cleanup. It requires an explicitly authenticated
commit, clean tracked sources and complete regular-file source inventory.
prepare-plan.py binds bytes to Git blobs/tree and SHA256 without executing
anything. Unknown entries, target drift, source changes and unsupported root
syntax fail closed. The worker receives a sealed read-only source snapshot;
untracked and ignored source files cannot enter through the live checkout.
This phase does not yet implement snapshot creation or its mount verification.
The snapshot must include isolated Git metadata because per-file gate.sh invokes
Git. Construct it from a pinned sealed bundle into a private clone, never by
pointing at live .git or a shared worktree common directory. Disable system and
global Git config, external hooks/filters and alternates; verify the exact
commit/tree and complete materialized snapshot. Mount that private Git metadata
read-only with the source. The preparer's descriptor-relative no-follow regular
file reads reject symlink ancestors/FIFOs/devices and bound reads by blob size;
this is still a non-atomic live observation, not a substitute for snapshot proof.

Pin every Lake dependency/package tree and lake-manifest.json, including ignored
.lake/packages inputs, with exact source and resolved package identities. Reject
unlisted dependencies or packages not present in the sealed input inventory;
no network resolution during checking. Pin the Docker image by immutable digest, full Lean toolchain tree (binaries,
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
sealed. Only a drained, verified zero-exit module within the remaining runner budget is a pass.
Every failure records its stage; missing data is unknown/fail, never zero time.

Reserve an unguessable run name and ownership label before container creation.
Persist the intended identity before Docker starts; interrupted create still
has a known name to reconcile. Verify ownership before destructive cleanup.
Install signal handling before create. Timeout, exception, signal, output I/O
failure, OOM or reserve breach initiates whole-container kill/removal, including
setsid/double-fork descendants. Waiting for the launcher or killing its process
group is insufficient. Confirm the owned cgroup is empty/removed and reconcile
the Docker identity before declaring cleanup complete. Failure to establish
cleanup is a failed run that blocks the next module. The 600-second acceptance
deadline stops new work and triggers termination; cleanup continues beyond it
until emptiness is established, but all excess time is recorded and cannot be
counted as a passing run or a renewed deadline. A separate cleanup watchdog
reports unresolved cleanup and prevents any subsequent worker; it never turns
a timeout into success. Cleanup must not delete
pre-existing or foreign containers. Never start a second worker speculatively.

Use monotonic_ns plus CLOCK_BOOTTIME for sub-second elapsed measurement and
detect disagreement/suspension. Start timing before the measured command;
enforce one total 600-second runner deadline independently of exits, covering
all worker/dependency/check/cleanup stages, with no reset between modules.
Source/toolchain preparation before that invocation is recorded separately and
runs no Lean. Obtain the original H116 granularity from the requested handoff;
if it authorizes a different policy, review that explicit policy before use. Report setup,
dependency preparation, check and cleanup separately. Record exact command,
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
slow module, inspect its full receipt, and proceed serially through all fourteen
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
