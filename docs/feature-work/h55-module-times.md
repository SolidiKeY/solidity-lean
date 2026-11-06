# H55 module-times backfill

Base: `4d3790eadb8a5212233bc7d5e345817476b2f590`. This is an
incomplete standalone backfill, not a production timing gate or a proof pass.
The H55 correction reserves existing producer and consumer files to their
current owners until the coordinator transfers exact leases. No such files
were edited here.

The existing `scripts/check-automatic.mjs` parses only Built TestSuite rows;
it does not require every intended module to occur, and its own documentation
says cache replays are not timed. Its cumulative memory-loop gate is a separate
requirement and must not be replaced by a per-module check.

At the base, `git ls-files '*.lean'` reports 7,166 tracked Lean paths:
6,261 under `Solidity/`, 629 under `Bridge/`, 251 under `tests/`, eight under
`vendor/`, and the remainder elsewhere. These are a broad census, not an
approved scope or a list of buildable Lake modules. Bridge source directories,
test controls, root modules, generated modules and optional libraries need
explicit discovery and classification; a filesystem count or only generated
roots cannot establish full coverage. In particular path-to-module mapping and
standalone controls must be checked against actual build configuration.

`scripts/h55/module-times/receipts.py` is a standalone JSON consumer for a
nonempty explicit inventory of source paths and one fresh successful receipt
per path, with a fixed 300-second maximum. It rejects missing, duplicate,
extra, malformed, failed, timeout, cached and over-budget records. The unit
controls use synthetic data only. It neither determines the assignment scope
nor executes Lean, enforces a timeout, authenticates the producer, the clock,
the tree, toolchain or cache, or ensures serial execution and resource bounds.
A forged successful row can pass. It must not be wired as a production gate
until those missing controls and a complete independently checked inventory
are supplied. Cumulative workload rules remain separate.

Validation: `PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s
tests/h55/module-times -p 'test_*.py' -v` passed two test methods with
boundary and negative cases. This is a software test, not a Lean proof or H56
measurement. Installed binaries report Lean 4.24.0 commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b` and Lake `5.0.0-src+797c613`;
no KeySort runtime gate was run.

Outstanding: authenticated complete inventory, actual H56 gate-VM execution,
real timeout/fake-time and failure controls, full-scope acceptance, independent
read-only finder and skeptic reviews without Lean server, owner migration
patches and exact leases, qualifying splits, identical-state before/after
wall and RSS with stop above 10% slowdown, affected-module and final gates,
cache pack, checksums and final handoff. No claim of completion is made.

## Additive census and Lake-log parser

The coordinator confirmed that missing `get_goal` is not a blocker and that
H56 VM identity remains a measurement dependency. `census.py` enumerates and
hashes every Git-tracked Lean path in the live worktree; it fails on missing
files or symlinks. Its classifications retain every row, including 101
vendor-review, nine bridge-control-review, 254 control-check-review, and 14
root-or-other-review paths. The other categories comprise 5,907 core, 354
examples and 527 Bridge paths. This is not a completed source-to-module/build
mapping, a clean-tree guarantee, or authority to exclude any category.

`lake_log.py` recognizes Lake Built/Replayed rows with strict duration units,
and its CLI compares an explicit module-to-path JSON inventory with the log
and supplied process exit status. Duplicate or missing mappings and records,
extra modules, replays, bad timing syntax, failed process status and times over
300 seconds fail. Its input log and exit status are unauthenticated; it cannot
prove the clock, execution, timeout, cache state, environment or inventory.
Untimed replay rows are rejected as unrecognized timing rows. When run as a
library on `tests/h28-terra/drift-reports/evidence/full-gate.log`, the parser
found 144 timed rows and one unrecognized untimed replay row. This historical
probe is not H56 evidence.

The first expanded unit-test run failed to import the parser due to an
unterminated docstring; it was fixed. The subsequent command
`PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/h55/module-times -p 'test_*.py' -v`
passed six test methods. Independent finder and skeptic reviews remain pending.
Timeout enforcement and fake-clock detection are not implemented; synthetic
status and malformed-time tests do not establish either property. No source or
proof migration occurred, and the full gate remains incomplete.

## Experimental process and clock controls

`measurement_control.py` runs isolated subprocess controls, with timeout
termination of the spawned process group and comparisons of monotonic and
boot-time clocks. Its tests exercise successful execution, nonzero exit,
spawn failure, real timeout, invalid configuration and injected clock
inconsistency. `PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s
tests/h55/module-times -p 'test_*.py' -v` passed nine methods for the committed control files; an 11-method run
also included the then-uncommitted mapping tests. These are synthetic controls, not H56 measurements or a Lean proof.
The runner is deliberately not a production gate: it discards process output,
does not authenticate clocks or execution environment, cannot detect clocks
falsified consistently, and does not impose the required memory/no-swap/serial
or source/cache binding conditions. Its process timeout begins after process
creation; the later clock check includes creation time. In particular no gate
may accept its output as authenticated measurement evidence. Independent
finder and skeptic reviews remain outstanding.


## Candidate context mapping

`mapping.py` preserves every census row and supplies a candidate module name
and context where path shape permits. On the base tree it identifies 6,896
candidate names and retains 270 unresolved rows, without selecting exclusions.
It reports same-context collisions; none were found in this census. All names
remain marked for review: the mapping does not establish that a path is a Lake
target, that its imports resolve, or which test inputs are intentionally
negative. Bridge vendor paths use a separate candidate context and still need
actual Lake-glob inspection. The source hashes are worktree hashes, not a
verified clean-tree or cache identity. Tests compare all paths against the
tracked-file census and cover Bridge, example, standalone and ambiguous names.
`PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/h55/module-times -p test_*.py -v`
passed 11 methods. Independent finder and skeptic reviews are pending.

## Parser failure-row correction

A local review found that the initial parser could accept a `✖` Built row if a
caller supplied zero process status. The parser now rejects such a row, and
rejects traversal or malformed module/path mappings. Regression controls and
the full 11-method synthetic suite pass. This local check is not a substitute
for either required independent review. The parser remains a log consumer,
not authenticated proof that any measurement occurred.

## H70 census reconciliation

The previous 270 rows now receive candidate dispositions: 269 standalone
file-check candidates (nine Bridge and 260 root-context candidates), plus the
Bridge vendor DoNames module with an apostrophe in its name. Apostrophes are
accepted in candidate module names and the log parser. These are classification
results, not established execution recipes or exclusions. Standalone tests and
scripts may depend on custom fixtures, special contexts or intentionally
failing behavior; their expected outcomes, imports and scope still require
owner review. All 7,166 paths remain in the inventory, and no duplicate names
were observed within a candidate context.

## H70 resource-control prototype

`resource_guard.py` fails closed when the cgroup layout or values cannot be
read, the memory limit exceeds 12 GiB, swap is enabled, or available host or
cgroup headroom falls below 4 GiB. It never changes a cap. Its experimental
command helper samples those constraints during a subprocess, stops on a
resource failure or timeout and cleans up its process group before reaping the
leader. Synthetic tests cover boundaries, spawn and process failures, timeout,
resource loss and refusal before spawn. The executor preflight returned
`resource state unavailable or unsupported` (its observed cgroup limit is
16 GiB and swap limit is unrestricted); no Lean job was launched.

This is not production timeout/resource acceptance: sampling is periodic,
caller lock ownership is assumed, and no check binds the toolchain, command,
Lean thread/job settings, exact tree, cache or H56 identity. It does not
prevent a child from escaping the process group, and it does not authenticate
clocks or measurement results. The fixed 300-second production orchestration,
complete inventory and independent finder/skeptic reviews remain outstanding.
The full synthetic suite passed 14 test methods. An initial commit command for
the census failed at shell parsing and made no edits; the corrected command
succeeded.

## Published-master comparison and locked prototype

A fresh `git fetch origin master` resolved master to
`96788a95383b6295dc13774ef681297adf1337a7`; the assigned base is its ancestor.
The published tree had no H55 module-times helpers in the assigned paths.
A read-only Git-tree comparison found 7,328 tracked Lean paths on that master,
162 more and none removed relative to the assigned base. The candidate mapper
classified all as 7,034 module-name candidates and 294 standalone file-check
candidates, with no same-context collisions. This is not a source-hashed or
approved master inventory, and no rebase or new master measurement is claimed.

The experimental guard now exposes a fixed-300-second wrapper that acquires the
repository writer lock nonblockingly, and compares monotonic and boot-time
clocks during monitoring. Tests cover lock contention and deliberate clock
disagreement. Sixteen synthetic test methods pass without Lean. The wrapper
still accepts a caller-supplied command, cannot authenticate two falsified
clocks or the VM/tree/cache/toolchain, cannot guarantee process-tree containment
against process-group escape, and does not enforce Lean thread or job flags.
Production acceptance, actual H56 evidence and both independent reviews remain
pending; the attached executor preflight still cannot be counted as a pass.

## Inventory coverage consumer

A fresh origin/master fetch resolved to `5f7bb1441566aaad64a34436904afc61de762fd2`;
the assigned base remains its ancestor. No H55 module-times helper was found
in the assigned master paths. The frozen-base worktree remains unchanged.
`inventory_gate.py` compares every tracked Lean path and its current SHA-256
against a supplied inventory, rejects absent, duplicate, extra and undecided
rows, and refuses tracked source changes and untracked Lean files. Its tests
cover these structural cases. Eighteen synthetic test methods passed before
subsequent command-constructor work. The checker does not validate whether the
chosen execution context or method is correct, prove exhaustive coverage of
ignored/generated Lean sources, authenticate toolchain or cache, or measure a
module. A manually supplied disposition is not owner acceptance.

## Fixed-shape Lean command candidate

`lean_command.py` constructs an absolute Lean invocation with `-j1`, the
existing `--tstack=131072` flag and `LEAN_NUM_THREADS=1`, verifies a supplied
executable SHA-256 and rejects source traversal or symlink paths. The additional
synthetic test uses a fake fixture executable; no Lean was executed. Nineteen
synthetic test methods pass. This constructor is not wired to the resource
prototype and cannot authenticate the supplied executable pin, environment,
import path, toolchain, tree, cache or H56 VM. It does not independently enforce
one heavy job or process containment. The complete gate and independent
finder and skeptic reviews are still pending.

## H70 command hardening

The additive command constructor now also requires an executable Lean file
and rejects selected dynamic-loader and Lean-option environment variables.
The 21-method synthetic suite passes after all current backfill changes. This
is not an environment allowlist or proof that the supplied executable hash,
import path, cache and runtime are trustworthy; no production pass is claimed.

## H70 containment status

The fixed-budget prototype wrapper now returns `untrusted-prototype-success`
rather than a passing status even when its child exits successfully. This
prevents an experimental process-group run from being mistaken for production
acceptance. A process can still escape the group; kernel-enforced dedicated
containment and independent acceptance remain unimplemented. This change does
not establish timeout cleanup for escaped descendants and does not authorize a
Lean measurement.

## H70 source and tool identity snapshots

`provenance.py` records a supplied exact clean Git HEAD and tree plus the
selected tracked source and tool SHA-256. Synthetic temporary-repository
controls reject wrong HEAD, dirty source and path traversal and detect changed
tool bytes. It is an identity snapshot, not an authenticated measurement: it
does not pin ignored files, imported objects, caches, environment, VM identity,
file stability during execution or an approved tool hash, and it is not wired
to the runner. The full 21-method synthetic suite passed. Independent finder
and skeptic reviews, containment and production acceptance remain pending.

## Synthetic escaped-process containment control

After fetching origin/master at `5f7bb1441566aaad64a34436904afc61de762fd2`,
`tests/h55/module-times/container-containment.sh` builds a tiny static C
fixture locally and runs it without network or Lean in an owned disposable
Docker container. The child calls `setsid`, leaving the parent process group.
The test verifies distinct session IDs and process start times, kills only its
own container, and checks that neither original process identity remains.
The final hardened run exited 0 with memory and memory-swap both 67,108,864
bytes, pids limit 16 and network none; the container reported exit 137 without
OOM. Evidence is `/workspace/h55-module-times-evidence/containment-control-02`.
Docker server was 28.4.0 and compiler was Debian 14.2.0. A prior exploratory
fixture also passed; neither run is a timing or Lean proof receipt.

This establishes one local synthetic containment observation, not production
acceptance. The timing runner is not integrated with Docker or a trusted
containment backend, and the control does not demonstrate an automated timeout,
resource-stop cleanup, cache/provenance binding or behavior on H56. No hard
resource limit was raised. Independent finder and skeptic reviews remain
pending; no production timing pass is claimed.

A local review also found that `provenance.unchanged` accepted any equal
nonempty dictionaries, even when they lacked identity fields. It now rejects
incomplete or malformed records, with synthetic regression controls. The
21-method unit suite passes, and `sha256sum -c` passes for the committed
containment evidence manifest. This is a local finding, not either independent
review, and it does not authenticate the recorded identities.

## Synthetic automatic container deadline

An additive `container_watch.py` prototype monitors an explicitly labeled,
owned fixture container using the local Docker socket, compares monotonic and
boot-time clocks and kills the container on a synthetic deadline. The
repeatable containment script now drives a 0.3-second deadline against a
64 MiB, no-swap, no-network fixture whose child escapes its process group with
`setsid`. Runs 03 and 04 returned `timeout`, container exit 137 without OOM,
and showed both original process identities absent. Their files and hashes are
recorded in `tests/h55/module-times/deadline-evidence.sha256`; bulk data remains
under `/workspace/h55-module-times-evidence/containment-control-03` and
`/workspace/h55-module-times-evidence/containment-control-04`.

Twenty-five synthetic unit test methods passed, including invalid identifier,
ownership mismatch, unverifiable ownership and inconsistent-clock controls.
This is not production acceptance or H56 evidence. Docker inspect/kill calls
can delay cleanup after the deadline or fail; cleanup is attempted only after
ownership is verified. The watcher does not continuously enforce resource
headroom, authenticate image or daemon, bind source/tool/cache, prove the
300-second production bound or orchestrate actual Lean. Both clocks can be
falsified together. The full runner, independent finder/skeptic reviews and
all assigned runtime and migration gates remain pending. No Lean was run.

## Synthetic container resource monitoring

The experimental deadline watcher now checks host `MemAvailable`, zero host
swap, and finite parent-cgroup headroom on each polling pass, retaining a 4 GiB
reserve. It inspects the owned container for a finite memory limit no greater
than 12 GiB, memory-swap equal to memory, network none and a positive pids
limit. On a policy or resource failure it attempts cleanup only after verifying
the owned label, and cannot report a passing result. Two local synthetic runs
(05 and 06) used the 64 MiB no-swap escaped-child fixture and reached the
0.3-second timeout with both process identities absent. Their off-Git evidence
is bound by `tests/h55/module-times/resource-evidence.sha256`. The expanded
28-method synthetic suite covers resource loss, unreadable state and mismatched
container limits.

These checks sample rather than continuously enforce host reserve. Docker
inspection reports configuration rather than authenticated effective kernel
state, and cleanup may be delayed or fail. The watcher does not bind a trusted
image, daemon, source/toolchain/cache or H56 identity, and it is not wired to
an actual Lean production gate. No 300-second measurement or Lean proof is
claimed. Independent finder/skeptic reviews, full acceptance and the assigned
H56 and owner dependencies remain outstanding.

## H82 synthetic effective-cgroup checks

After fetching master at `7ae5607c9ecfff4078162115eaaaa48a1ff46eb0`, the
synthetic watcher compares the owned container process and exact container ID
to the observed local cgroup-v2 mount and verifies effective `memory.max`,
`memory.swap.max`, `memory.swap.current` and `pids.max` against its configured
limits. Unsupported cgroup layouts and mismatches fail closed. The 29-method
synthetic unit suite passes. The final local escaped-child deadline control
09 passed with effective memory.max 67,108,864 bytes and memory.swap.max 0;
control 08 also passed. The first attempt, control 07, failed safely because
its initial path guard rejected the sibling cgroup namespace path. All three
runs are retained off Git and bound by
`tests/h55/module-times/kernel-resource-evidence.sha256`.

This is a local synthetic control, not a 300-second Lean timing or production
acceptance. It supports only the observed local namespace layout, samples
rather than continuously checks resources, and does not authenticate the
Docker daemon, image, VM, tree, toolchain or cache. The command, timeout,
provenance and inventory helpers are not integrated as an accepted runner.
H56 identity and actual full-inventory measurements remain a wait before
qualifying splits. H82 supplies standing permission for statement-preserving
edits; owner permission remains required for the statement, dependency,
interface, proof-budget, axiom-set and exclusion changes specified by H82.
Independent finder and skeptic reviews and all full-scope gates remain pending.

## H82 consolidation and cache-state backfill

This branch already contains the listed module-times member head
`9869c12e3f689be6056bfa7c59ada2f5c91c3e58` as an ancestor. The H28 timing
member remains behind the retirement and frozen-assignment barriers: its
reported `/workspace/h28-timing-handoff` is absent on this VM, the named
remote lane ref was not found, and no final stopped or goal-paused
acknowledgement was supplied. The full original rendered assignment and exact
scope manifest must be verified from its authenticated final handoff before
that lane can be merged or edited. Published master contains a timing-parser
commit, but that does not establish the requested final member head.

The additive `cache_fingerprint.py` fingerprints every regular file and
directory in a caller-selected tree, including content hashes, modes, mtimes,
link counts and empty directories. It rejects symlinks and nonregular files and
checks for changes during traversal and reading. Synthetic controls cover
content and directory changes, symlinks, FIFO inputs and mutation during a read;
the 32-method synthetic suite passes. This is a cache-state comparison helper,
not proof that the selected tree comprises all actual Lean caches, that a cache
is authentic, or that a before/after measurement occurred. It is not wired into
an accepted runner. Race-free snapshots, H56 identity and measurements, the
full gate, independent reviews and cache pack remain outstanding.

## H82 paused-member update and receipt consistency

The coordinator subsequently confirmed the H28 member goal paused. Its
reported final head is `28900209b0e221f9e20e07e06921a79527ca4d18`, but the
handoff directory is unavailable on this VM and the member explicitly reports
that the exact original rendered prompt is absent. Its branch was not found at
the named remote ref. The member must not be merged or worked on until the
final bundle, checksums, exact rendered prompt and scope are obtained and
verified. The module-times branch was externally advanced by two clean merges
of published master; previous local head `298e57b77d9d1cfbc8c9ad0f7d81acb7da9d4428`
remains an ancestor. On the resulting tree the candidate census retains 7,369
Lean paths: 7,064 module-name candidates and 305 standalone file-check
candidates, with no same-context collisions. These are not approved recipes.

The additive `evidence_consistency.py` checks supplied rows against a supplied
inventory and common source, tool, image, cache and VM fields. It rejects
missing, duplicate, stale, nonfresh, failed, nonserial, over-budget,
resource-invalid and inconsistent dual-clock examples. It checks consistency
only: a forged set of matching inputs can pass; it does not authenticate H56,
clock readings, inventory, source/tool/cache or process execution, and it is not
a production gate. The 34-method synthetic suite passes. Independent reviews,
H56 actual measurements and all full-scope acceptance remain pending.

## Receipt seriality correction

A local review found that the consistency checker previously accepted two
rows that each claimed one Lean job even if their recorded intervals overlap.
It now rejects overlapping monotonic or boot-time intervals, unsafe inventory
paths and oversized clock deltas; touching endpoints remain allowed. The
36-method synthetic suite passes, including overlap and extreme-clock controls.
This only checks supplied claims and cannot authenticate actual concurrency,
clocks or execution. It is not an independent review, an H56 measurement or
production acceptance. The H28 goal pause is confirmed by the coordinator, but
its exact original prompt and final bundle are still unavailable on this VM.

## Combined selected-input snapshots

`bound_snapshot.py` combines a clean source/tree/tool snapshot with a
caller-selected cache fingerprint, checking source and tool again after cache
traversal. Synthetic controls detect changed cache or tool bytes, dirty source
and a corrupted equal manifest; the 37-method synthetic suite passes. This
compares supplied snapshots and paths, not actual H56 measurements. It does
not establish cache completeness, trusted VM/tool identity, race-free state
between snapshots, or production runner integration. Independent reviews and
all H56, production and full-scope acceptance gates remain pending.

## Synthetic inspection-deadline correction

The experimental watcher previously checked time before Docker inspection but
could accept a successful exit after a slow inspection crossed the deadline.
It now checks both clocks after inspection. Its first live synthetic retest,
control 10, exited 1 with `watch-error` when inspection itself timed out near
the deadline; the fixture cleanup trap removed the owned container. The
watcher was then changed to classify an inspection timeout as a deadline only
when both clocks confirm the deadline has passed. Control 11 passed with the
escaped child absent after cleanup. Both attempts are retained and bound by
`tests/h55/module-times/inspection-deadline-evidence.sha256`; the 40-method
synthetic unit suite passes.

This is not a production timing or Lean proof pass. Docker inspection/kill can
still be delayed or unavailable, the watcher has not been integrated with
trusted image, source, toolchain, cache or VM identity, and independent reviews
remain pending. The coordinator confirmed H28 goal pause and quiescence, but
its final bundle and exact original rendered prompt remain unavailable here.

## Synthetic slowdown comparison

`slowdown_compare.py` compares a supplied pair for one source path. It requires
matching supplied VM, CPU, tool, cache, image, unchanged-input, memory, swap,
thread and job fields; fresh successful measurements; wall/RSS values; and the
4 GiB reserve. It stops when after-wall time is strictly greater than 110% of
before-wall time, using integer arithmetic. Synthetic controls cover the exact
boundary, over-boundary, failures and unmatched conditions; the 42-method
synthetic suite passes.

The comparator does not authenticate inputs, prove unchanged inputs or cache,
collect wall/RSS, handle a censored baseline timeout as a measurement, compare
statements/imports or identify H56. It is not an actual before/after result or
production acceptance. No split or Lean job was performed. Independent reviews,
H56 and the full gate remain pending. The H28 member pause and quiescence are
confirmed by the coordinator, but its final bundle, exact rendered prompt and
scope bytes remain unavailable on this VM.

## Synthetic full-set slowdown control

The slowdown comparator now accepts an explicit expected path set and checks
that each side has exactly one row for every path. Missing, extra, duplicate,
failed or over-300-second records cannot pass. A valid over-10% slowdown
retains the stop verdict even if another row is missing or duplicated; a
faster duplicate cannot conceal it. The command exposes this full-set mode.
The 45-method synthetic suite passes, including a command-level missing-path
control. A timeout is not converted into an invented baseline measurement.

This remains a comparison of supplied data. It does not prove the expected
set is complete, authenticate any VM or measurement, or establish identical
source, cache or toolchain state. It is not an actual H56 run, production
acceptance, a split or a Lean proof. Independent reviews and the full gate
remain pending. The H28 paused-member final bundle and exact original prompt
remain unavailable on this VM.

## H82b member-intake verification

The delivered H82b archive, manifest and SHA256SUMS matched their advertised
hashes; `sha256sum -c SHA256SUMS` passed. The timing-tools member record has
`verified_final_stop_head_pause=true`, paused status and the exact requested
head `28900209b0e221f9e20e07e06921a79527ca4d18`. The metadata archive contains
no Git bundle. The named remote branch was absent, and an exact-SHA fetch from
origin failed with `upload-pack: not our ref`. No H28 merge or source edit was
performed.

The metadata assignment field includes substantial original-assignment text
and an authenticated scope manifest. Its decoded UTF-8 bytes have SHA-256
`b1146de0b55d7ac23777b109a56342270f9b15bf86e875857844668776218589`; the
member objective names rendered-prompt SHA-256
`1693a6c1af58fbbe4fa6d829f8b464f608e725d0351415a9f2faf78d5780dfac`.
The relationship between those byte representations is unresolved; the
metadata is not claimed as a verified exact rendered prompt. The final Git
bundle/patch and the exact prompt bytes or a verified byte-reconstruction
procedure remain required before member integration or task work. No contact to
the retired worker was made.

## Synthetic unobserved-exit correction

The experimental container watcher now returns `unobserved-exit` if its first
successful observation finds the container already stopped; an observed nonzero
exit is classified as `failed`. Synthetic controls cover both cases. The
47-method synthetic unit suite passes, and the escaped-child deadline fixture
control 12 also passes. Its off-Git evidence is bound by
`tests/h55/module-times/observed-exit-evidence.sha256`. This does not prove
production execution, trusted provenance or H56 identity, and the watcher
remains outside an accepted production runner. No Lean job was run.

The H82b metadata checksum verification and paused head remain valid, but no
member Git bundle was included or fetchable at the named exact SHA. Common
newline transformations of the supplied assignment field did not reproduce
the member objective rendered-prompt hash. Exact prompt-byte provenance and
the final Git artifact therefore remain waits before H28 integration; no H28
files were edited.

## Experimental observation and snapshot bridge

`observation_bridge.py` holds the repository writer lock while taking
source/tool/selected-cache snapshots before and after a supplied experimental
action. It refuses failed actions, input drift, clock disagreement and invalid
elapsed values; even its successful result is explicitly marked
`untrusted-observation`. The 48-method synthetic suite passes, including
lock contention, fake-clock, failed-action and cache-drift controls.

This bridge cannot impose a timeout on arbitrary actions, authenticate action
results or H56 identity, establish cache completeness, enforce the container
resource policy, or produce a production timing receipt. It is not integrated
with the actual Lean runner. H28 final Git artifact and exact rendered-prompt
bytes remain unavailable; H56 measurements, full acceptance and independent
reviews remain pending. No Lean job or production timing pass occurred.

## Container-spec regression control

`container_spec.py` checks a supplied Docker inspection object against a
supplied plan for a fixed single-thread Lean command, image ID, non-root user,
environment, working directory, read-only bind mounts, memory/no-swap limits,
network isolation, namespace settings, devices and privilege settings. Its
synthetic controls exercise matching and mismatching objects. The first suite
attempt failed on a syntax error in the new test file; it was fixed, and the
final 50-method synthetic suite passes. The new control docstrings name the
container-masquerading regression they guard.

This is a verifier of caller-supplied objects, not an authenticated Docker
inspection or accepted runner. It does not prove the plan, image contents,
mount contents, effective cgroup state, deadline enforcement, cache, H56
identity or Lean execution. It is not wired into the experimental observation
bridge. The H28 final artifact and exact rendered prompt, H56 measurements,
full acceptance and independent reviews remain pending; no Lean timing or proof
pass is claimed.

## Static inventory and runner-control review

The coordinator-delivered H28 rendered prompt at
`/workspace/h62-coordinator-inputs/router-20261106T200314Z/timing-tools-prompt.txt`
hashes to the required `1693a6c1af58fbbe4fa6d829f8b464f608e725d0351415a9f2faf78d5780dfac`.
This resolves the exact-prompt-byte wait; the final H28 Git artifact for
`28900209b0e221f9e20e07e06921a79527ca4d18` remains unavailable and has not
been merged. H93 defers the h55b cold-timing experiment; it was not resumed.

On parent `4c2c5d9ccd3038c27ffc17ec322aac4bd3a26b0d`, the tracked-file census
contains 7,592 Lean paths: 7,088 candidate module names and 504 file-check
candidates. The census reports no same-context collisions. These are static
candidate classifications, not approved execution recipes or a complete gate.
The newer fetched master is `d96f2406d352de7e0b72ba6ac4ab29dc457582c6`.

Independent read-only finder and skeptic reviews examined the Python inventory,
provenance and runner-acceptance controls without Lean, server, builds or
writes. The finder identified zero-duration receipt acceptance and decimal
rounding above 300 seconds; exact Fraction-based Lake duration comparisons,
positive receipt times and exact Decimal CLI parsing now reject those cases.
On re-review the finder verified CLI `300.0` succeeds while
`300.00000000000001`, zero, NaN and Infinity fail. The skeptic identified
restart policies and healthchecks that could launch extra work, plus unbound
CPU quota/cpuset fields. The container-spec control now requires disabled
restart/healthcheck settings and matching explicit CPU fields. On re-review
the skeptic confirmed those exact examples are rejected. The reviewed input
hashes are `tests/h55/module-times/static-review-inputs.sha256`.

The skeptic also identified an unresolved production boundary: the watcher
starts its clock after container startup, so it cannot establish total runtime;
matching Docker CPU configuration also does not authenticate effective parent
cgroup quotas/cpusets. These are not fixed by the synthetic controls. The
51-method synthetic suite passes, but no H56 measurement, production runner
attestation, full inventory acceptance or Lean proof is claimed. H56 access
and actual full-inventory measurements, final H28 Git artifact, production
gates, split qualification, full acceptance and any needed further reviews
remain outstanding.

A further independent skeptic recheck found that a different Docker
`CgroupParent` could pass the synthetic configuration control. The control now
requires the reported parent to match the explicit plan, and the skeptic
confirmed its exact counterexample is rejected. The reviewed input hash
manifest was refreshed. A matching parent string does not authenticate the
actual ancestor CPU quota, cpuset, namespace mapping or daemon identity. The
pre-watch portion of runtime is still outside the watcher deadline. These
remaining limitations preclude production acceptance; no H56 run was made.

## Pre-start deadline and visible CPU ancestry backfill

The coordinator supplied H56 provisioning identity, not measurement or runner
attestation. The experimental `start_and_watch` checks for an owned created
container and anchors both clocks immediately before the Docker start request;
its synthetic tests include time spent in that request. It uses the unchanged
full requested allowance, not a one-second sub-limit. A 1.5-second synthetic
fixture in a network-isolated, 64 MiB no-swap container timed out and removed
both the parent and an escaped-session child. Runs 01 through 04 are retained
under `/workspace/h55-module-times-evidence/prestart-control-*` and bound by
`tests/h55/module-times/prestart-evidence.sha256`. No Lean job or H56 timing
was run, and the H93-deferred cold-timing experiment was not restarted.

The additive CPU ancestry helper reads visible cgroup-v2 `cpu.max` and effective
CPU/memory sets, binds the sampled process start time and cgroup membership on
both sides, rejects malformed ranges and incomplete Docker chains, and compares
visible policies across separately identified containers. Its output remains
`matching-visible-unattested`, never a production pass: the local `/..` mount
root hides higher ancestors. The fixture records that incomplete ancestry.
The 58-method synthetic suite passes.

Independent read-only finder and skeptic reviews used no Lean server, builds or
writes. Their PID-reuse, malformed-chain, reversed-range and cross-run identity
findings were fixed and rechecked; their input hashes are recorded in
`tests/h55/module-times/prestart-review-inputs.sha256`. The finder confirmed the
pre-start anchor and removal of the one-second sub-limit. It also found that
created-state inspection and Docker start remain non-atomic, a timed-out start
can finish after inconclusive cleanup, and daemon/kill latency can exceed the
deadline. The skeptic confirmed that hidden ancestors, transient changes,
CPU burst/weight/idle, daemon/VM identity and host scheduling remain
unauthenticated. The helpers are not an accepted production runner, and no
300-second hard-bound or actual H56 measurement is claimed. The exact H28
rendered prompt is verified; its final Git artifact remains unavailable.

## Visible CPU burst, weight and idle controls

The visible cgroup chain now records `cpu.max.burst`, `cpu.weight` and
`cpu.idle` alongside quota and effective CPU/memory sets. Missing or invalid
fields fail closed. Independent read-only finder and skeptic reviews found
that non-ASCII, oversized and over-u64 numeric strings could be mishandled;
those cases were fixed with bounded ASCII parsing and regression controls. The
finder rechecked the u64 boundary, and the skeptic rechecked oversized values
and changed or missing weight/idle fields. Neither reviewer used Lean, a server,
builds or writes. Reviewed source hashes are in
`tests/h55/module-times/cpu-policy-review-inputs.sha256`.

The final network-isolated synthetic fixture, control 07, passed using a
1.5-second deadline and a 64 MiB no-swap container; it recorded the visible
CPU chain as `ancestor_complete=false`. Controls 05 through 07 are retained off
Git and hashed in `tests/h55/module-times/cpu-policy-evidence.sha256`. This is
not H56 timing or a production pass. Hidden ancestors, transient changes,
quota-period phase and burst credit, sibling load, CPU frequency, host
scheduling and VM/daemon identity remain unattested. The pre-start race and
possible delayed Docker cleanup also remain unresolved. H93 cold timing was
not restarted, and the H28 final Git artifact remains unavailable.

The first final manifest verification after this CPU-policy change failed for
two entries in the earlier pre-start review manifest because that manifest
records the old CPU files at `57308b9ddc7c1c997dbcbead7ea3f4aa88be4474`.
Those reviewed bytes were extracted from that exact commit to
`/workspace/h55-module-times-evidence/prestart-review-57308b9dd`; the unchanged
historical manifest verifies against that snapshot. The other current evidence
and CPU-policy review manifests verify against their respective paths. The
failed check and corrected historical check are retained separately; this does
not retroactively claim the old review covered the changed CPU files.

## Candidate Lake invocation control

The published master gate now invokes `lake lean`; this additive constructor
prepares a serial candidate with `--no-build`, pinned executable hashes and
an explicit environment allowlist. It rejects unrecognized environment
variables, including `LEAN`, `LAKE_OVERRIDE_LEAN` and cache overrides. The
allowlist fix addresses the independent finder and skeptic finding that Lake
can otherwise select a different Lean executable despite a pinned PATH. The
focused synthetic control exercises the override pair and a cache override.

Both reviewers worked read-only without a Lean server or build. The finder
rechecked the fix and noted that HOME and XDG_CACHE_HOME still affect Lake
cache location; neither cache contents nor toolchain installation is
authenticated by this constructor. The skeptic identified that workspace
loading, configuration and dependency materialization can precede build
actions: `--no-build` is not containment, a write-free guarantee, or a cold
build equivalent. Source, toolchain, cache, VM and effective resource
provenance, production deadline enforcement and full integration remain
unproved. This is not an H56 measurement or a runtime/proof gate pass.
Installed versions inspected: Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613.

## Inventory acceptance review

Read-only static review of `inventory_gate.py` and `census.py` identified
remaining production acceptance gaps. The structural validator accepts a
manifest with a Bridge path assigned root context and no module identity; it
does not establish runnable mappings. The CLI checks tracked changes before
reading worktree bytes, without an atomic binding to committed blobs, so a
concurrent writer could invalidate the intended HEAD association. No such
concurrent change was observed. Ignored and generated Lean paths are outside
the current tracked-source census and untracked check. Resolving their role
requires a reviewed full inventory and runner/source provenance; structural
acceptance alone must not be used as the production gate.

The finder exposed staged edits hidden by opposite unstaged edits in the
original HEAD-to-worktree check. The checker now separately checks the index;
a synthetic Git repository tests that the old comparison succeeds while the
index comparison rejects a valid matching manifest. Both reviewers found the
first version of that regression test could fail for an unrelated empty
manifest; it was strengthened to check the precise diagnostic. This does not
resolve the source-to-blob race. The finder also identified that Git index
flags can hide changes; the checker now rejects Lean entries whose `ls-files
-v` tag is not ordinary `H`, with an assume-unchanged regression control.
This flag check is not an atomic source binding. Both reviews were read-only
and ran no Lean server or build. On this
turn origin/master advanced to `ac9d8db2ad2b29d4f04ed2391d78b5f19b4c97a6`;
its per-file `lake lean` gate does not implement this inventory-wide timing
acceptance. The H28 final Git object remains absent locally. No H56
measurement, bounded KeySort, runtime gate or proof pass is claimed.

## Selected Lake workspace observations

An additive synthetic observer fingerprints caller-selected configuration
files and dependency/cache trees and binds a digest of a candidate command.
Tests exercise selected file content, timestamp and link-count changes,
dependency and cache mutations, command changes, symlink/missing paths and
rejection of unknown environment keys. The first focused test run failed
because the missing-directory test expected `OSError` while the existing
cache helper raises `ValueError`; the corrected focused run passed.

Independent read-only finder and skeptic reviews identified missing file
mtime/link metadata and raw command retention; the observer now records the
metadata and stores a command digest rather than raw command data. They also
identified that Lake/Lean dynamically load shared libraries, and root and
Bridge have distinct workspace manifests, packages and builds. Executable
hashes alone do not authenticate the toolchain. Lake may choose an Elan cache
instead of XDG cache; caller-selected trees do not establish actual cache
selection or complete dependency/input coverage. `LEAN_PATH` is refused by
the command allowlist, so the observer cannot represent all resolved import
environments. Sequential snapshots cannot establish simultaneous consistency
or prevent workspace loading and dependency materialization. Paths and labels
in the observation remain visible; its digest is not a confidentiality or
authentication guarantee. No production runner, H56 measurement, bounded
KeySort, runtime gate or Lean proof pass is claimed.

## Explicit XDG observation binding

When the candidate command supplies `XDG_CACHE_HOME`, the selected-path
observer now requires an absolute canonical matching `xdg_cache_home` tree
and fingerprints it. Synthetic controls reject missing, mismatched and
relative bindings, and detect a mutation in the selected tree. Independent
read-only finder and skeptic reviews rechecked the narrow binding without
Lean, a server or builds.

This is not effective-cache authentication: Lake may prefer an Elan
toolchain cache or another configuration, and the HOME fallback when XDG is
absent is not bound. The skeptic also identified that one-pass sequential
tree scans can combine observations of states that never coexisted. A second
sweep would still not establish atomicity and would add cache scanning; it
has not been imposed or benchmarked. Discovery of actual dependency/cache
inputs, their simultaneous authenticated identity, runner integration and
H56 timing remain open. No production, runtime or Lean proof pass is claimed.

## Static root and Bridge input/provenance inventory

This census is a read-only snapshot of tracked files at head
`74732686f3f2e175e26958361534d1c0463c3709` (tree
`624d3edfc15c787fe66cd9539ae46be275bd8c34`), not a runnable or
authenticated H56 inventory. The unchanged candidate mapper counted 7,592
Lean paths: 6,460 root, 527 Bridge, 93 Bridge vendor, 8 root vendor, 495
standalone root review, and 9 standalone Bridge review. It produced 7,088
candidate module rows and 504 file-check-review rows with no module name;
zero candidate `(context, module)` collisions do not establish valid
Lake targets or complete source scope. Ignored/generated files are outside
this tracked census. Decisions for every standalone row and actual execution
recipes remain open.

| Input or resolution | Static evidence and remaining binding |
| --- | --- |
| Root configuration | `lakefile.toml` defines core, examples and optional corpus/check targets plus LeanTeX in `vendor/LeanTeX`; `lake-manifest.json` declares no external packages. Root default targets do not cover every control or check. Bind source, imports, Lake arguments and the actual root workspace. |
| Bridge configuration | `Bridge/lakefile.toml` uses a path dependency on the parent core checkout, direct mathlib, cslib and auto requirements, and selective `vendor` srcDir/globs. `Bridge/lake-manifest.json` has 12 entries including that path and inherited packages; the direct git revisions include mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, cslib `e1fea784d55eae30275c205291f12a1b4868eed3`, and auto `36d85bf6372f1a35fb5487325d1ef965b33c6296`. A manifest pin is not proof of materialized package bytes or imports. |
| Workspace setup | Both toolchain files specify Lean 4.24.0. Before build actions Lake can load configuration and materialize dependencies; overrides, including `.lake/package-overrides.json`, must be bound or their absence established. `--no-build` does not establish that workspace loading is read-only or offline. |
| Outputs and caches | Both packages enable artifact caching. Root and Bridge `.lake/build`, Bridge `.lake/packages`, vendored sources, transitive package configurations and the actually selected shared cache all need provenance and freshness. Lake cache selection gives `LAKE_CACHE_DIR` priority, then an identified Elan toolchain cache, then XDG/HOME fallback. Merely observing XDG does not prove the effective cache. |
| Runtime and imports | Lake builds `LEAN_PATH` and `LEAN_SRC_PATH` from workspace/package paths and augments shared library paths. Executable hashes omit dynamically loaded Lean/Lake libraries and system loader; bind the actual toolchain, runtime, search paths and effective environment as well as source and cache. |
| Timing identity | Lake 4.24's `weakLeanArgs` do not affect build traces; identical artifact traces or replay do not establish the actual weak arguments, thread count or fresh execution. Bind actual command, environment, resource policy, deadline and fresh measurement separately. No claim is made that `LAKE_NO_CACHE` alone forbids local reuse. |

SHA-256 of the six configuration inputs at this snapshot, in root/Bridge
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain` order:
`79e2e18f976dac7010db7ac489fc3a5d90717c682299f76de4583188caa5ab5e`,
`8a441014ff7cad71175d9709ddb59f56cfb2106a0c2e2e19e4b3effb58572abe`,
`42779d67b81608af8a12aa4328d2ab47ca201925b3b2bd68369587b5340bb434`;
`cc6857054608cd99af58b2cc9208df6aeb03e92fc8aeb9bff4b3d99daa5fb236`,
`97bba755b0c4f8bea75d4e69e153ec674a546bdbb4df722359775bd59b7b788d`,
`42779d67b81608af8a12aa4328d2ab47ca201925b3b2bd68369587b5340bb434`.
Hashes identify observed bytes only; they do not authenticate the VM, source
snapshot or runner. Independent read-only finder and skeptic reviewed the
mapping and Lake 4.24 source without Lean, a server or builds. Full reviewed
coverage, atomic source binding, complete runtime provenance, bounded
KeySort and H56 measurements remain outstanding; H93 cold timing remains
deferred. No proof, production or runtime gate pass is claimed.
