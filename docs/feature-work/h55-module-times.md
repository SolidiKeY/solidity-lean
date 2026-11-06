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
