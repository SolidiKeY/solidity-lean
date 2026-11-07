# H62/6 Theory migration overlay

Status: **blocked; full assignment unfinished**. Base is
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`; branch is
`codex/solidity-h62-6-20261106/migrate-theory`; checkout is
`/workspace/solidity-lean`. The base was fetched and verified as an ancestor of
fetched `origin/master` (`821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`). The original
clean `work` branch remains at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`.

This is an isolated migration overlay. No live producer ownership transferred.
No production Lean file, tracked toolchain, root, module map, or axiom pin changed.
There was no push, merge, PR, deployment, pre-gate, or freeze announcement.
No existing owned Theory file was edited, so no absent owner reply was treated
as permission. Coordinator requests are saved for pickup; `relay.sh` was not
available on this VM. Optional `get_goal` inspection was not exposed; the
original goal was retained without creating or resetting a goal.

## Checkpoints

| Checkpoint | State | Evidence |
| --- | --- | --- |
| 1: pinned census and clean old build | Done for this directory | 25 assigned modules, 138 external local dependencies; all 163 closure modules passed on v4.24.0. Source command/branch census plus checked-environment declaration/type/axiom baseline exported. |
| 2: identical official v4.35.0 and adaptation | Blocked | Official coordinator archive verified; no assigned new-toolchain module reached because prerequisites fail outside scope. |
| 3: new assigned build and clean comparison | Blocked | Full new probe fails in Syntax.Raw; independent Tuple probe fails in Hash.CollisionBound. Full wall/RSS delta is unavailable, not zero. |
| 4: migration patch and root/gate handoff | Partial | Tooling, test fixtures, source/interface pins, owner requests and reproducible evidence supplied. A validated final migration patch awaits dependencies and all final gates. |

## Toolchains and resources

The coordinator pin is `leanprover/lean4:v4.35.0`, asset
`lean-4.35.0-linux.tar.zst`, SHA-256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
The archive is at
`/workspace/scratch/migrate-theory/toolchains/lean-4.35.0-linux.tar.zst`.
All supplied coordinator input hashes were verified against `sha256.json`.

Actual versions:

- Old: Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Release;
  Lake `5.0.0-src+797c613`.
- New: Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release;
  Lake `5.0.0-src+eb6cafb`.

The VM has four CPU quota cores, a 16 GiB memory cgroup, and no host swap.
Closure probes use one module at a time in dependency order, `LEAN_NUM_THREADS=1`,
explicit `-j1`, `--tstack=131072`, `-M10000`, inherited 12 GiB per-process virtual
address limit, a sampled 12 GiB aggregate RSS stop, and a 4 GiB reserve check on
host and cgroup headroom. RSS is sampled every 250 ms and may miss brief peaks;
it is not an exact OS maximum-RSS measurement or hard aggregate RSS limit.
The no-swap guard checks actual usage; cgroup `memory.swap.max` reports `max`.
No `systemd-run` was used. No heartbeat or recursion budget was raised.

Each closure uses a fresh private `buildDir`, `enableArtifactCache=false`,
`--no-cache`; no per-master v4.24 cache was restored. Private binary selection
leaves tracked `lean-toolchain` unchanged. Root/gate owns its final edit.

## Commands and outcomes

Run these from the checkout. Full command arrays, exits, versions, configuration
hashes, source snapshots and per-file logs are under the evidence root below.

```sh
python3 scripts/h62/item6/migrate-theory/census.py --output /workspace/scratch/migrate-theory/evidence/census.json
python3 tests/h62/item6/migrate-theory/test_census.py -v
python3 scripts/h62/item6/migrate-theory/report.py --inputs /workspace/h62-coordinator-inputs --output /workspace/scratch/migrate-theory/evidence/dependency-report.json
python3 scripts/h62/item6/migrate-theory/api_inventory.py --check-fixture
```

Six scanner controls pass, including nested comments/strings, multiple imports,
anonymous instances, rejected missing project imports, vendor layout, exact
frozen source coverage and deterministic census, and drift-report nonzero exit.
The source census has 661 lexical declaration-command sites and 1,240 branch
lines. It is not a parser-complete generated declaration inventory; the separate
kernel-environment export supplies the complete imported-module inventory.
All 138 external dependencies have migration-owner mappings.

The definitive old closure command (under the writer lock) was:

```sh
python3 scripts/h62/item6/migrate-theory/build.py --toolchain /workspace/.setup/tools/lean-4.24.0-linux --output /workspace/scratch/migrate-theory/evidence/old-final-clean
```

Exit 0, all 163 modules including all 25 assigned modules. Wall: **1,092.930192 s**.
Sampled peak aggregate RSS: **1,726,169,088 bytes (1.61 GiB)**. Source manifests
at start/end match. `Solidity.KeySort` passed with the same bounds. An earlier
pilot was deliberately stopped and excluded from timing acceptance; its logs
and stop record are retained. Exact measured driver source is saved beside its
recorded hash. Later driver changes add modes and reporting; a future paired
comparison must use an identical driver on both sides.

```sh
python3 scripts/h62/item6/migrate-theory/build.py --toolchain /workspace/scratch/migrate-theory/toolchains/lean-4.35.0-linux --output /workspace/scratch/migrate-theory/evidence/new-final-clean
python3 scripts/h62/item6/migrate-theory/build.py --toolchain /workspace/scratch/migrate-theory/toolchains/lean-4.35.0-linux --output /workspace/scratch/migrate-theory/evidence/new-tuple-clean --target Solidity.Theory.Progress.Tuple
```

Both exit 1 at external prerequisites. The new KeySort prerequisite passed;
this is not a full runtime gate. Both failed probes record matching ending
source snapshots. No assigned Theory module compiled on the new toolchain.

The API introspection fixture ran on v4.24.0 with explicit
`LEAN_PATH=/workspace/scratch/migrate-theory/evidence/old-final-clean/build/lib/lean`.
It passed in 86.81 s and exported 25 module headers, 2,264 declarations (including
private/generated declarations, constructors and recursors), their exact raw
`Lean.Expr` type representations, universe parameters, and transitive axiom
closures. The union is exactly `Classical.choice`, `Quot.sound`, `propext`.
Canonical extraction reproduces byte-for-byte. Per-declaration interface hashes
are versioned raw-expression hashes, not a cross-version equivalence proof.
Whole-source SHA-256 pins also conservatively freeze all statements and proofs.
Source `sorry`/`axiom`/`native_decide` counts in the 25 assigned files are all zero.

Fixture runs are **replays**, not clean directory timing measurements. They
import bundled Lean libraries; API introspection additionally imports the old
baseline oleans. Original generic cache labels are corrected by the supplemental
`fixture-provenance.json`, which records the explicit import path and hashes of
all imported baseline oleans. Future driver results distinguish modes and record
`effective_LEAN_PATH` directly. Supplemental provenance was captured after the
run, not as a contemporaneous imported-artifact snapshot.

## Scoped backfill and proof boundary

`StringBoundaryWitness.lean` proves five finite Unicode/empty/overdrop character
cases on both official binaries (exit 0 each). These are ordinary `decide`
proofs, with no native evaluation shortcut. They do not prove production
function equivalence. `LegacyStringApiRepro.lean` passes on old Lean and fails on
new Lean with four specifically checked API diagnostics: slice result type,
missing slice `toList`, missing String `dropRight`, and polymorphic `endsWith`
eta shape. That negative fixture is intentionally excluded from library roots.

An additional, uncommitted positive-suffix experiment did **not** prove its
statement. Its initial source and failed attempts are off-Git artifacts, not
repository modules. The historical artifact locator is recorded in the
[complete work/backfill queue](../../tests/h62/item6/migrate-theory/h82-handoff/complete-work-backfill-queue.json);
those artifact bytes have not been recovered or revalidated here. It is excluded
from accepted coverage, is not a replacement or weakening of a frozen theorem,
and is not claimed successful. No original Theory statement changed.

The three delivered Lean fixtures live only under the assigned tests directory.
No production-module registration is requested. The API generator is committed;
59 MB raw introspection output and other bulk evidence remain off git with hashes.
No new API interface, proof, or trust-policy change is introduced into the core.

## Typed dependency blockers and escalation

- `DEP-SYNTAX-RAW-435`: `migrate-syntax` owns `Solidity/Syntax/Raw.lean`.
  Errors at 597, 650, 665, 682, 684 reflect String/Slice API and pattern changes.
  This dependency blocks 24 assigned files.
- `DEP-HASH-COLLISIONBOUND-435`: `migrate-hash` owns
  `Solidity/Hash/CollisionBound.lean`. Proof failures at 407, 660, 680 and
  diagnostic pins at 950, 953, 956, 959, 962, 968 fail on v4.35. This blocks
  seven assigned files, including the otherwise independent Tuple target.
- `PERF-KEYSORT-WALL-435`: KeySort prerequisite wall increased from 1.511297 s
  to 2.013636 s (33.24%). This incomplete prefix used different reporting
  revisions and does not establish the full comparison. **Further migration
  Lean runs are held for root/gate review** under the >10% STOP rule. No
  performance acceptance or threshold waiver is claimed.
- `PERF-PREFIX-RSS-435`: passing prerequisite modules show increased sampled RSS;
  root/gate must review `prefix-metrics.json`. These incomplete prefixes do not
  establish a full migration timing delta. Any regression must be escalated;
  **STOP if the full wall slowdown exceeds 10%**.

The union of the first two dependency blocker sets covers all 25 assigned files.
Exact-file requests, owner keys, paths, logs and required actions are in
`owner-requests.json`; no owner response or repair overlay has arrived. Existing
out-of-scope originals remain read only. No H55 producer work was duplicated.

## Reviews, artifacts and resume

Independent finder and skeptic reviews used no Lean server and made no edits.
Confirmed findings were fixed: anonymous instances and missing-import handling,
vendor resolution, drift failure exit, source/configuration snapshots, bounded
termination, fixture provenance/cache labels and both owner requests. Full
review receipts and resolutions are in `reviews.json`.

Absolute artifact root: `/workspace/scratch/migrate-theory`.

- Evidence: `/workspace/scratch/migrate-theory/evidence`.
- Original patch: `/workspace/scratch/migrate-theory/original.patch`.
- Bundle: `/workspace/scratch/migrate-theory/migration.bundle`.
- Handoff (full committed head): `/workspace/scratch/migrate-theory/handoff.md`.
- Checksums: `/workspace/scratch/migrate-theory/SHA256SUMS`.

After root/gate resolves the performance stop and reviewed owner overlays are
received at this pinned base, rerun all assigned
modules serially with the identical pinned v4.35 archive. Coordinate exact Theory
files before any existing-file edits. Preserve signatures, semantics, observations
and proof budgets; warn and inspect history before a potentially slower refactor.
Recheck complete new API/axiom inventories, frozen source/type compatibility,
all affected consumers and repository-required `./run-lean.sh`, then measure
clean before/after with identical driver/resources/cache policy. The final full
gate and full KeySort checker remain pending; **no RUNTIME_GATE_PASS** is claimed.
The root lane alone owns final toolchain cut-over and integration.

Continue the same original persistent goal on this VM
`ccarenv_b64_Y2NhcmVudl85ZGQyODU3NzBlYjg4MTkxYmJjYjgyNGQxNGYyODcxMw`.
This is a fresh-thread handoff to the coordinator, not a new/replacement goal.
The entire assignment must remain unfinished until all four checkpoints pass.


## H82 retirement preservation checkpoint

Human-approved stop-and-handoff and its ordering correction retire this worker.
No new proof implementation or Lean run is performed. The successor is
`solidity-h62-6-20261106/migrate-root-gate`, responsible for integration after the
final stopped/head acknowledgement. Existing goal is explicitly requested PAUSED,
but the exposed goal API has no pause operation; `stop_goal` accepts only complete
or blocked. No substitute completion/reset/transition is attempted. Exact capability
failure is recorded in the committed handoff. No automatic implementation
continuation is authorized by retirement. The coordinator explicitly resolved
Q-H82-RETIRE: KEEP RETIREMENT/HANDOFF; generic broadcasts and tickets do not
revoke it. Coordinator will set the existing goal paused after final head report
and idle turn. No human decision is needed.

The complete original assignment and goal text, exact scope, all work/backfill
items and waits, current policy/ordering messages, latest root request and source
hashes are committed under `tests/h62/item6/migrate-theory/h82-handoff/`. Read its
README and HANDOFF-SOURCES.sha256 before successor work. Launcher rendering digest
is retained as provenance; actual transcription file hashes are separate.

Current H82 standing agreements supersede the earlier exact-file protocol in
this historical document for statement-preserving proof/additive/split/import/doc
edits. Existing statement/depended-on definition/signature/budget/axiom/exclusion
changes still need owner, with H57 versioned frozen pairs. No proof-only permission
wait is retained. Retirement and performance holds still prohibit implementation
here. H78 complete original public generated API/shim requirements remain open;
the old inventory alone does not establish visibility or old/new compatibility.

No H71 original-branch push permission was supplied, so no push is performed.
The cumulative patch, bundle, portable archive and final hashes are saved under
`/workspace/scratch/migrate-theory/h82-retirement/`. Historical H44 evidence and
all VM/branch artifacts are preserved. No Claude-owned edits or messages occur.
