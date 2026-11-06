# H62 item 6: Bridge migration overlay

Owner: `solidity-h62-6-20261106/migrate-bridge`.
Branch: `codex/solidity-h62-6-20261106/migrate-bridge`.
Exact base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Checkout: `/workspace/migrate-bridge` (separate worktree).
The older `/workspace/solidity-lean` checkout remains intact.

## State and boundaries

The migration remains incomplete. No original Lean source, generated root,
module map, axiom pin, dependency manifest or toolchain pin changed. The census
covers 629 unchanged original Bridge Lean files, preserving their bytes and
cases at this checkpoint. It is not an elaborated declaration audit or v4.35
semantic acceptance. Zero Lean helpers, axioms, sorry, frozen-statement changes,
trust shortcuts or raised proof budgets were introduced. Core remains intrinsic
and dependency-free. No push, merge, PR, pre-gate or publication occurred.

The old Bridge package clean measurement remains incomplete after a resource
stop in attempt 5. Official release
provisioning and both KeySort prerequisites passed. Proof/API migration,
new clean measurements, affected validation and full final gates are pending.
No RUNTIME_GATE_PASS or actual before/after timing delta exists.

## Official toolchain

All five coordinator input hashes in `/workspace/h62-coordinator-inputs`
matched the supplied `sha256.json`. The exact release is
`leanprover/lean4:v4.35.0`, asset `lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
It is downloaded and extracted under
`/workspace/h62-migrate-bridge-evidence/toolchains`.

- Old: Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
  Lake `5.0.0-src+797c613`.
- New: Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
  Lake `5.0.0-src+eb6cafb`.

Both compilers returned exit 0 on `Solidity/KeySort.lean` with
`LEAN_NUM_THREADS=1`, `-j1`, and `--tstack=131072`. Standalone old/new probes
used `-M3072`/`-M10240`; these are prerequisites, not comparable timing samples.

## Measurement and final-gate commands

`run-bounded.py --bridge-measurement` invokes the existing
`bash ./scripts/check-bridge.sh` for directory measurements. Pass absolute
`--root`, `--toolchain`, `--evidence` and `--solkey-rules` arguments. The latter
is retained for the mandatory full gate. Without the measurement flag the
runner invokes `bash ./run-lean.sh --bridge`; this full final gate remains
required after migration. A Bridge-only receipt never establishes that gate.

The runner holds the repository writer lock, refuses existing root/Bridge and
dependency Lean library outputs and nonempty evidence directories, disables Lake
artifact/download caches, serializes Lean `-j1 -M10240`, requires zero host
swap, bounds each compiler to 300 seconds, and preserves 4 GiB of host and VM
headroom under the explicit assignment's reserve. The VM cap is 16 GiB; CPU
quota is four cores with five visible CPUs. No systemd-run is used. A
`command-pass` receipt remains subject to independent decisive-output review.
Only prepared ProofWidgets JavaScript is permitted in a dependency build tree:
real directories, regular `.js` files and exact top-level `js/lake.trace`.
Symlinks, Lean artifacts, IR and unknown files are rejected. The JS prerequisite
is required before a Bridge measurement, and this cold-library/JS-only policy
is included in timing receipts and comparisons. Package configuration and
non-Lean asset setup are performed before the measurement; library proof outputs
are cold. Ten negative controls exercise this preflight separately.

The first three preliminary commands included full core targets before Bridge.
A static source-import estimate found 784 core modules in Bridge's closure
versus 6,385 core source modules overall. The old directory measurement was
corrected to the package target; the final full gate was retained. Preliminary
runs are preserved and are not accepted clean Bridge measurements:

- Attempt 1: stopped for a reviewed timeout-group cleanup defect, exit -15,
  81.05 seconds. The defect was fixed before further checks.
- Attempt 2: VM reserve guard stopped core
  `Solidity/Backend/Scalar/PowerBounds.lean` after 1,178.6967 seconds. Preserve
  both runner and external-watchdog receipts; this was not a theorem failure.
- Attempt 3: unchanged `PowerBounds` passed in 237 seconds after cache recovery;
  full preliminary command was intentionally stopped for scope correction,
  exit -15 after 1,966.2415 seconds. It is not a completed final gate.
- Bridge attempt 4: missing ProofWidgets JS prerequisite caused a real target
  failure. The invalid run was stopped, exit -15 after 1,874.2515 seconds;
  its partial Lean outputs cannot be reused in a clean measurement.
- Bridge attempt 5: the 4 GiB reserve guard stopped the active
  `Solidity/Backend/Scalar/PowerBounds.lean` compiler. The runner exited 1;
  the child command exited -15 after 7,028.575882715 seconds, with peak VM
  usage 12,911,218,688 bytes. Receipt status is `fail`. No accepted timing or
  theorem failure follows. No live runner/compiler remains; two exited
  wrapper zombies await PID 1 reaping. Failed partial outputs remain preserved
  in their original owned build trees and must not be reused as a clean run.

`PowerBounds` is in Bridge's import closure. The earlier full-core commands
were overbroad, but this particular dependency cannot be excluded. The exact
local chain is `SolidityBridge` →
`SolidityBridge.RoadmapV15.P10.SignedDivisionConsumer` →
`Solidity.Backend.Scalar.SignedMul` →
`Solidity.Backend.Scalar.PowerGuard` →
`Solidity.Backend.Scalar.PowerBounds`. The runner and source remained unchanged
through attempt 5. Its source was last modified before the attempt started.

Unused owned v4.35 release-file cache was advised away via read-only file
handles, reducing VM usage from 4.95 GB to 1.05 GB. No contents were changed or
deleted and no proof/resource limit was raised. Cache-release accounting and
failed/preliminary products remain off git. Document unused-cache handling
symmetrically for final before/after conditions.

Eleven dependency source checkouts were provisioned at the exact revisions
already in the base Bridge manifest, with no compiled cache or pin changes.
Source-fetch setup is excluded from the timed build. Commands and revision
equality checks are in old/pinned-source-preparation.log and its JSON receipt.
Migration dependency selection and cross-directory prerequisites still require
root/gate coordination.

The first standalone pinned ProofWidgets JS target attempt failed its guard.
Standard standalone `lake --reconfigure --no-cache
-d <proofwidgets> build widgetJsAll` then succeeded in 57.04 seconds with clean
source status and no imported Lean library cache. The original Bridge-context
`proofwidgets/widgetJsAll` prerequisite also passed afterward. No Mathlib or
ProofWidgets source/guard was edited or disabled. The JS-only target is the
pinned deterministic generator; generated assets and checksum evidence stay
off git. All partial library outputs from attempt 4 are preserved outside the
new clean build. This prerequisite success is not Bridge semantic acceptance.

## Deterministic acceptance backfill

`census.py --require-unchanged` compares baseline bytes with current indexed
Bridge Lean paths, including staged additions and working-tree deletions. Its
bulk JSON stays off git. Five controls cover comparison and real Git/CLI
success/failure behavior. Deterministic repeated outputs matched.

`compare-timings.py --old <directory> --new <directory>` rejects incomplete,
interrupted and malformed receipts, mismatched command/scope/resource/cache/
rules profiles, unexpected versions and invalid durations. Historical attempt
2 also requires its external-watchdog receipt; current runners use the built-in
guard. Scope and command are included in exported comparison JSON. Exact
rational arithmetic returns exit 3 for positive slowdown up to 10 percent,
exit 4 strictly above 10 percent, exit 0 for no slowdown, and exit 2 when
blocked. No exit certifies proof or full-gate acceptance. Eighteen synthetic
controls passed, including exact thresholds and cross-scope rejection.

## Independent review and checks

Finder and skeptic worked independently, read-only, without Lean servers or
fixes. Confirmed findings were fixed: staged additions/deletions, process-group
cleanup, stale sysroot reuse, clean dependency outputs, SolKey skip handling,
VM headroom, incomplete/malformed receipts, invalid equal profiles, threshold
rounding and exported scope labels. The JS-only blacklist was replaced by a strict
allowlist after both reviewers identified IR/unknown-file acceptance. Final code
reviews found no remaining blockers; final proof/build milestone reviews remain outstanding. Review text
is preserved in versioned off-git checkpoint exports.

Layer and whitespace checks passed. Documentation-path checks initially failed
because an unchanged existing document referenced a missing downloaded mathlib
test source. After exact pinned source provisioning, the path gate passed: every backticked
Lean-file reference resolves. The out-of-scope document was not edited and no
placeholder file was fabricated.

## Incoming H70 requests

Latest incoming tickets are saved byte-identically to the coordinator hashes:

- Label-execution head `d89b309029f9ad57f17711432aeef4990005994b`, ticket
  SHA256 `5f63fe1a9f15bdd857e4bd601f59a36886cc06477474bcbf80bedf6ce2cc6c3d`.
  Its six non-Bridge prerequisites remain with their named migration owners;
  B07 is the common Bridge dependency request. The older DEP-H70-01 file
  delivery request is superseded and inactive.
- Audit-precompiles head `13ae4273bad4123baea9347dfa724ded432dfd57`, ticket
  SHA256 `952fa62cf764b457877c5c511c16d828fbef1761201d6af31628abd1e7d5290c`.
  DEP-BRIDGE-435 is routed to this lane and precompile-agreement. Its full
  20,624-byte handoff still needs coordinator delivery; exact host/VM paths
  and SHA256 are in the exported DEP-H70-PRECOMPILES-HANDOFF request.

OBL-SUCCESS remains G43/V14's separate actual-compiler success theorem; no
change to `Solidity.Stipend.Obligation` is requested or authorized. Raw String
and BLS recursion prerequisites stay with their named owners. Routing grants
no source permission, proof-budget change or passing-gate claim. relay.sh is
host-only and is not a VM installation task.

## Concrete unapplied dependency proposal

COORD-BRIDGE-435 supplies a reviewable proposal for exactly
`Bridge/lakefile.toml` and `Bridge/lake-manifest.json`, saved off git under
`/workspace/h62-migrate-bridge-evidence/proposals/v4.35.0-common-deps`.
The dependency-only patch SHA256 is
`ee61b53ebe5cd46688c8a986dcaebf3e8172b0d5f07e16aa3b835f928c8ab832`.
Exact official v4.35.0 tag receipts bind:

- Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`;
- CSLib `5b56df99362532c46e1175381fbbdd755bd56030`;
- Auto `30f46ddb9a68d6878f5a1337eb2565ba4e70126b`.

The upstream toolchains match v4.35.0 and shared transitive revisions agree.
Independent finder/skeptic metadata reviews passed. This is unapplied,
unelaborated metadata, not API acceptance or original-file agreement. Draft
warning-suppression flags were removed. New Auto declares a versioned solver
asset without a content-digest check; provenance and its non-proof-asset setup
policy remain pending. No solver binary was downloaded or run. Selected old
Loom examples use the default `grind`, with no source SMT override found.

## Dependencies and continuation

`DEP-ROOT-01` [proof/API migration and new gates]: root/gate must supply the
approved v4.35 core overlay, dependency decisions/artifacts and exact-file
coordination receipt. No relay.sh, published migration branch or reply was
available. Root owns toolchain edits and V15 owns live producer work. Absent
replies grant no permission. No existing producer has been edited or claimed,
and no H55 work duplicated.

Continue the same persistent goal and VM. No new/reset/completed goal or
replacement thread was created. get_goal is unavailable; coordinator explicitly
waived that optional inspection. Coordinator owns fresh-thread handoff after
the reviewed work items. Do not self-launch a replacement. Inspect saved
receipts and process state before another Lean job or source/toolchain mutation.
Resolve the failed old measurement under unchanged limits, then perform proof/API
migration once root coordination arrives, new matched measurements, all
affected/full gates and new independent reviews. Escalate any regression and
stop above 10 percent slowdown. A partial checkpoint is not completion of the
original four-checkpoint queue.

`RESOURCE-OLD-01` [old clean measurement]: root/gate and migrate-backend must
coordinate a reviewed within-budget recovery for the observed PowerBounds
reserve stop. After termination the VM had about 4.31 GB file cache versus
42 MB anonymous memory. Advisory eviction of only owned, unused artifact pages
is a plausible experiment, not a validated fix. A module-boundary policy must
be deterministic, included in elapsed time, reviewed, and identical for old/new
measurements. Clearing initial cache alone may repeat growth before this file.
No global drop_caches, larger cap, lower reserve, partial-output clean reuse,
statement change, omitted dependency or proof-budget increase is authorized by
this report. Keep failed evidence. No automatic retry with the same conditions
was launched. This file belongs to the backend owner and remains read-only here.

Final attempt-5 finder and skeptic reviews independently confirmed the resource
failure, cleanup and actual import chain. They found no basis for a passing
timing, theorem-failure conclusion, exclusion or regression waiver. Both were
read-only and used no Lean server. Their complete results and corrected handoff
are preserved in the new versioned evidence export. The persistent goal must
remain unfinished; request root/dependency/resource delivery before resuming.


## H82 retirement handoff

Human stop-and-handoff instruction names
`solidity-h62-6-20261106/migrate-root-gate` as survivor. No new implementation
or proof checking follows that instruction. A later general H82 message says
"Continue now"; Q-H82-RETIRE requested clarification without resuming work.
The coordinator explicitly resolved KEEP RETIREMENT AND HANDOFF; generic
broadcasts do not revoke this lane-specific stop. The question is closed.
No new goal, VM, replacement continuation or completed-goal claim is created.

The exposed goal tool accepts only complete/blocked, with no PAUSED action.
Report this precise limitation and use a blocked stop to suppress automatic
continuation; do not describe the tool state as successfully PAUSED. H71 push
permission was not supplied, so preserve the original no-push restriction and
export a cumulative patch plus portable lane bundle. The coordinator will set
the existing goal PAUSED after the final head report and idle turn. No
Claude-owned source edits or messages occur.

H82 withdraws blanket exact-file agreement requirements for statement-preserving
proof-only/additive/import/doc work. Earlier handoff permission language is
historical and superseded for those edits. Existing-statement/definition-body/
interface/budget/axiom/exclusion changes retain owner/H57 requirements. The
common root/dependency overlay and actual resource waits remain unresolved.

The retirement files under `tests/h62/item6/migrate-bridge/retirement/` preserve
the exact original frozen rendering, separate first-user wrapper transcription,
complete original work/backfill queues and exact 836-entry pinned scope.
After correcting three owner-key transcription errors and restoring the original
rendering, the frozen prompt exactly matches launcher SHA256
`7456740aae294bbb28be3e1b5806b783646bfbddeed942fd01137d0562faf014`.
The earlier mismatch/delivery wait is resolved; provenance records the match.
Existing old/new full public generated API exports and shim records are absent;
implemented shims remain empty. All four original checkpoint outcomes, backfill
items and schema-v1 waits are recorded, with no full migration acceptance.
