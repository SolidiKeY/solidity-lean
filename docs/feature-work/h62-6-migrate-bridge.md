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

The old Bridge package clean measurement is pending. Official release
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

`DEP-H70-01`: the audit-label-execution ticket from requester head
`a107fd353aba492a3144da90cabcbde20032ca0c` is unavailable in this VM. Its verified
host receipt and requested VM delivery path are recorded in the exported
requests/DEP-H70-01.json, with expected 11,017 bytes and SHA256
`4d515bbb0b5de8540c660ccf8c5f0aa5efa3a2f9d502eba8dab5142391ed51f1`.
Coordinator delivery is requested for exact-path read-only triage. Its reported
51 unresolved declaration owners have not been accepted as this lane's producer
scope. relay.sh is host-only and is not a VM installation task.

The audit-precompiles relay from head
`5fcec7dca5ab0d6d321eaf29ca176045b5c38e0c` routes `DEP-BRIDGE-435` to this lane
and precompile-agreement. This VM has frozen v4.24 source dependencies for the
old baseline; approved v4.35 dependencies remain pending. `OBL-SUCCESS` belongs
to G43/V14 and requires a separate actual-compiler success theorem, not a change
to `Solidity.Stipend.Obligation`. Raw String and BLS recursion prerequisites
remain with their named migration owners. Routing grants no original-file
permission, budget change or passing gate; all frozen statements remain intact.

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
the reviewed work items. Do not self-launch a replacement. Inspect the live
measurement before another Lean job or any source/toolchain mutation. Finish
old measurement acceptance, then proof/API migration once root coordination
arrives, new matched measurements, all affected/full gates and new independent
reviews. Escalate any regression and stop above 10 percent slowdown. A partial
checkpoint is not completion of the original four-checkpoint queue.
