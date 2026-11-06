# H62 item 6: Bridge migration overlay

Owner: `solidity-h62-6-20261106/migrate-bridge`.
Branch: `codex/solidity-h62-6-20261106/migrate-bridge`.
Exact base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Checkout: `/workspace/migrate-bridge` (separate worktree).
The older `/workspace/solidity-lean` checkout remains intact.

## State and scope

This is an incomplete migration checkpoint. No Lean source, generated root,
module map, axiom pin, dependency manifest or toolchain pin has changed.
All 629 original tracked Bridge Lean files have an unchanged byte census.
This preserves their declarations and cases at this checkpoint; it does not
establish v4.35 elaboration, declaration inventory completeness or semantic
acceptance. There are zero introduced Lean helpers, axioms, sorry or frozen
statement changes. No proof budget, premise, exclusion or observation changed.
Core remains dependency-free. No push, merge, publication or PR occurred.

The old full clean gate is running as attempt 3 in a bounded serial session. Its completion
and old Bridge clean measurement remain pending. Official release provisioning
and both KeySort prerequisites passed; proof/API migration and new full gates
remain pending. No RUNTIME_GATE_PASS or slowdown claim is made.

## Official toolchain

Coordinator inputs in `/workspace/h62-coordinator-inputs` passed all five
hashes from their supplied `sha256.json`. The exact release is
`leanprover/lean4:v4.35.0`, asset `lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
It is downloaded and extracted under
`/workspace/h62-migrate-bridge-evidence/toolchains`. Actual versions:

- Old: Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
  Lake `5.0.0-src+797c613`.
- New: Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
  Lake `5.0.0-src+eb6cafb`.

Both compilers returned exit 0 on `Solidity/KeySort.lean` with
`LEAN_NUM_THREADS=1`, `-j1`, and `--tstack=131072`. Old standalone probe used
`-M3072`; new used `-M10240`. These standalone probes are prerequisites,
not full builds or comparable timing samples.

## Reproduction and boundaries

`python3 scripts/h62/item6/migrate-bridge/census.py --require-unchanged`
compares baseline source bytes with current indexed Bridge Lean paths, retaining
working-tree deletions as removals. Its JSON is bulk evidence kept off git.
`python3 tests/h62/item6/migrate-bridge/test_census.py` exercises unchanged,
added, changed and removed rows plus real Git discovery and CLI exit controls.

`run-bounded.py` invokes `bash ./run-lean.sh --bridge` under the repository
writer lock. Pass absolute `--root`, `--toolchain`, `--evidence` and
`--solkey-rules` arguments. It refuses nonempty evidence and existing build
outputs in root, Bridge and downloaded dependency packages; disables Lake
artifact/download caches; serializes compiler calls; supplies Lean `-j1
-M10240`; bounds each compiler to 300 seconds; requires zero host swap; and
preserves 4 GiB host/VM headroom, following the explicit assignment's VM reserve.
The VM has a 16 GiB cgroup cap. No systemd-run was used.
A `command-pass` receipt is subject to decisive-output review, including the
SolKey result, affected Bridge coverage and full assigned gates. No proof trust
follows merely from a runner label.

The first old attempt was stopped after independent review found timeout group
cleanup unsafe. It returned -15 after 81.05 seconds and is not a valid clean
measurement. Its outputs are preserved outside git. Attempt 2 ran for
1,178.6967 seconds before the VM-headroom watchdog stopped it in core module
`Solidity/Backend/Scalar/PowerBounds.lean`. Its runner receipt and independent
watchdog receipt are both preserved under old/clean-build-2; this is a failed
resource gate, not a clean timing result or a theorem failure.

After stopping, cgroup accounting showed 4.58 GB of file cache. Advisory eviction
of only this worker's unused downloaded v4.35 archive/extraction pages reduced VM
usage from 4.95 GB to 1.05 GB. Files were opened read-only; no contents were
changed or deleted, and no proof/resource limit was raised. The operation and
counts are saved as old/cache-release.json. Failed attempt 2 build products
were preserved separately before restarting.

Attempt 3 is the active old clean gate at
`/workspace/h62-migrate-bridge-evidence/old/clean-build-3`, using the reviewed
runner's built-in host and VM guards, the same Lean `-j1 -M10240`, 300-second
module limit and 4 GiB reserve. This provisioning retry has not passed. No
Bridge dependency package directory existed at its clean start. Do not restart
or accept it without inspecting the live process, starting state, receipt and
log. Final before/after timing must use matching clean artifact/cache/resource
conditions, with unused release-cache handling documented symmetrically.

## Independent review

Finder and skeptic worked read-only, without Lean servers or fixes. Both found
that the first census omitted staged additions. Finder also identified deletion
reporting. These were fixed and covered by actual Git/CLI negative controls.
Both found timeout process-group cleanup could leak Lean processes; finder
found stale sysroot reuse and dependency-cache measurement gaps; skeptic found
SolKey skip, clean-tree and VM-headroom risks. All reported code findings were
fixed. Their final checks confirm the fixes, real compiler `-j1 -M10240`, and
attempt 2's separate watchdog. Final build acceptance and any proof edits need their own
milestone reviews. Full review text is exported in off-git `reviews.md`.

## Non-Lean checkpoint checks

The census controls passed (five tests), deterministic repeated census outputs
matched, and the layer check passed. The documentation-path gate returned exit
1 because an existing document cites a missing downloaded mathlib test source:
`docs/feature-work/after-roadmap-va1.md`, reference into
Bridge/.lake/packages/mathlib/MathlibTest/SplitIfs.lean. That document is
byte-identical to the pinned base; Bridge dependency packages have not been
provisioned in this clean worktree. This is a pending dependency gate, not a
passing check, and its citing document is outside this lane's scope. Do not
change the document or manufacture the dependency path to silence this result.

## Timing comparison backfill

`compare-timings.py --old <run-directory> --new <run-directory>` requires
completed bounded-run receipts, matching explicit command/resource/cache/rules
profiles, expected actual Lean/Lake versions, finite positive durations, and a
completed independent watchdog receipt for historical attempt 2, whose saved
launched-source marker selects that requirement. Attempt 3 uses its built-in
guard and runner receipt. Missing,
interrupted or malformed evidence returns structured `blocked` output and exit
2. The actual current comparison returns this pending state because the old
build has not finished; it does not produce an estimated timing delta.

Classification uses exact rational arithmetic: any positive slowdown returns
`escalate`/exit 3, strictly above 10 percent returns `stop`/exit 4, and no
slowdown returns exit 0. Exactly 10 percent still requires escalation. These
exits describe timings and never establish theorem or full-gate acceptance.
Fifteen synthetic controls passed, including incomplete watchdogs, equally
invalid profiles, malformed receipt objects, interrupted builds and a slowdown
infinitesimally above the threshold. These fixtures are external tooling tests,
not Lean measurements or proofs.

Independent finder and skeptic reviews found missing-field/profile checks and
rounding at the strict threshold. All confirmed findings were fixed; final
read-only reviews report none remaining. Their timing review evidence is saved
with the next versioned checkpoint artifact export. Full build/proof milestone
reviews remain outstanding.

## Dependencies and next work

`DEP-ROOT-01` (migration root/gate): provide the authorized v4.35 core overlay,
shared dependency decisions/artifacts and exact-file coordination receipt.
No relay.sh or published migration branch was available in this VM. Existing
Bridge pins still target v4.24 mathlib/CSLib/auto. Root owns toolchain edits;
V15 owns live producer work. No existing producer file has been edited or
claimed, and absent coordination replies grant no permission.

Continue the same persistent goal; no replacement goal was created. The reviewed
backfill milestones are ready for coordinator-owned fresh-thread handoff; do
not self-launch a replacement thread or goal. Goal tool
inspection was unavailable and the coordinator explicitly waived that optional
inspection. Inspect the running old gate, finish its measurement and acceptance,
then resume proof migration once the dependency/ownership receipt arrives.
Run all affected validations and full assigned gates, obtain new independent
reviews, measure new clean builds with matching resources/cache conditions,
escalate any regression and stop above 10 percent slowdown. No comparison is
possible yet. Do not merge, pre-gate or publish. Preserve this VM and branch.

The exported handoff records committed head, patch paths, evidence snapshots,
checksums, active process IDs and pending obligations. A partial report is not
completion of the four-checkpoint queue.
