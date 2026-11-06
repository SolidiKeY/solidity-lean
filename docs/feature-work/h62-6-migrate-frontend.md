# H62 item 6: Frontend migration overlay

Owner: `solidity-h62-6-20261106/migrate-frontend`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-6-20261106/migrate-frontend`.
Checkout: `/workspace/solidity-h62-migrate-frontend`.
Evidence: `/workspace/h62-migrate-frontend-evidence` (bulk files outside Git).

Status: partial. Checkpoint 1 now has a passing clean old build and complete
elaborated environment census; checkpoints 2–4 remain open until their
required build, review, compatibility and timing gates pass. No runtime-gate
pass, migration completion, producer ownership transfer, cut-over, root edit,
push or merge is claimed.

## Census tooling checkpoint

The exact ownership snapshot covers 492 files: 490 Lean modules and two
registration files. Their local transitive import closure is 984 modules,
including 494 outside Frontend. There are 114 direct cross-directory edges
and 79 distinct direct external imports. The scanner records 7,576 lexical
declaration candidates; these are not qualified elaborated declarations,
complete command coverage or a proof of API compatibility. Whole-source
SHA256 pins cover every assigned file and every local closure module.
The only Frontend `set_option` found is the existing `smartUnfolding false`.

Generator and control commands, run from this checkout:

```sh
python3 scripts/h62/item6/migrate-frontend/census.py --out /workspace/h62-migrate-frontend-evidence/census
python3 -m unittest discover -s tests/h62/item6/migrate-frontend -v
```

The generator verifies every supplied coordinator input against
`/workspace/h62-coordinator-inputs/sha256.json`, checks exact ownership equality,
and fails on import cycles. The ten controls pass, including nested comments,
string/character masking, whitespace, false import lines, scope mismatch,
cycles, external dependency closure, interrupted process cleanup, failed
spawning and insufficient headroom. These are external Python/OS tests, not
Lean proofs. No new Lean declarations, axioms, `sorry`, `native_decide`,
heartbeats, semantic exclusions or premises have been introduced.

## Toolchain and reproducible measurement setup

The official `lean-4.35.0-linux.tar.zst` archive has SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`, matching
coordinator `toolchain-pin.json`. Lean reports 4.35.0, release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake reports
`5.0.0-src+eb6cafb (Lean version 4.35.0)`.

The installed official 4.24.0 archive has SHA256
`b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec`.
Lean reports 4.24.0, release commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake reports
`5.0.0-src+797c613 (Lean version 4.24.0)`.

`measure.py` requires a fresh output directory, verifies all recorded source
hashes, disables Lake artifact caching and cache downloads, writes an off-Git
private Lake configuration with a fresh absolute build directory and `-j1`,
and runs one target at a time in dependency order. It pins one CPU, sets
`LEAN_NUM_THREADS=1`, `-j1` and `-DElab.async=false`, verifies no host swap,
retains the supplied 16 GiB hard VM cgroup bound, monitors aggregate RSS
with a 12 GiB sampled stop threshold and requires at least 4 GiB of
host/cgroup headroom. Runtime thread counts are sampled separately; the
configured Lean worker count is not an observed OS-thread count. Its 0.1-second sampled aggregate RSS is not an exact
kernel peak. Signal/error cleanup kills only its own build process group.
OS page cache is uncontrolled and explicitly recorded. No `systemd-run` is used.
No tracked toolchain or root Lake configuration is changed. RSS and reserve
guards are sampled controls, not hard cgroup guarantees.

A first old KeySort probe was deliberately stopped because its initial
`--only` selection included unrelated modules. It is retained under
`old-keysort/` as failed probe evidence, excluded from baseline results.
The corrected old KeySort prerequisite passed (one target, exit 0) under
`old-keysort-corrected/`; v4.35.0 prerequisite evidence is `new-keysort/`.
These module builds do not substitute for the full SolKey checker or final gate.

## Independent reviews

Read-only finder `finder_census` independently verified 492 source hashes,
exact ownership equality and topological ordering. It found overbroad KeySort
selection and quote-character masking. Both are fixed and re-reviewed.

Read-only skeptic `skeptic_census` found interruption/cleanup holes, missing
pre-command failure evidence, absent external dependency/config provenance,
unchecked swap metadata and tab-separated import handling. All material
findings are fixed, covered by controls and confirmed on final re-review.
Neither reviewer used Lean or a language server. Their reviews establish
only this tooling checkpoint; later migration milestones need fresh reviews.

## Remaining obligations and coordination

1. Old clean build and baseline environment census completed below. Preserve
   these exact settings for new-toolchain comparison.
2. Complete v4.35.0 compatibility and preserve exact types, semantics, proof
   budgets and frozen interfaces. Out-of-scope dependencies require their owners.
3. Complete all assigned modules on v4.35.0, matched clean measurements,
   acceptance, final repository gate and reviews. Any regression escalates;
   slowdown above 10 percent stops migration.
4. Export the reviewable committed overlay patch/bundle, handoff, exact hashes
   and cross-directory dependency report to the root migration gate.

No coordinator `relay.sh` is present in the repository or discovered setup.
Existing Frontend originals remain untouched pending exact-file coordination.
No scope expansion is inferred from the migration overlay exception.
No second persistent goal has been created; get_goal is not exposed here,
which the coordinator explicitly confirmed is not a blocker.

## Resource-method correction checkpoint

The first clean old run (`old-clean/measurement.json`) failed, not passed:
83 successful closure modules (60 Frontend), then UnitExamples failed with
`failed to create thread`, Lean exit 134, Lake exit 1. Attempt wall time
343.604841 seconds; sampled peak group RSS 2,539,126,784 bytes. This is not
a complete clean baseline and provides no migration timing delta.

The initial harness added a 12 GiB virtual-address limit. That was inappropriate
for Lean's large thread stack reservations (the repository warns that virtual
reservations are not resident RAM). The same module without that extra limit
reserved 28,103,172,096 virtual bytes and reached 7,704,879,104 sampled RSS bytes,
but hit the conservative 4 GiB headroom guard after 100.614966 seconds; no proof
verdict was obtained. Both diagnostic attempts are retained and excluded from
baseline comparisons. The VM had no cgroup OOM/max events and no swap.

A separate private diagnostic with `-DElab.async=false` passed UnitExamples,
exit 0, in 120.735350 seconds, sampled RSS 1,716,277,248 bytes, virtual size
5,676,617,728 bytes, 12 maximum sampled group threads. Source, proof budgets,
CPU affinity and kernel checking were preserved. This diagnostic reused built
dependencies and is explicitly not a clean baseline. Both official releases
support this scheduling option; it avoids retaining many simultaneous theorem
elaborations despite the single configured Lean worker. Future old/new clean
measurements use identical revised settings and fresh build directories.

Read-only finder confirmed proc-stat indexing and owned-group cleanup, and
requested accurate configured-versus-observed thread labels (fixed). Read-only
skeptic confirmed the virtual-limit diagnosis was supported but initially
unproved, and then confirmed synchronous elaboration is a scheduling control,
not a kernel-check bypass or heartbeat increase. Neither review used Lean/server.
The conservative cache-inclusive headroom guard remains unchanged.

## Checkpoint 1: accepted old baseline

The fresh `old-clean-serial/` run passed all 984 dependency-ordered closure
modules, including every one of the 490 assigned Frontend modules, exactly
once. Every result has exit 0 and no resource stop, and every target has a
fresh `Built` log plus Lean artifacts. Wall time: **3676.983463 seconds**
(61.2831 minutes). Peak sampled aggregate process-group RSS:
**3,333,246,976 bytes** (3.104 GiB). The maximum target duration was below
300 seconds. Actual arguments include `--tstack=131072 -j1 -DElab.async=false`;
no theorem heartbeat or recursion budget was raised. One CPU was pinned.
This is the directory lane closure build, not full root acceptance.

```sh
python3 scripts/h62/item6/migrate-frontend/measure.py --toolchain /workspace/.setup/tools/lean-4.24.0-linux --census /workspace/h62-migrate-frontend-evidence/census/census.json --out /workspace/h62-migrate-frontend-evidence/old-clean-serial
python3 scripts/h62/item6/migrate-frontend/api_snapshot.py --measurement /workspace/h62-migrate-frontend-evidence/old-clean-serial/measurement.json --census /workspace/h62-migrate-frontend-evidence/census/census.json --out /workspace/h62-migrate-frontend-evidence/old-api
```

The API extractor passed with 20,218 constants across all 490 Frontend modules,
including private/generated declarations and import-only modules. It records
structural type representations, universe parameters, kind, safety/partial
markers and transitive axiom sets, then emits sorted per-module JSON and SHA256
hashes. The baseline has zero Frontend axiom declarations and zero `sorryAx`
users. The complete axiom union is `Classical.choice`, `Quot.sound`, `propext`.
Its 309.263242-second Lean subprocess time excludes Python normalization and
hashing and is separate introspection overhead, not
an assigned production module's build time or part of the clean-build wall time.
The generated command introduces no proof declarations. Bulk output stays off
Git; the generator is committed. Compiler auxiliary names must be distinguished
from frozen source statements when comparing versions. New-toolchain type and
axiom equivalence remains unvalidated.

Independent finder and skeptic reviewed the full clean dataset: exact census
ordering/coverage, single fresh module per invocation, source/configuration
hashes, logs/artifacts, exit codes and resource stops. Both accepted the lane
baseline with the stated sampled-RSS, conservative-headroom, uncontrolled-OS-cache
and per-invocation-overhead limitations. A full root gate remains pending.

The existing `NumericLiteralProofs/Audit.lean:45` writes the tracked
`tests/sol-numeric-literals/evidence/kernel-inventory.actual.json` as a build
side effect. Initial status was clean. Its generated bytes, diff and hashes
were preserved in off-Git `build-side-effects/`; only that confirmed generated
change was restored byte-for-byte from HEAD. No owner's inventory or source was
committed or manually migrated. Future builds must repeat this protection if
that audit module elaborates again. Both reviewers independently identified
and confirmed this provenance.

The corrected new-toolchain KeySort prerequisite also passed under the final
serial settings (`new-keysort-serial/`, one target, exit 0). Its wall time is
1.125943 seconds and sampled RSS 625,860,608 bytes; it is not a directory-level
performance comparison. The new clean build and regression decision remain
pending.

The API census finder/skeptic reviews verified manifest membership, counts and
sampled per-module hashes. They requested provenance checks under the writer
lock, recorded-census/private-config validation and streaming JSON input; these
were implemented. Saved evidence already satisfied those bindings independently.
Structural snapshots do not cover source commands, definition-body equivalence
or cross-version public-interface equivalence by themselves.

All 16 Python/OS acceptance controls pass, including six provenance-substitution
controls added for the API generator. Final independent finder and skeptic
rechecks accepted checkpoint 1 with no remaining material findings.
