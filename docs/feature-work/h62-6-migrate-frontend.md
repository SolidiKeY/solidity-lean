# H62 item 6: Frontend migration overlay

Owner: `solidity-h62-6-20261106/migrate-frontend`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-6-20261106/migrate-frontend`.
Checkout: `/workspace/solidity-h62-migrate-frontend`.
Evidence: `/workspace/h62-migrate-frontend-evidence` (bulk files outside Git).

Status: partial. All four assignment checkpoints remain open until their
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

1. Complete a clean old-toolchain build of all 490 Frontend modules and their
   dependencies, recording wall/RSS with these fixed settings.
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
