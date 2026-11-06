# H62 item 6: isolated Calculus toolchain migration

Assigned branch: `codex/solidity-h62-6-20261106/migrate-calculus`.
Pinned base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
VM checkout: `/workspace/migrate-calculus` (separate worktree).
Original `/workspace/solidity-lean` checkout remains on `work` unchanged.
The base was fetched from origin and its ancestry to fetched origin/master verified.

## Preparation checkpoint (not migration completion)

The deterministic source census covers all 385 pinned Calculus Lean modules,
490 local modules in their import closure, 83 direct boundary imports and 1,213
reverse boundary imports across tracked Lean files, including roots and Bridge.
No reverse header was unparsed. All 385 Calculus files and all 490 closure
sources remain byte-identical to base. Whole-file hashes cover every original
statement, declaration, case, proof and resource option. These are source hashes,
not elaborated semantic API hashes: that migration obligation remains pending.
No existing Lean file, generated root, central map, pin or lean-toolchain changed.
No new theorem/helper, sorry, axiom, native_decide or proof-budget increase.

Generators: `scripts/h62/item6/migrate-calculus/census.py` and `bounded.py`.
Controls: `tests/h62/item6/migrate-calculus/test_tooling.py` (five passing tests).
Bulk evidence is off git at `/workspace/migrate-calculus-evidence`.
Current census: `base-census-v3/census.json`, `source-sha256.txt` and
`ordered-modules.txt`. Reproduce with:

```sh
python3 scripts/h62/item6/migrate-calculus/census.py /workspace/migrate-calculus /workspace/migrate-calculus-evidence/new-census
PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item6/migrate-calculus/test_tooling.py
```

## Toolchain and measurement policy

Coordinator input manifest verifies all five supplied files. The required official
`leanprover/lean4:v4.35.0` archive has SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual Lean: 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake: `5.0.0-src+eb6cafb (Lean version 4.35.0)`.
Actual old Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake: `5.0.0-src+797c613 (Lean version 4.24.0)`.
Full extracted-install verification checked 11,574 old files and 17,938 new files
against their respective archives. Deliberately pairing the new archive with the
old installation was rejected (`share/lean/lean.mk` mismatch).
See `installation-verification.json` off git.

Measurements use a fresh output directory with artifact caches disabled,
Docker memory.max=12884901888 and swap.max=0, one CPU, 4 GiB outer available
reserve, LEAN_NUM_THREADS=1 and explicit Lean -j1 behind a serial lock. No systemd-run.
The runtime image is pinned by local image SHA256
`d9b8c34d61a9b9a3c44cab883d7d2f2619d674966ab520186f799cf32e3e0377`;
read-only host executable/library mounts are recorded in each result.
The harness validates the full source inventory before and after, records
config/source/harness hashes, and times the 490-module directory closure.
It is a directory measurement, not the repository final `run-lean.sh` gate.
Any measured regression must be escalated; over 10 percent requires STOP.

The preliminary `old-clean-01` run was deliberately stopped after review found
monitoring/provenance gaps. Its 81.691 s partial timing is invalid as a baseline.
The initial new KeySort probe passed (2.527 s; sampled aggregate RSS 617336832
bytes), but predates final archive/install admission checks. Retain as diagnostic
only; repeat under the final harness before accepting prerequisites.
RUNTIME_GATE_PASS is pending. Full old clean build, new directory build,
matched timing comparison, final validation, semantic interface validation and
migration patch acceptance are all unfinished.

## Independent reviews

Finder and skeptic were separate read-only agents; neither ran Lean or a server.
Initial reviews requested: complete reverse imports, validate census/source
provenance, reserve before workload, bounded monitoring, support module headers,
and bind archive to the selected installation. Confirmed findings were fixed.
Finder accepted the focused census/harness fixes; skeptic accepted the original
census/monitoring fixes and requested the final archive/install binding, now
implemented and checked by positive and deliberately mismatched-install controls.
Focused re-review of that final change is pending. This is no full migration review.

## Ownership and remaining work

No `relay.sh` is present in the actual checkout or supplied coordinator inputs.
Exact-file requests must be saved for coordinator pickup when a required source
adaptation is identified. No absent reply is treated as permission. Live producer
ownership continues unchanged; no H55 work is claimed. External dependency
sources in the census are read-only to this lane. No cut-over, push, merge,
pre-gate, deployment or freeze announcement has occurred.

Next: final-harness new-toolchain dependency probe, clean old closure measurement,
owner relay for concrete external failures, scoped acceptance/fixture backfill,
owner-coordinated Calculus adaptations, full new build and matched timings,
independent milestone reviews, final patch/bundle/hash handoff to root/gate.
