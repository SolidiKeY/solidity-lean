# H62 item 6 — Storage migration overlay

Owner: `solidity-h62-6-20261106/migrate-storage`. Repository:
`/workspace/solidity-lean`. Branch:
`codex/solidity-h62-6-20261106/migrate-storage`. Pinned base:
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4` (verified ancestor of fetched
`origin/master`). Original clean branch `work` was preserved; no reset,
push, merge, cut-over, freeze, or producer-ownership transfer occurred.

## Checkpoint 1: census and clean old component build

All 21 assigned original modules remain byte-identical to the base. The census
covers 360 named declarations and every original case, statement, proof and
budget through whole-source SHA-256. Lexical declaration rows are navigation aids;
they are not elaborated interface fingerprints. There are 36 external source
modules in the 57-module closure (including the KeySort prerequisite), eight
direct edges out of Storage, and 1,576 downstream affected modules. Full details
and per-file hashes: `/workspace/migrate-storage-evidence/census-base.json`.
No owned Lean declarations/helpers were added or edited. Original lexical
`sorry`, `axiom`, `native_decide` counts: 0, 0, 0; introduced counts: 0, 0, 0.

Commands (repository cwd unless absolute):

```sh
python3 scripts/h62/item6/migrate-storage/census.py
PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item6/migrate-storage/acceptance.py
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/measure.py /workspace/.setup/tools/lean-4.24.0-linux /workspace/migrate-storage-evidence/old-clean-2 --image sha256:d9b8c34d61a9b9a3c44cab883d7d2f2619d674966ab520186f799cf32e3e0377
```

Scanner negative controls PASS: nested comments, strings, multi-imports, cycle
rejection, source positions, actual owned/external file mutations, and missing
inputs. These are Python/tooling tests, not Lean proofs or EVM external tests.

Clean old component build PASS: 57/57 modules, including 21/21 assigned originals;
actual Lean 4.24.0 commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`,
Lake `5.0.0-src+797c613`. Decisive output: `KEYSORT_COMPONENT_PASS` and
`COMPONENT_RESULT 0 None`. Build wall 174.421309 s;
peak sampled aggregate RSS 855543808 bytes. All module commands, exits,
wall/RSS samples, input/config hashes and cleanup state are saved in
`/workspace/migrate-storage-evidence/old-clean-2/result.json`; console and
per-module logs are adjacent. Both `sources_unchanged` and `controls_unchanged`
are true and the private container is stopped. Failed `old-clean-1` is retained:
Docker top omitted its required PID column; it supplies no accepted timing.

Measurements use a fixed image, one CPU, a hard Docker memory cap of 12 GiB,
memory+swap total 12 GiB (zero swap), a 4 GiB available-memory reserve, one Lean
process, `LEAN_NUM_THREADS=1`, explicit `-j1`, `--tstack=131072`, and `-M=10240`.
Sources/toolchains are mounted read-only. Every run starts with an empty private
artifact directory and uses no Lake/per-master cache. RSS is sampled, not an
exact high-water mark; OS page cache is not normalized. These are serial
per-file component elaborations and do not replace `./run-lean.sh` final gates.

Independent read-only finder and skeptic reviewed the tooling without a Lean
server or Lean execution. Findings fixed: verify all external source bytes,
record archive and executable identities, use immutable image ID, handle
signals, bound Docker calls, guard host Lean/Lake processes, fix declaration
positions and Docker PID sampling, remove bytecode, and exercise real file drift.
Final rereviews found no further confirmed tooling defects; their evidence
limitations above remain explicit.

## Checkpoint 2: pinned new toolchain and adaptation

Coordinator inputs in `/workspace/h62-coordinator-inputs/` were checked against
`sha256.json`. Official pin: `leanprover/lean4:v4.35.0`, archive
`lean-4.35.0-linux.tar.zst`, SHA-256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Archive/extraction: `/workspace/migrate-storage-evidence/toolchains/`.
Observed Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
Lake `5.0.0-src+eb6cafb`. Candidate component run pending. Tracked
`lean-toolchain` remains unchanged. Existing-file owner coordination is required
before any source repair; no `relay.sh` is supplied here and no repair is yet
requested or performed. The coordinator retrieves saved artifacts from this VM.

## Remaining queue and handoff

Checkpoint 3 (new build, same-settings comparison, regression decision) and
checkpoint 4 (final reviewable patch/bundle and root-gate dependency report) are
pending. Required full affected validation, final `./run-lean.sh`, and new
KeySort prerequisite remain pending. No `RUNTIME_GATE_PASS` or assignment
completion is claimed. Continue on this exact VM/branch/goal; do not create a
replacement goal. There is no callable `get_goal`; coordinator confirmed this
optional inspection absence is not a blocker.
