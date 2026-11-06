# H62 item 6: EVM migration overlay

Owner: `solidity-h62-6-20261106/migrate-evm`. This is an isolated migration
overlay, not live producer ownership. No source migration or runtime pass is
claimed by the tooling checkpoint.

## Checkout and authorization

- Repository: `/workspace/migrate-evm`.
- Branch: `codex/solidity-h62-6-20261106/migrate-evm`.
- Exact base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
- Original clean checkout `/workspace/solidity-lean` at `6cf853aea` was preserved.
  `git fetch origin master` recovered the base; `git merge-base --is-ancestor
  c6f550e281a7e5affa9a99bc2cdaed556dec00e4 origin/master` passed. Published
  master observed at `821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`.
- Coordinator inputs: `/workspace/h62-coordinator-inputs`; all five files match
  `sha256.json`. The absent `get_goal` tool is explicitly not a blocker per the
  coordinator continuation. No goal was created or reset.
- No existing `Solidity/Evm` file has been edited. Exact-file owner coordination
  remains required before edits; no `relay.sh` is available in this VM.

## Toolchains and bounds

Official release archives are retained under
`/workspace/migrate-evm-artifacts/toolchains/`:

| Version | Archive SHA256 | Actual Lean/Lake |
|---|---|---|
| 4.24.0 | `b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec` | Lean commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake `5.0.0-src+797c613` |
| 4.35.0 | `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` | Lean commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake `5.0.0-src+eb6cafb` |

The new archive exactly matches coordinator `toolchain-pin.json`; no substitute
build or per-master cache is used. Tracked `lean-toolchain` remains v4.24.0.

VM cgroup: 16 GiB memory, four CPUs; host swap observed zero. Final measurement
containers enforce 12 GiB memory, zero swap, one CPU, 128 PIDs, read-only source,
and no network. Container image is pinned to
`python@sha256:935c3c5b12357a7e10caa9c1e6ca5692344d97cf229832ef584be2cec9fc03df`.
The runner checks an outer 4 GiB reserve before and during each module, uses
`LEAN_NUM_THREADS=1`, `--tstack=131072 -j1`, and a 300-second module stop. Kernel
`wait4` peak RSS and sampled process-group RSS are separate fields; cgroup peak
memory is also recorded. OOM, reserve, timeout and elaboration stops are distinct.
There is one Lean job at a time. No systemd-run is used.

## Census and acceptance

`census.py` freezes exact source bytes and budgets for 277 EVM sources and their
386-module local closure. There are 39 direct cross-directory import edges to
17 distinct modules. Lexical EVM counts are 4,319 declaration keywords, zero
`sorry`, and zero `axiom`; these are not an elaborated declaration inventory.
Source hash equality freezes all original declarations/cases/proofs without
claiming compiler-level type equality.

`generate-inventory.py` deterministically generates the test-only
`Inventory.lean` and `InventorySmoke.lean`. It emits all imported EVM constants by
module origin, including constructors, recursors and generated auxiliaries,
with sorted names, exact raw type expressions and universe parameters. It does
not prove bodies equivalent or replace the full repository gate.

Commands run:

- `PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item6/migrate-evm/test_census.py`:
  exit 0, five tests. Includes source-mutation, missing-import and cycle negative
  controls, comment/string/character masking and multiline import controls.
- `bash -n scripts/h62/item6/migrate-evm/run-bounded.sh`: pass.
- Python AST parsing of all lane scripts: pass.
- Bounded v4.24.0 `lean --tstack=131072 -j1
  tests/h62/item6/migrate-evm/InventorySmoke.lean`, using the pilot's private
  imports: exit 0, 494 unique constants (53 constructors). Raw JSONL is off git
  in `evidence/old-inventory-smoke.log`. Initial helper check found unsupported
  `liftIO`; replaced with the supported MonadLift IO action and rechecked.

## Independent reviews

Read-only finder `/root/finder_census` and skeptic `/root/skeptic_census` ran no
Lean server and made no edits. Confirmed findings and fixes:

- Sampled leader-only RSS was insufficient: added wait4 exact RSS, process-group
  sampling, Docker hard bounds, resource preflight and cgroup peak memory.
- Character literal and multiline import fixtures: scanner corrected; current
  full census remains exactly equal to its original result.
- Monitoring exceptions and residual descendants: exception-safe reap and
  process-group KILL after both normal and interrupted leader exits.
- Docker client cancellation: owned-container EXIT/INT/TERM cleanup; pipeline
  runs in background with interruptible wait.
- OOM classification: cgroup `oom_kill` deltas produce typed resource stop.
- Base-only whole-source check prevented future migrated proofs: launcher accepts
  a separately frozen candidate census; exact API comparison remains required.

The two initial instrumentation pilots (`old-clean`, `old-clean-v2`) were
intentionally stopped before completion while resolving these findings. They
are retained off git and are not baseline passes or slowdown measurements.

## Checkpoint handoff and outstanding gates

1. Import/source census and reproduction tooling prepared; complete old clean
   timing and full elaborated API inventory are pending.
2. Official new toolchain pin verified; all source adaptation and external-owner
   dependencies remain pending until the bounded new-toolchain run identifies
   actual failures. Existing originals require exact-file owner relay first.
3. All 277 new-toolchain EVM module checks, affected acceptance, final Lake /
   `run-lean.sh` gate, and comparable clean old/new wall/RSS are pending. No
   RUNTIME_GATE_PASS or regression conclusion is asserted. Any regression must
   escalate; greater than 10 percent is STOP.
4. Final patch/bundle, API hashes, cross-directory dependency report, checksum
   manifest and migration-root-gate handoff remain pending.

Bulk output stays off git in `/workspace/migrate-evm-artifacts/evidence/`.
Source/test helper changes are additive only; zero production declarations,
frozen statements, premises, exclusions, proof budgets or axiom pins changed.
No push, merge, PR, master cut-over, producer freeze or ownership transfer occurred.
