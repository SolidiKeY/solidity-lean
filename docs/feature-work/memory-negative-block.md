# Memory negative-block reconstruction prerequisite

Status: incomplete. `gapMemInnerNeg` remains an original open closer gap. No
`DecisionTheorem`, `inTarget`, exclusion, waiver, or original verdict pin is
changed. This work proves an independent object-reconstruction prerequisite
and a kernel countermodel for the original formula; it does not implement
the scoped negative-block preparation pass.

Baseline: `/workspace/solidity-lean`, origin
`https://github.com/SolidiKeY/solidity-lean.git`, published master and branch
base `f4dee4a29c2e208b36db4a4161a4723c735cd775`. The isolated branch is
`codex/next10-memory-negative-block`. Fetch and ancestry checks succeeded.
Lean 4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`), Lake
5.0.0-src+797c613. Activation is `/workspace/.setup/activate.sh`.

## Interface

`Calculus/MemFloor.lean` uses the existing `floorIn` and `MemSwap` object
constructors. `mxFloorRebuild` takes a primitive-array kind, the existing
`mxArrOk` condition, an intrinsic `MObj`, and integer breakpoints. Its
output has exactly the input length and kind. It never grows a memory
array to `2^256` slots and never reconstructs reference-valued members.

`mxFloorRebuild_slot` proves optional-read equality at **every** natural
index: new slot `k` equals old slot `mxFloorIndex B k`. Its essential
side condition is that the original length belongs to `B`. Monotonicity,
the decreasing-floor law, and that fixed length prove bounds equivalence.
`mxFloorRebuild_at` fixes retained reads, including halted ones;
`mxFloorRebuild_fillN` preserves the length word; `mxFloorRebuild_fill`
preserves the existing `MxMap` filling interface when all successful index
evaluations are retained. These lemmas are useful to later written-memory
hashing, but do not prove interaction with writes.

The API only reconstructs objects. It does not change heap identities or
claim state-level alias preservation. Existing `MxRel.apart` and fresh
allocation semantics remain unchanged. No given-heap binder or struct
coverage is added. No new syntax or term constructor needs a printer.

## Controls and evidence boundary

`Examples/MemoryFloor.lean` checks dynamic uint and fixed bool objects,
zero/nonzero lengths, same/different retained indices, and reads at/past the
length. Negative controls show why omitting a length breakpoint changes
definedness and why a decreasing floor alone does not transfer a strict
guard. Compiled `#guard` observations are distinct from the named kernel
proofs (`retained_read`, `empty_read_halts`,
`missing_length_changes_definedness`, `missing_threshold_changes_guard`).
These are semantic/kernel and compiled Lean observations, not solc or EVM
execution evidence. No Solidity source fixture or compiler behavior is
changed, and no feature support classification is promoted.

The original formula is false for an empty fresh array: its universal
premise holds vacuously while its concluding read halts. Its future exact
closer verdict must be `refuted`, not `proved`. `Examples/MemoryNegativeCountermodel.lean` now proves this on the original
formula: `gapMemInnerNeg_falseAt` gives the empty-array witness at every
base state, `gapMemInnerNeg_countermodel` selects `State.init Gaps`, and
`gapMemInnerNeg_notValid` establishes non-validity. These are kernel proofs,
not an improved compiled closer verdict; the existing pin stays `unknown`.
All three audit to `[propext, Classical.choice, Quot.sound]`.

## Remaining dependency

The missing prerequisite for full closure is a memory-specific scoped
array-property preparation: recognize negative blocks; collect other reads,
lengths, guard operands and valid successors; perform capture-safe
instantiation; transfer guards; lift object reconstruction through fresh
allocation to the observation/`MxRel` relation; and prove soundness and
refutation of that preparation before `Fml.mx`. Then integrate its coverage
and change the original pin only after the actual improved verdict is
proved. `Fml.mx_holds` retains its per-state exactness statement.

## Review

Independent read-only finder and skeptic agents inspected MemSwap,
ArrayProperty/ArrayBlock, and the reconstruction and control drafts. Neither
used a Lean server or ran a build. They confirmed the missing bounds
obligation and the need for a separate preparation relation. Confirmed
findings fixed: replace an unavailable `by_contra` tactic; distinguish
compiled `#guard` checks from kernel proofs and add kernel boundary controls.
Final source and documentation review is recorded below.

## Validation

Raw logs, command drivers, startup identity and original source hashes are
exported under `/workspace/next10-memory-negative-block-evidence/`.
The writer lock is
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`.
Heavy checks run serially with `LEAN_NUM_THREADS=1` and explicit Lean
`-j1` using an untracked alternate Lake configuration. Docker cgroup v2
reports `memory.max=12884901888`, `memory.swap.max=0`; its aggregate
`memory.peak` includes workers and cache. The VM's outer limit is 16 GiB;
the local-machine 12 GiB reserve is not applied to this VM.

`lake build Solidity.KeySort` succeeded before `RUNTIME_GATE_PASS` was
written: runtime-gate.log retains actual output and a 24,920,064-byte
aggregate cgroup peak. systemd's user scope was unavailable (no user bus),
so the verified Docker equivalent was used. The first direct baseline
fixture check failed because its imported `Decision.olean` was absent;
the missing dependencies were then built in the same executor.

The measured run reused the saved on-disk caches and rebuilt missing
artifacts; it is not a clean-cache or general 16 GiB guarantee. No resource
stop occurred. The full run reached the configured 12 GiB cap: cgroup
`memory.events` recorded `max 18`, `oom 0`, `oom_kill 0` (reclaim pressure,
not an OOM kill). The final warm confirmation had no OOM events either.
`headroom-samples.jsonl` records the outer 16 GiB limit, anonymous/file
usage, and a 5,729,007,672-byte estimate of headroom after reclaimable
inactive-file pages and slab. Cache reclamation is distinguished from
anonymous process memory.

All successful commands below exited 0. Times are wall seconds. Peaks
from grouped validation are cumulative aggregate cgroup peaks in that
container, including cache; they are not isolated per-command RSS.

| Command / check | Seconds | Aggregate peak bytes | Evidence log |
|---|---:|---:|---|
| `lake build Solidity.KeySort` (initial gate) | 0.525 tool-wall | 24920064 | `runtime-gate.log` |
| `lake build Solidity.Examples.DecisionMemory` (baseline) | 3404 | 10435162112 | `baseline-build.log` |
| `lake env lean --tstack=131072 -j1 ObserveMemory.lean` (before) | 26 | 214134784 | `observations-before.log` |
| MCP all-severity `MemFloor.lean` | 4 | 545284096 | `mcp-core-4.log` |
| MCP all-severity `MemoryFloor.lean` | 3 | 543367168 | `mcp-controls-4.log` |
| MCP all-severity `MemoryNegativeCountermodel.lean` | 3 | 632573952 | `mcp-countermodel-2.log` |
| `lake build Solidity.Examples.MemoryFloor` (controls-build) | 2.147 | 198365184 | `controls-build.log` |
| `lake env lean --tstack=131072 -j1 /workspace/next10-memory-negative-block-evidence/ObserveMemory.lean` (observations-after) | 27.459 | 222322688 | `observations-after.log` |
| `node scripts/check-orphans.mjs` (orphans) | 0.121 | 67735552 | `orphans.log` |
| `node scripts/check-layers.mjs` (layers) | 0.141 | 69787648 | `layers.log` |
| `node scripts/check-automatic.mjs --strict` (automatic-strict) | 0.042 | 69787648 | `automatic-strict.log` |
| `bash scripts/check-trust.sh` (trust) | 4.066 | 169979904 | `trust.log` |
| `python3 scripts/solidity-feature-audit.py` (inventory) | 0.045 | 169979904 | `inventory.log` |
| `bash ./run-lean.sh` (full-run-lean) | 6267.705 | 12884901888 | `full-run-lean.log` |
| `lake build Solidity.Examples.MemoryNegativeCountermodel` (countermodel-build) | 1.873 | 206585856 | `countermodel-build.log` |
| `lake env lean --tstack=131072 -j1 /workspace/next10-memory-negative-block-evidence/ObserveFloor.lean` (floor-observations) | 3.411 | 206585856 | `floor-observations.log` |
| `bash ./run-lean.sh` (full-final-warm) | 2.714 | 451903488 | `full-final-warm.log` |
| `node scripts/check-orphans.mjs` (orphans-final) | 0.157 | 451903488 | `orphans-final.log` |
| `node scripts/check-layers.mjs` (layers-final) | 0.169 | 451903488 | `layers-final.log` |
| `node scripts/check-automatic.mjs --strict --build-log /workspace/next10-memory-negative-block-evidence/full-run-lean.log` (automatic-strict-timed) | 0.068 | 451903488 | `automatic-strict-timed.log` |
| `bash scripts/check-trust.sh` (trust-final) | 5.023 | 451903488 | `trust-final.log` |
| `python3 scripts/solidity-feature-audit.py` (inventory-final) | 0.058 | 451903488 | `inventory-final.log` |
| `git diff --check` (diff-check) | 0.013 | 451903488 | `diff-check.log` |

The strict timed gate checked 26 TestSuite modules at the unchanged 300 s
budget: 491 automatic, 61 with a step budget, 0 manual, 11 refuted, 0
pending. The final trust scan covered 717 sources and 240 inventoried
implementation/recovery sites with 0 findings. Feature inventory
regeneration produced no tracked change. No repository script changed,
so no script-unit-test change was needed.

Failed attempts are retained separately: the first baseline file check
lacked `Decision.olean` (exit 1, repaired by the successful dependency
build); the first MCP container lacked the existing `/opt` Python runtime
(exit 127, repaired by a read-only runtime mount); edit diagnostics failed
until the local proof/type issues were fixed; the first gate launcher
lacked Node on PATH (exit 1 before Node gates ran, repaired using the saved
runtime). Completed checks were retained and only unrun gates resumed.
The known MCP shutdown event-loop warning followed successful diagnostics;
final results have `success=true`, `partial=false`, no errors/warnings, and
no failed dependencies. No source `sorry` scaffold or new axiom was used.

### Actual axiom audits

`mxFloorRebuild_slot`, `mxFloorRebuild_fill`, `retained_read`,
`empty_read_halts`, `missing_length_changes_definedness`, and all three
original-formula countermodel theorems depend only on
`[propext, Classical.choice, Quot.sound]`.
`missing_threshold_changes_guard` has no axioms. Exact printed output is
in the successful MCP, module-build, and floor-observation logs. Existing
`memAck_iff` and `gapMemWrite_iff` retain the same three-axiom audit.

### Ordered fixture observations

The original 21 verdicts below are identical before and after. Raw complete
ordered output is in `observations-before.log` and `observations-after.log`;
`observations-comparison.json` records the equality. All three original
source files owning the six gap statements and `inTarget` certificates are
byte-identical to the base, with SHA256 records in
`original-gap-source-hashes.json`.

| Fixture | Before | After |
|---|---|---|
| `gapMemory` | refuted | refuted |
| `memSame` | proved | proved |
| `memAck` | proved | proved |
| `memAckBad` | refuted | refuted |
| `memApart` | refuted | refuted |
| `memInRange` | proved | proved |
| `memPast` | refuted | refuted |
| `memHalts` | proved | proved |
| `memFixed` | proved | proved |
| `memFixedPast` | refuted | refuted |
| `memLenEq` | refuted | refuted |
| `memBools` | proved | proved |
| `gapMemInnerNeg` | unknown | unknown |
| `gapMemParam` | unknown | unknown |
| `gapMemStruct` | unknown | unknown |
| `gapMemInner` | refuted | refuted |
| `memInnerAck` | proved | proved |
| `gapMemWrite` | proved | proved |
| `memWriteBad` | refuted | refuted |
| `memWriteOther` | proved | proved |
| `memWriteDia` | refuted | refuted |

The new controls' full ordered compiled observations are retained in
`floor-observations.log`: dynamic `[7,7]`; retained `[7,9]`; bounds
`[none,none]`; empty `(0,none)`; fixed bool `([true,true,true],none)`;
missing length `(none,some 7)`; missing guard `(false,true)`. The same run
checks the named kernel certificates. No source/compiler/EVM observation
is inferred from these compiled Lean values.

### Final independent review

Finder and skeptic separately reviewed the installed reconstruction,
controls, countermodel, registrations, module-map entry, M7 link and scope
statement, read-only and without a Lean server or build. Both reported no
remaining confirmed issue. Earlier confirmed source findings were fixed before
final verification. The final evidence review also corrected the replay
example so that both configuration copying and Docker execution hold one
writer lock. The final validation table records completed commands;
the outstanding assignment work is the preparation/integration described
above, not an unreported passing verdict.

### Replay on this saved executor

The exported `lakefile.memory-negative.toml` differs from the tracked
configuration only by adding `-j1` to the existing library `weakLeanArgs`.
It was removed from the checkout after validation. With the exported
configuration copied back, the full gate can be replayed under the writer
lock using the same runtime and bounds:

```sh
(
  flock 9
  git -C /workspace/solidity-lean status --short
  cp /workspace/next10-memory-negative-block-evidence/lakefile.memory-negative.toml /workspace/solidity-lean/lakefile.memory-negative.toml
  docker run --rm --user 1000:1000 --memory=12g --memory-swap=12g \
  --mount type=bind,src=/workspace,dst=/workspace \
  --mount type=bind,src=/usr,dst=/usr,readonly \
  --mount type=bind,src=/opt/codex/runtimes,dst=/opt/codex/runtimes,readonly \
  -w /workspace/solidity-lean ubuntu:24.04 bash -c 'source /workspace/.setup/activate.sh; export LEAN_NUM_THREADS=1; export PATH=/workspace/next10-memory-negative-block-evidence/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin:$PATH; bash ./run-lean.sh'
) 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
```

The exported MCP runner checks one file at a time with `interactive=false`;
its container additionally mounts the existing Python runtime read-only.
`validation-results.json` and `final-scope-results.json` retain the exact
inner command arguments, UTC intervals, exit codes and measured peaks.


## Shared edits

Only module registrations in `Solidity.lean`, the module-map entry, and the
M7 link in `docs/automation.md` are shared. Implementation and controls use
new task-specific additive modules. No previous-batch work, ordinary
recursive-type migration, profile decision, push, merge, or other VM is used.
