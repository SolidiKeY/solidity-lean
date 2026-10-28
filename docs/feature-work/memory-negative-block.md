# Memory negative-block preparation and exact closer refutation

Status: complete for the assigned original `gapMemInnerNeg`. Its unchanged
formula now receives a kernel-certified **refuted** verdict from the actual
integrated closer, including a theorem about its returned countermodel.
All mandatory full/strict/trust/fixture/axiom/diagnostic/orphan/layer/inventory
gates passed. An extra global documentation-path scan still reports 20
pre-existing references into absent external projects; those remain open and
are not claimed passing. No task-owned missing path remains.

The earlier sections below are historical partial milestones. The latest
integration and final evidence are at the end. No target, waiver, exclusion,
profile or `DecisionTheorem` statement is changed. The other five original
gap statements and all six original target certificates are preserved.

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

The `MemFloor` API only reconstructs objects. It does not change heap identities or
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

The latest continuation supplies intrinsic range-body recognition and guarded
point instantiation in `MemInst`, including a fresh-allocation reconstruction
boundary. Full closure still needs the enclosing-leaf collector, stable exterior
observations, scoped length atoms, a whole-leaf soundness/refutation certificate,
and actual integration before `mxTop`. See continuation `bab6410c` below for the
exact attempted construction and current remaining proof obligation.

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

## Continuation b4b6f3b8-ee8a-4ec4-b964-c2cbb819f21a

Retained executor and checkout verified on 2026-10-28: same origin, clean
branch at `755c9bac0d3e39934eb1a8f7487f40d57a2e6a50` before edits, unchanged
Lean/Lake versions, local Docker cgroup v2 usable after sandbox escalation.
No replacement VM, network configuration, credentials, other task, or
monitor was changed. New raw evidence is in
`/workspace/next10-memory-negative-block-continuation/`.

This continuation adds proofs, not a closer implementation. The exact original
`gapMemInnerNeg` still returns `unknown`; all six gap definitions and target
certificates are retained. No external provisioning blocker was found. The
remaining blocker is an unproved implementation/reduction obligation.

### Newly proved semantic reduction

`mxFloorIndex_ge_iff`, `gt_iff`, `le_iff`, and `eq_iff` transfer natural-index
comparison guards. Non-strict lower and strict upper comparisons retain the
operand; strict lower and non-strict upper comparisons retain its successor;
equality retains both. `mxFloorIndex_point` places every floored index at zero
or a nonnegative retained point. The successor theorems operate on natural
indices; they do not authorize a uint literal `2^256`. The kernel control
`top_successor_not_uint` explicitly rejects that value.

`mxFloorRebuild_block` turns instances at zero and retained points into a
universal **length-guarded** property of the rebuilt object's optional reads.
`mxFloorRebuild_block_reads` simultaneously preserves all listed exterior
reads, including halted ones. `mxFloorRebuild_negative_iff` proves an exact
finite-instance reduction for universal implications over one fresh intrinsic
primitive object: the block predicate may depend on length and optional word;
the consequent may depend on length and listed fixed natural read indices.
The points may depend on the original object. The theorem's forward direction
applies the original universal claim to the reconstructed object, whose length
and exterior reads agree. Its reverse direction takes ordinary instances.
Zero lengths need no special case: the range premise is false and exterior
reads remain `none`.

Written-memory hashing can use `block_reads` to obtain block satisfaction and
an equal vector of optional observations together, alongside the existing
`fillN`/`fill` interfaces. This interface proves no interaction with writes,
no identity surgery, and no state-level alias preservation. Repeated listed exterior reads of
the same object are preserved; multiple coupled arrays and reference members
are outside this lemma.

### Exact unproved bridge to the original closer

The semantic equivalence is not a proof-carrying `Fml` preparation. What is
still missing is a fail-closed recognizer producing an intrinsic scoped output
and a proof connecting it to the original leaf. It must:

1. Introduce scoped length atoms before fresh-array binders, with proved
   correspondence to each allocated object's actual length. Instantiating at
   a raw `mlen` term cannot simply pass `Tm.ixOk`.
2. Collect exterior read terms, lengths, guard operands and valid successors,
   and substitute block variables capture-safely. `Fml.mxIdx` currently tries
   to pull indices to the array binder; binder-dependent indices are discarded.
3. Lift the object result through allocation and the original state's heap
   typing while preserving the same aliases and the distinct fresh locals
   required by `MxRel.apart`. Apply the natural guard results to **evaluated
   intrinsic terms**, including their optional/short-circuit definedness.
4. Produce the soundness/refutation certificate consumed before `Fml.mxTop`
   in `decideMem`, and update coverage only after that proof checks.

The existing storage `apfPrepK` cannot supply this bridge: `apfState` performs
storage/ledger surgery and its `Surg` relation does not relate fresh memory
objects. Nor does hoisting move the negative block out: doing so would change
polarity semantics. No bypass or named-fixture special case was introduced.

### Controls and reviews

`rebuilt_block` uses the new generic theorem to show all live slots satisfy
its finite instances; `original_block_fails` shows the original nonsampled
slot violates that same property. Kernel controls distinguish an operand from
its successor, expose the equality singleton-region requirement, and reject
uint successor overflow. Existing empty/fixed/halting/read controls remain.
These are kernel/compiled Lean evidence, not Solidity compiler or EVM runs.

Independent finder and skeptic reviews were read-only, with no Lean server or
build. Both found no missing hypothesis in the object-level equivalence,
including its object-dependent point set. Both explicitly confirmed that its
scope excludes arbitrary index-dependent block predicates, general intrinsic
guards, coupled objects, heap relations and a decider certificate.

### Continuation validation

Every command below exited 0; raw outputs and UTC intervals are retained in
`core-results.json` and `final-results.json`. Peaks are cumulative per bounded
Docker group. The final MCP files reported success, partial=false, and no
errors/warnings. Intermediate failed length simplifications are retained in
`mcp-core.log` and `mcp-controls-initial.log`; their automatic error-recovery
`sorryAx` is absent from final audits. No source `sorry` was introduced.
The MCP process still emits the pre-existing Python event-loop cleanup warning
after returning successful diagnostics, with exit 0.

| Check | Seconds | Peak bytes in group |
|---|---:|---:|
| `mcp-core-final` | 3.537 | 674738176 |
| `core-build` | 1.758 | 674738176 |
| `mcp-controls` | 2.955 | 674738176 |
| `runtime-gate` | 0.154 | 30416896 |
| `controls-build` | 1.459 | 209649664 |
| `original-observations` | 25.364 | 220053504 |
| `floor-observations` | 2.826 | 220053504 |
| `full-confirmation` | 2.257 | 386113536 |
| `orphans` | 0.116 | 386113536 |
| `layers` | 0.149 | 386113536 |
| `automatic-strict` | 0.043 | 386113536 |
| `trust` | 3.973 | 386113536 |
| `inventory` | 0.044 | 386113536 |
| `diff-check` | 0.009 | 386113536 |

The full confirmation reused the existing disk cache; it is not a clean-cache
benchmark. Its strict automation report times zero replayed TestSuite modules,
while enforcing unchanged verdict/budget policies; the original full-build
26-module timing evidence remains in the earlier evidence directory. The
continuation strict gate reports 491 automatic, 61 with a step budget, zero
manual, 11 refuted and zero pending. Trust reports 717 sources, 240 inventoried
implementation/recovery sites and zero findings. Inventory regeneration made
no tracked inventory change and no support promotion. No scripts were changed.
No source/compiler/EVM pipeline was added or claimed: these are Lean object
controls and original closer observations.

All 21 original ordered fixture observations match the original baseline,
including `gapMemInnerNeg: unknown → unknown`. Full per-fixture comparisons
are in `original-observation-comparison.json`. `Calculus/Decision.lean`,
`DecisionKInt.lean`, and `DecisionMemory.lean` remain byte-identical to the
published baseline; `original-gap-source-hashes.json` records the comparison.

Final kernel audits of `mxFloorRebuild_negative_iff`, `block`, `block_reads`,
`mxFloorIndex_eq_iff`, `rebuilt_block` and `original_block_fails` contain only
`propext`, `Classical.choice`, `Quot.sound`. The successor-repair and uint-top
kernel controls have no axioms. The original three countermodel theorems are
unchanged and retain their previously audited standard three axioms. No
conditional or concrete execution is presented as a decider certificate.

Finder's final documentation review corrected “repeated reads” to “repeated
listed exterior reads”; unretained slots may change. Skeptic found no further
issue. Both reviews were independent, read-only, and used no Lean server.

Shared tracked edits in this continuation are only `Calculus/MemFloor.lean`,
`Examples/MemoryFloor.lean`, `docs/automation.md` and this owning handoff. No
imports changed; no other lane, given-heap binder, struct, callback or invariant
semantics changed. The temporary alternate Lake file is removed after checks;
its exact resource-only settings remain in evidence. The task is incomplete:
its original exact verdict and the scoped/state preparation bridge above are
still open, despite all validation of this bounded increment passing.

Final finder and skeptic evidence reviews matched the actual JSON/log records;
their confirmed Markdown table-spacing issue was fixed. No source or scope
changes followed validation.

## Intrinsic continuation bab6410c-67c6-4ce0-b0cc-af7c473a54ea

Status: the distinct intrinsic instantiation step is checked; the original
assignment is **incomplete**. `gapMemInnerNeg` still has its unchanged unknown
pin. The retained clean branch started at `add3e02446f88c9298edb6ad57485a8c7bd74c4d`,
with the same repository, base and Lean/Lake versions. Actual executor startup
and bounded Lean execution are in `intrinsic/startup.log` in the refreshed
archive. No object-level milestone was rerun or altered. No named-fixture
match, changed target/profile/waiver, new axiom, sorry or increased budget was
introduced.

### Intrinsic certificate and supported shape

`Calculus/MemInst.lean` is additive. `MxPoint C Γ` carries a typed uint term,
a provenance tag and a proof of denote/evaluation agreement at every state;
it does not assert totality or reconstruction stability. The scoped point
builder includes zero, the actual memory length, supplied read/guard operands
and their checked successors. The caller supplies those read/guard operands;
this is not yet a certified traversal of an enclosing leaf. Successor overflow
halts and does not wrap to zero.

`mxInst_holds` proves exact substitution across one uint binder when its point
returns. `mxInst_eval` preserves the full optional term evaluation at every
sort. Both reuse the existing update substitution and its landing theorem.
`MxPoint.wk` and `underMemory_eval` prove capture-free weakening, including
failed evaluations. No untyped syntax or new formula constructors are used;
existing formula/term printers apply.

`mxInstances?` refuses any unsupported requested substitution. Its low-level
empty list has a vacuous conjunction; after independent review, the public
`mxInstPrep?` factory explicitly refuses empty requests. Thus an empty point
list cannot bypass the public factory's unsupported-binder refusal.
`MxInstPrep.holds_iff` states the exact interpretation of the output conjunction:
every successful scoped point must satisfy the original body at its pushed
value. A halting point remains in the output as a definedness-guarded instance.
It is neither silently skipped nor evaluated at a default index.

`mxRangeBody?` recognizes only a dynamic primitive-array body with the existing
`length > bound_uint` guard and an equality between that same array's bound-index
read and a primitive literal. It returns `MxRangeView` with a proof of equality
to the actual intrinsic source body. It refuses nested binders, unrelated array
identities, fixed arrays and other shapes. `MxRangeView.prepare` builds the
checked typed instances, always including zero and length. The general finite
instance helper is broader than this recognizer and carries no coverage claim.

### Allocation and reconstruction boundary

`mxRangeInstance_holds`, `mxRangeBody_holds` and `mxRangeBlock_holds` connect the
intrinsic formulas to the actual `State.allocPush` object, its exact length and
optional slots. This includes zero-length vacuity and out-of-bounds reads.
`MxInstPrep.range_reconstruct_points` takes the checked preparation at the old
fresh allocation and constructs a fresh allocation satisfying the original
universal range block. Its finite floor set includes zero, length and precisely
the successfully evaluated point values. The only extra point requirement is a
successful zero instance; the recognized range builder supplies zero.

`mxFloorRebuild_alloc_local` proves every local value, including the new fresh
id, agrees between original and reconstructed allocations in the same extended
heap typing. `mxFloorRebuild_alloc_alias` therefore preserves memory-local
identity equalities, including comparisons with outer memory locals. This is a
one-new-object relation; it does not rebuild arbitrary given-heap objects or
coupled arrays. `mxRangeBlock_negative_iff` connects the committed object-level
finite-instance equivalence to the actual intrinsic universal range block.
Its consequent is still a semantic observation function, not an arbitrary
recognized enclosing `Fml`.

For written-memory hashing, the interface is `MxInstPrep.holds_iff` for exact
successful-point interpretation, `range_reconstruct_points` for realizing the
range block, and the local/alias equalities alongside `MemFloor`'s retained
optional-read vector. A caller must separately establish stability of its
exterior terms and point evaluations across reconstruction. Denote/eval
agreement alone does **not** establish that stability, and no write/hash
composition claim is made.

### Exact failed next construction and remaining reduction

`Examples/MemoryInstantiation.rawPreparedLeaf` retains the concrete attempted
next step: put the checked intrinsic point conjunction in the negative premise
of a fresh primitive-array leaf, with its original exterior read. Its compiled
`mxTop` result is `none`. The points still contain a raw `mlen` term as an index;
`Tm.ixOk` does not admit such memory reads, and the unchanged cut cannot collect
that index at the array binder. `bound_index_not_ground` separately proves that
the original uint-bound index cannot be pulled before its array binder. This
is an implementation/proof obligation, not an external or user-decision blocker.
The failed construction was not repeatedly retried or installed in the closer.

The next unproved transformation must introduce a uint length atom **before**
the fresh array binder, constrain it to the allocated object's actual length,
and replace those length-based point indices by the atom capture-safely. For a
whole negative implication, the proof must relate exterior intrinsic term
observations in the original and reconstructed states, not just their local
identities. In particular, arbitrary `MxPoint.agrees` points could read changed
contents: stability must be derived from a fail-closed whole-leaf collector
(e.g. pre-array `ixOk` indices and preserved lengths). Only then can a
whole-leaf soundness/refutation certificate feed `mxTop`/`decideMem`, coverage,
and an improved original pin. Neither `Calculus/Decision.lean` nor `decideMem` was edited.

### Controls, review and evidence scope

`Examples/MemoryInstantiation.lean` tests capture-preserving removal of one
binder, explicit nested refusal, empty-request refusal, primitive uint/bool
recognition, wrong-array refusal and same second-array identity acceptance.
It also proves failed-point vacuity, uint-top successor halting, empty original
and prepared blocks, a still-halted exterior read, and actual fresh/outer local
alias comparison preservation. Compiled observation order is exported separately.
The initial bound-index collection assertion had a wrong array position; its
failed diagnostic is retained. Skeptic found that the first replacement equality
was vacuous for that same reason. It is now corrected to array position 1 and
thinning both binders into the pre-array context, with a positive ground-index
collection equality under the identical position/thinning. No old observation
or verdict was changed.

Independent read-only finder and skeptic reviews used no Lean server/build.
Both confirmed the empty-list API edge; the public factory now refuses that
request and the low-level vacuity is documented/tested. Skeptic also found the vacuous array-position control; its corrected negative
and positive controls now exercise the intended binder boundary. Finder confirmed
that point agreement is not reconstruction stability; the contract above now
states this explicitly. No theorem hypothesis or verdict was weakened.
These are Lean kernel/compiled observations, not Solidity source/compiler/EVM
executions. Final command records, raw diagnostics, timings, peaks and axiom
output are in `/workspace/next10-memory-negative-block-intrinsic/`.

### Intrinsic continuation validation

All final commands below exited zero. Raw command arguments, UTC intervals,
exit codes and cumulative per-group peaks are in `build-results.json`,
`final-results.json` and `repair-results.json`. The initial failed controls
and proof iterations remain separate. The repaired source's per-file MCP
reports success with partial=false and no Lean errors/warnings; the registered
root also passed per-file diagnostics. `final-diagnostics-and-axioms.json`
extracts the actual final diagnostic and axiom messages.

| Check | Seconds | Cumulative group peak bytes |
|---|---:|---:|
| `mcp-core-final` | 6.19 | 978153472 |
| `core-build` | 3.961 | 978153472 |
| `mcp-controls` | 3.989 | 978153472 |
| `mcp-root` | 2.746 | 610701312 |
| `original-observations` | 24.036 | 610701312 |
| `instantiation-observations` | 1.473 | 610701312 |
| `mcp-controls-repair` | 3.944 | 773373952 |
| `controls-build-repair` | 2.67 | 773373952 |
| `full-confirmation-repair` | 2.032 | 773373952 |
| `orphans-repair` | 0.111 | 773373952 |
| `layers-repair` | 0.143 | 773373952 |
| `automatic-strict-repair` | 0.049 | 773373952 |
| `trust-repair` | 4.097 | 773373952 |
| `inventory-repair` | 0.062 | 773373952 |
| `diff-check-repair` | 0.009 | 773373952 |

The repaired final full confirmation was cache-assisted, not a clean-cache
benchmark. Strict automation reports zero newly timed replayed TestSuite
modules and unchanged 491 automatic, 61 step-budget, zero manual, 11 refuted,
zero pending. Original full-build timing evidence is retained historically.
Trust reports 719 sources, 240 inventoried implementation/recovery sites and
zero findings. Inventory regeneration made no generated-file change and did
not promote support. No repository script changed; external drivers retain
the commands they actually executed.

Measured final groups peaked at 978,153,472 bytes (MCP/build group) and
773,373,952 bytes (repair/final group), beneath the verified 12 GiB cap with
zero swap and no group OOM events. Every check ran with LEAN_NUM_THREADS=1,
explicit library Lean -j1, the documented writer lock and disk caches. The
outer 16 GiB cgroup snapshot is exported separately. The temporary alternate
Lake invocation file is removed after checks; no tracked/user configuration
was changed. Initial runtime-only proof/diagnostic attempts not covered by
these cumulative samples are not presented as measured peaks.

All 21 original ordered verdicts are exactly unchanged, including the original
unknown. Before/after comparisons and baseline-equal hashes of all three
original gap-owning files are exported. The seven new ordered compiled boolean
observations are true/true/false/false/true/false/false for uint recognition,
bool recognition, nested recognition, wrong-array recognition, second-array
recognition, top-successor return and raw-cut success, followed by point/instance
counts (5,5). These observations precede the final control-only repair; those
observed definitions were unchanged by the repair and the final build checked
all corrected controls. No compiler/EVM evidence is implied.

Actual final axiom audits show only propext, Classical.choice and Quot.sound
for substitution, exact successful-point preparation, fresh alias preservation,
point-based reconstruction and the intrinsic block equivalence. The direct
range-body substitution audit uses propext; nested-recognition control uses
propext; no headline audit contains sorryAx or a new axiom. The original
countermodel proofs were not changed; their earlier audits remain historical
evidence. Conditional reconstruction theorems remain conditional theorems,
not an executed original closer certificate.

Final read-only finder and skeptic reviews confirmed the corrected positive
and negative array-position controls and matched the documented boundary.
No production proof changed after its successful diagnostics. Shared tracked
edits are only the new MemInst and MemoryInstantiation modules, their two
Solidity.lean registrations, docs/module-map.md, docs/automation.md and this
owning handoff. MemFloor, callback/invariant semantics and all other lanes
remain untouched. The whole-leaf length-atom/exterior-observation reduction
and actual original closer refutation remain open. The assignment is not
complete despite the new intrinsic instantiator and its gates passing.


## Exact enclosing-leaf integration (2026-10-28)

`MemObserve` adds typed primitive observations, not user term/formula syntax.
Its checked parser reifies to existing intrinsic `Tm` and certifies equality.
It accepts literals, the newly allocated dynamic primitive array's length,
its reads at literal uint indices, and typed binary operators. The exterior
formula view accepts Theory equality, true, negation, conjunction and
implication over those observations. Other locals/arrays, nonliteral indices,
unary/other symbols, modalities and exterior binders are refused. No given-heap,
reference-member struct, recursive type, hash or write support is claimed.

`MemNegPrep` recognizes a fresh dynamic primitive array whose body is an
implication with the existing negative uniform uint range block. Positive
prefix value binders are preserved. A uint length atom is quantified before
the fresh allocation; its equality with the actual length guards the prepared
body. Instances use zero, length, every retained literal exterior read index,
and checked successors of length/read operands. Failed successors stay guarded.
The parser has no fixture-name check. Unsupported shapes return the original
formula and identity certificate. This is a deliberately fail-closed supported
shape inside the unchanged target, not a claim of full decision completeness.

`mxNegativeBody_holds` proves equivalence at every parent state. One direction
chooses the actual length and uses certified instances; the other reconstructs
a primitive array with its length retained and transfers every optional
exterior observation. The object stays in the actual extended heap typing with
the same fresh identity; previous local/alias laws remain applicable. Empty
arrays retain vacuous block truth and failed optional reads; Theory equality
of two halted reads remains distinct from a failed program comparison.
`decideMem` and `memCovered` use the identical preparation, hoisting and cut.
Soundness/refutation transport uses the certificate in the appropriate direction.

`MemoryNegativeDecision.gap_decision` certifies that the actual unchanged
`decideGoal gapMemInnerNeg` returns a refuting state, using kernel coverage,
closer completeness/soundness and the original non-validity theorem.
`gap_returned_countermodel` certifies that very returned state falsifies the
original under the existing hash-premise semantics. This is separate from the
old concrete empty-array countermodel and from compiled Lean observations.
No solc/EVM run or source semantics change is claimed by these intrinsic tests.

The additive interface for written-memory hashing is: supply an equality-
certified typed exterior view and its read footprint; preserve the object's
actual length and every footprint index in the reconstruction breakpoints;
use `MxObs.rebuild`/`MxExterior.rebuild` for exact optional observations and
`MxNegativePrep.exact` for enclosing-leaf transport. This proves no write/hash
composition itself and cannot be reused as a given-heap surgery theorem.

The first integrated source build passed in 934.865 s, aggregate cgroup peak
7,697,956,864 bytes, no cgroup max/oom events, 12 GiB cap/zero swap. It checked
the original changed verdict pin and six ordered uint/bool controls. Headline
exact/returned-state audits list only `propext`, `Classical.choice`, `Quot.sound`.
Review then found the internal `mxLen` fresh prefix did not round-trip through
`FreshNames`. It was repaired to the standard `se` prefix with the whole input's
`Fml.fresh` supply, threaded through preserved binders. This is a printer fix;
indices were intrinsically sound already. Fresh-prefix and nested-exterior
binder-refusal controls now cover the repaired boundary. Final core rebuild
passed in 36.543 s; final verification below will supersede this checkpoint.


### Final validation and remaining boundaries

Actual command arguments, exit codes, UTC intervals and aggregate cgroup
peaks are in `/workspace/next10-memory-negative-block-close/final-results.json`
and the matching raw logs. Every mandatory row below exited zero. The full
confirmation is cache-assisted and rebuilt the changed dependency chain;
TestSuite cache replays are not a clean-cache performance benchmark.

| Command / evidence name | Seconds | Aggregate group peak bytes |
|---|---:|---:|
| `full-confirmation` | 978.852 | 7668064256 |
| `runtime-keysort` | 0.164 | 30494720 |
| `mcp-decision-final` | 38.351 | 1242238976 |
| `mcp-observe-final` | 4.94 | 963260416 |
| `mcp-preparation-final` | 3.923 | 963260416 |
| `mcp-controls-complete` | 19.804 | 1216303104 |
| `mcp-memory-complete` | 54.675 | 1216303104 |
| `mcp-instantiation-complete` | 4.224 | 1216303104 |
| `mcp-countermodel-complete` | 3.178 | 1216303104 |
| `mcp-root-complete` | 2.863 | 1216303104 |
| `original-observations` | 25.712 | 1216303104 |
| `decision-pipelines` | 9.617 | 1216303104 |
| `instantiation-observations` | 1.476 | 1216303104 |
| `floor-observations` | 2.611 | 1216303104 |
| `orphans` | 0.117 | 1216303104 |
| `layers` | 0.154 | 1216303104 |
| `automatic-strict` | 0.036 | 1216303104 |
| `trust` | 3.809 | 1216303104 |
| `inventory` | 0.04 | 1216303104 |
| `inventory-check` | 0.038 | 1216303104 |

The final sequential-check rows share one container, so their peaks are
cumulative within that group. Every group used `LEAN_NUM_THREADS=1`, explicit
Lean `-j1` through the evidence-local temporary Lake configuration, the writer
lock, `memory.max=12884901888` and `memory.swap.max=0`. No cgroup limit/oom
or kill events occurred. `headroom.jsonl` retains actual 16 GiB VM samples,
including 7,761,413,432 bytes conservative headroom near the large fixture
stage (free plus inactive-file/slab reclaimable memory). Disk caches were
preserved. No unrelated process was killed; an early accidentally nested
writer-lock launcher was stopped before any Lean worker started and repaired
by removing the redundant lock.

`run-lean.sh` passed the final core/root and SolkeyTestSuite builds and the
SolKey annotation check (377 taclets, 131 read-bearing, all covered). The
actual final `lake build Solidity.KeySort` output preceded the fresh
`RUNTIME_GATE_PASS` marker. Strict automation retained the unchanged 300 s
TestSuite policy: 491 automatic, 61 with step budgets, zero manual,
11 refuted and zero pending; zero TestSuite cache replays were newly timed.
Trust audited 722 sources, 240 inventoried implementation/recovery sites,
zero findings. Feature inventory regeneration/check passed: 212 features,
783 upstream symbols, no generated diff or support promotion. No repository
script was changed, so no new script behavior is claimed.

Eight final owning-file MCP reports are complete (`partial=false`,
`success=true`, no Lean errors/warnings), extracted in
`final-diagnostics-and-axioms.json`. Earlier 45 s partial diagnostic attempts
remain recorded as failed; the final evidence-local driver omits that wait
truncation after rebuilding imports. This changes neither Lean proof limits
nor test budgets. Some MCP shutdowns print Python event-loop cleanup traces
after delivering a complete successful report; those are retained separately
from the Lean diagnostics. The earlier bare kernel coverage reduction got
stuck at the well-founded exterior parser, and a diagnostic `#reduce` exceeded
the unchanged recursion bound. The repaired proof uses the parser's proved
unfolding equation (`gap_prepared`) before kernel coverage evaluation; no
bound was increased. The original raw-length cut refusal remains a negative
control, superseded by the correctly scoped length atom in preparation.

The final actual axiom audits for `gap_decision`, `gap_returned_countermodel`,
`mxNegativeBody_holds`, `MxExterior.rebuild`, `decideMem_sound` and
`decideMem_refutes` list exactly `propext`, `Classical.choice`, `Quot.sound`.
The positive semantic controls and original negative empty-array certificate
have the same standard axiom set. No new axiom or `sorry` was introduced.
Kernel exact/returned-state certificates are distinct from the compiled Lean
pipeline observations below; no solc/EVM observation is inferred from either.

The ordered 21-fixture before/after comparison is preserved in
`original-observation-comparison.json`: only `gapMemInnerNeg` changes
`unknown → refuted`; all other 20 observations and their ordering are identical.
`original-six-declarations.json` verifies byte-identical source for all six
original gap definitions and six target certificates against the published
base. The original enclosing source files naturally differ only where the
proof-backed verdict pin/comments changed; earlier full-file hashes are
historical, not the current preservation claim.

| New/current fixture | Arithmetic pipeline | Memory / leaf / goal | memCovered |
|---|---|---|---|
| `original` | unknown | refuted / refuted / refuted | true |
| `guardedZero` | unknown | proved / proved / proved | true |
| `guardedWrong` | unknown | refuted / refuted / refuted | true |
| `haltedEqual` | unknown | proved / proved / proved | true |
| `haltedCompare` | unknown | refuted / refuted / refuted | true |
| `boolGuardedTrue` | unknown | proved / proved / proved | true |
| `boolGuardedFalse` | unknown | refuted / refuted / refuted | true |
| `namedPrefix` | unknown | refuted / refuted / refuted | true |

The old floor and instantiation ordered drivers also passed unchanged,
including zero length, out-of-bounds optional reads, failed top successor,
missing-length/guard counterexamples, capture refusal and local identity/alias
certificates. New controls distinguish vacuous guarded truth, wrong live
values, equal halted Theory reads, failed program comparison, uint/bool
arrays, reserved prefix names and unsupported exterior binders/indices/arrays.

Independent read-only finder and skeptic reviews examined reconstruction,
typed recognition, exactness/guard transfer, fresh identity, integration,
coverage correspondence, controls and owning documentation without Lean
server/build access. They found the fresh-name printer issue and stale docs;
both were fixed. The final source review found no remaining confirmed source
or coverage mismatch. Exact review scopes/findings are in `reviews.json`.

The additional global `check-doc-paths.sh` remains exit 1 for 20 pre-existing
external-project file references in untouched `Eqns`/upstream validation
records. `doc-path-baseline.json` proves those citing sources byte-identical
to the published base. Registering the new modules removed the two task-owned
missing references, and the handoff's ambiguous decision paths were made
explicit. No unrelated docs, checker exclusions or policy were altered.
This optional global scan is recorded open; all mandatory assignment gates
above passed. Broader memory blocks, given-heap binders, reference-member
structs and written-memory hashing remain separate work, not residual claims
or a narrowed target. There is no remaining reduction blocker for this
assignment's original gap.

Shared tracked edits in this final continuation: new `MemObserve`, `MemNegPrep`
and `MemoryNegativeDecision`; the narrow `Calculus/Decision` import/pipeline/
certificate transport and identical coverage pipeline; three root imports;
the one justified original verdict pin and task-local example comments;
`docs/module-map.md`, M7 in `docs/automation.md`, and this owning handoff.
Earlier committed `MemFloor`/`MemInst` results are preserved. No other task,
monitor, user setup, callback/invariant/profile or resource policy was changed.


Both independent reviewers then rechecked the actual final source, diagnostics,
full/strict/resource logs, standard-three axiom audits and ordered comparisons.
Neither found a remaining mandatory proof/validation blocker or unsupported
completion claim. The optional global documentation baseline remains explicitly
open. Final whitespace and retained toolchain/branch/base identity checks also
exited zero; their raw commands/results are in the same evidence directory.
The temporary Lake resource configuration is preserved there and removed from
the checkout before commit, leaving tracked and user configuration intact.
