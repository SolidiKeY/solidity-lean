# Written-memory/hash composition (partial)

The original `gapWrittenMemory` is **not closed**. Its statement, `inTarget`
certificate and unknown verdict remain unchanged, as do all six original M7
gaps, waivers, exclusions and `DecisionTheorem`. This branch delivers proved
independent composition helpers, not a complete decision procedure or a new
source-support verdict.

## Proved scope

[HashWritten.lean](../../Solidity/Calculus/HashWritten.lean) adds:

- Normalized byte-input equality as equal lengths and bounded pointwise byte
  equality. Values are reduced modulo 256; equality of full uint words would
  incorrectly distinguish 1 and 257.
- The actual successful heap-write input observation, preserving every other
  byte. The success witness is mandatory: out-of-bounds `List.set` alone is
  not a successful Solidity memory write.
- `hashEq_iff_input` under the existing formula-local finite `HashFree`
  premise, with set-local identity witnesses. The converse excludes
  `ecrecover`; forward congruence reuses the existing all-kind theorem.
- `hashFree_lands` and `hashEq_afterT_iff`, including arbitrary actual memory
  updates. Both modalities retain their exact failure/exhaustion branch.
- An intrinsic `HashInputReduction` certificate whose correctness explicitly
  retains the original premise and the binder-local reading. Its `cut` and
  `cut?` use the existing hoist 1024 and `mxTop`; the soundness and refutation
  adapters reuse `decideMem`. A refutation requires the actual original hash
  premise at the same prestate. No global injectivity assumption is added.

[DecisionWrittenMemory.lean](../../Solidity/Examples/DecisionWrittenMemory.lean)
checks a certified positive composition, actual write/input/hash observations
for every kind and both aliases, modulo-equivalent bytes, unequal tails and
lengths, actual distinct family hashes, invalid recovery inputs with equal
outputs, zero-length box/diamond writes, and an unset local. Its full ordered
18-path matrix is retained before and after this patch.

## Exact remaining dependency

`decideHash` still does not extract `HashInputReduction` for the original pin.
The required intrinsic input comparison has equal lengths and a universal
comparison of normalized array bytes, including bytes after the write. At
negative polarity it needs exact finite instantiation and reconstruction of
memory arrays, not merely sampled indices. `MemSwap.mxIdx`/`mxAt?` currently
require an index to thin to the array's binder; a comparison index bound
inside that scope is not a supported read-table entry. `HashSwap.sw1?` rejects
memory updates and `Tm.mx` rejects hash operands, so chaining the two existing
deciders does not repair this boundary.

The missing memory-array realization/floor proof is the independently owned
`gapMemInnerNeg` prerequisite described in [M7](../automation.md). After it is
available, this lane still needs the intrinsic comparison/certificate producer
and its scope-correct lifting through the original fresh-array binders, then
sound countermodel transfer with the existing finite premise. The current
certificate consumer asserts none of that production or coverage. No other
VM's unmerged work was inspected, copied or contacted.

## Repository and resource evidence

- Checkout: `/workspace/solidity-lean`; origin:
  `https://github.com/SolidiKeY/solidity-lean.git`.
- Branch: `codex/next10-written-memory-hash`, based on published master
  `f4dee4a29c2e208b36db4a4161a4723c735cd775`; fetched ancestry confirmed.
- Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
  Lake `5.0.0-src+797c613`.
- Saved setup activation was required; no setup/user file was changed.
- Writes/checks use the documented writer lock. Heavy checks are serialized;
  no Lean server runs with a build. `LEAN_NUM_THREADS=1` and an untracked
  alternate TOML pass explicit `-j1`; no proof, fuel, node or test budget changes.
- The verified local Docker cgroup has `memory.max=12884901888` and
  `memory.swap.max=0`, beneath the attached executor's 16 GiB parent limit.
  Cgroup peak measures the whole group, including its page cache; it is not
  mislabeled as an individual process's RSS. Caches remain on disk.

The actual startup KeySort gate passed before `RUNTIME_GATE_PASS` was written:
`lake -f lakefile.next10.toml build Solidity.KeySort`, exit 0, peak 24,862,720
bytes. An initial Lake `-j1` invocation failed because Lake has no such option;
the documented weak-Lean-argument TOML repaired it, without budget changes.
Both logs are retained.

The unchanged baseline `lake -f lakefile.next10.toml build
Solidity.Examples.Decision` passed all 309 jobs in 3,238 seconds, including the
original verdict pin and target certificates. Aggregate cgroup peak was
10,657,259,520 bytes (9.93 GiB); no OOM. `DecisionHashes` took 275 seconds,
`Decision` 607 seconds. The standalone 72-observation fixture matrix passed
in 5 seconds, peak 175,456,256 bytes.

## Before/after observations

| Fixture | Before | After |
|---|---|---|
| Original written-memory pin | unknown in all 18 tested paths; inTarget true | Identical unknown observations; inTarget true |
| Written self-hash box | unknown in all 18 paths | Certified composition proved; dispatcher observations unchanged |
| Input self box | mem and goal proved; other 16 paths unknown | Pinned unchanged |
| Input diamond | mem and goal refuted, preheap length 0; other 16 unknown | Pinned unchanged |

The paths are `decideMem`, the three supported `decideHashK` kinds, six
ordered two-kind paths, six ordered three-kind paths, `decideHash` and
`decideGoal`. Full tuples, including ordering and refutation preheap
observations, are in the retained logs, not replaced by aggregate counts.

## Kernel audits and evidence boundary

The checked `hashInput_write_index` uses only `propext`. The audited update,
cut, decision-transfer and fixture theorems use only `propext`,
`Classical.choice`, `Quot.sound`; their exact outputs are `#guard_msgs` pins.
No new axiom or admitted proof is in the patch. Initial MCP failures and
subsequent successful repairs are retained; failed iterations are not passes.

These are kernel proofs about the existing intrinsic model and compiled
Lean regression observations. This patch introduces no Solidity source or
compiler/EVM semantic change. It does not claim a new solc/EVM conformance
result or source-support coverage from the helper proofs. The existing hash
implementations and finite computed-family proofs are reused unchanged.

## Validation and review status

Per-file MCP checks for both changed Lean files passed with no errors or
warnings, including actual axiom audits. The assignment module command-line
build passed (7 seconds, 227,266,560-byte cgroup peak). All 72 ordered
before/after observations are byte-identical, SHA256
`b5d5fe134d852fb2139275ecbb07164b470e9bd903731f42e8ada7609dae6547`.

The required repository gates passed: 702 reachable modules, no orphans;
152 core modules with no elaborator reachability; strict automation has 491
automatic, 61 step-budget proofs, 11 refuted and zero manual/pending;
trust has 716 sources, 240 inventoried sites and zero findings. Inventory
regeneration/check passed with unchanged 212 features and 783 upstream
symbols. Generated files and support classifications have no diff.

The first `./run-lean.sh` passed the default library (687 jobs), including
`DecisionMemory`, `DecisionArrays` and both new modules, but the parent-
headroom guard stopped it during `TestSuite/Derived17.lean`: exit 137 after
5,933 seconds. Docker reported no OOM kill, and parent OOM counters stayed
zero. Available headroom, computed as parent limit minus current plus inactive
file cache, fell to 1,001,287,680 bytes below the 1 GiB threshold. That stopped
run is retained as a failure. Its inner peak was not emitted because the
container was stopped; no exact inner peak is claimed for it.

The distinct repair was runtime-only serialization: `-DElab.async=false` in
the temporary weak arguments. `Derived17` has ten large proof declarations
and no async override. No source, proof/search/node/test budget or verdict was
changed. Lake's `LeanConfig.lean` documents weak arguments as not affecting
build-result traces. The isolated retry retained explicit `-j1`, the 12 GiB/
zero-swap cgroup, the same headroom threshold, and an explicit 300-second wall
limit. It passed in 133 seconds (135 seconds command wall), with exact cgroup
peak 10,500,837,376 bytes (9.78 GiB), no OOM, and minimum sampled available
headroom 1,841,979,392 bytes. The guard did not stop it.

The full `./run-lean.sh` then passed from the checked cache with serialized
elaboration: default library, complete SolkeyTestSuite (259 jobs) and the native
SolKey checker (377 taclets, 131 read-bearing annotations, all matched).
Command wall was 368 seconds and exact aggregate cgroup peak 5,992,030,208
bytes (5.58 GiB), no OOM. The resumed headroom guard did not fire; monitoring
coverage and samples are retained. This is a passing checked-cache confirmation,
not a claim that a cold build fits this VM.

The unchanged timed strict gate passed against the combined actual build logs:
26 TestSuite modules timed, maximum 173 seconds (`Derived7`), within the
unchanged 300-second budget. Cached replays are not counted as timed modules.
No stopped or failed iteration is counted as a passing check.

Draft finder and skeptic independently reviewed the input/update/cut scope
without Lean server access. Both confirmed the finite-premise and successful-
write conditions and required the missing certificate producer to remain
explicit. Confirmed proof-normalization findings were fixed through per-file
MCP goals and multi-attempt checks. Final finder and skeptic reviews covered both actual Lean modules, the 72
ordered observations, concrete write/input/hash and alias controls, all boundary
controls, audits, registrations and owning documentation. Neither used the Lean
server, builds or edits. Both found no confirmed defect. Their nonblocking limit
is retained: the positive certificate consumer control is reflexive and does
not directly instantiate `hashEq_afterT_iff`; the generic bridge has its own
kernel proof/audit. This is not an end-to-end reduction of the original pin.
Reviewed source hashes are recorded in the external review record and remain
unchanged after review.

## Handoff artifacts and shared edits

Raw evidence and reproducible bounded runners are under
`/workspace/next10-written-memory-hash-evidence`. Exports are `/workspace/next10-written-memory-hash.patch`,
`/workspace/next10-written-memory-hash.sha256`,
`/workspace/next10-written-memory-hash-handoff.md`, and
`/workspace/next10-written-memory-hash-evidence.tar.gz`. Commit identity,
per-command exit/time/peak values, source hashes and raw logs are in the evidence
manifest. The original pin remains blocked by the negative-array dependency and
certificate producer; the assignment is not marked complete.

The task-specific TOML is exported inside the evidence directory and removed
from the checkout before commit. For reproduction, copy it back to
`/workspace/solidity-lean/lakefile.next10.toml`, use the retained bounded runner,
and remove it again afterwards. On-disk build caches are preserved.

Shared edits are only the two root imports in `Solidity.lean`, two module-map
rows, one Lean-only correspondence row, and the M7 link to this handoff. The
feature inventory is regenerated by its audit script, without hand edits or
support inflation. All implementation/proof controls are additive files unique
to this task. No push, merge, cherry-pick or other VM/monitor change is authorized
or performed.
