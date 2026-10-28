# Upstream Solidity tests

The complete `test/` tree from Solidity **v0.8.38**, commit
`1835d247de183f23e7b0e2bc4a50732af525b77c`, is stored in
`tests/upstream/solidity-0.8.38.tar.gz`. This matches the language inventory's
pin. The archive also includes Solidity's license and the complete schema
submodule at `937e3484cb4cf408a4e808d62f34285a71fece80`.
`tests/upstream/snapshot.json` records all 11,622 regular files, their sizes,
SHA-256 hashes, repository revisions and the archive hash. Upstream inputs
and expectations are preserved without editing. Keeping them compressed
avoids adding thousands of unrelated source files to normal repository scans.

## Separate result lists

The recorded run is in `tests/upstream/results/` (counts and the observed
via-IR modifier differences: [the corpus summary](../tests/upstream/README.md)).
It is a baseline of base commit `cadb628c`; the model source hash is in
`summary.json`. Re-run the adapter to measure a newer model.

| File | Meaning |
| --- | --- |
| `working.json`, `working.txt` | Fixtures whose adapted expectations actually matched. |
| `broken.json`, `broken.txt` | Observed frontend import/call gaps or mismatched expectations, with reasons and available evidence. |
| `blocked.json`, `blocked.txt` | Fixtures requiring an unimplemented adapter, host/configuration, or more execution resources. These are not passing or demonstrated semantic bugs. |
| `summary.json` | Counts, compiler/source hashes, model hash, execution scope and completion flag. |
| `results.json` | Combined fixture verdicts and run provenance. |
| `file-coverage.json` | Every archived file, including native C++ suites, extensionless command-line assets, harnesses and support files. Unrun native assets are explicitly recorded. |
| `retries/*.json` | Complete isolated retry reports, including their distinct timeout/batch settings; the combined report retains their hashes and paths. |

Counts are **fixture/reference files**, not individual C++ tests or assertions.
The main verdict lists cover `.sol`, `.yul`, `.json`, `.stack`, `.ssa`, `.asm`
and `.asmjson` inputs. The exhaustive file ledger accounts for everything
else. A file's presence in the archive is not evidence it ran.

Two different checks have different meanings:

* `compiler-diagnostics` compares syntax-test diagnostics with the exact
  upstream expectations: diagnostic kind, number, order, source name,
  byte offsets and complete message. Expected compiler rejections count
  as working when their diagnostics match. This runs the SHA-pinned **solc
  reference**; it does not demonstrate Lean frontend or interpreter coverage.
* `lean-runtime` imports the contract through the repository's modern source
  admission and typed `solc_import`, then compares supported scalar runtime
  vectors with the typed Lean interpreter. Calls retain state in order,
  constructors/initializers run, failed calls roll back, and return values
  are compared as ABI words. Default/explicit `compileViaYul: also` fixtures
  must match in both legacy and via-IR source evaluation modes. `true` or
  `false` selects its requested single mode. The combined verdict retains
  each mode's observations and gaps.

Runtime results are observations, not universal correctness proofs. They do
not exercise generated solc EVM/SSA code, the repository's EVM compiler, gas
costs or the upstream C++ EVM host. Unsupported gas/log/revert-data checks,
aggregate/dynamic/bytes ABI inputs, noncanonical calldata, external host
behavior and source imports remain blocked rather than being dropped.
Only empty-data function failures are currently replayed; the model's generic
panic cannot certify an expected ABI panic code. Loop fuel is 1,000 per loop;
exhaustion or a process timeout is blocked, never a matching expected failure.
Unsupported compiler configurations and EVM-version constraints are likewise
explicit. Other upstream families (SMT checker, Yul optimizer, AST/NatSpec
goldens, command-line and native unit tests) are preserved and inventoried but
need their own adapters. A whole-suite `complete` flag means every selected
fixture has a verdict, including blocked cases; it does not mean all suites ran.

An [optional bounded reference EVM replay](../scripts/evm-reference/README.md)
executes pinned compiler bytecode separately. Its `evm-reference` reports retain
all adapted scalar observations, machine exceptions and provenance; they never
merge into Lean coverage or convert model exhaustion into an expected failure.
The Group 03 continuation records both methods' per-fixture results.

## Reproduce

Use Lean 4.24.0 from `lean-toolchain`, Node, Python 3 and `tar`.
No dependency is added to the core Lake package.

```sh
# Verify and extract all files into the ignored .lake/upstream/solidity/.
node scripts/solidity-upstream.mjs verify

# Download the exact external reference compiler if it is not already present.
curl -fL \
  https://raw.githubusercontent.com/ethereum/solc-bin/gh-pages/bin/soljson-v0.8.38+commit.1835d247.js \
  -o /tmp/soljson-v0.8.38+commit.1835d247.js

# The runner checks the compiler's SHA-256 and full version before using it.
node scripts/solidity-upstream.mjs run \
  --compiler /tmp/soljson-v0.8.38+commit.1835d247.js

# Focused rerun (keep its result directory separate from the complete report).
node scripts/solidity-upstream.mjs run \
  --compiler /tmp/soljson-v0.8.38+commit.1835d247.js \
  --filter semanticTests/arithmetics --out .lake/upstream/arithmetic-results

node --test --test-isolation=none scripts/solidity-upstream.test.mjs
lake --no-build lean tests/upstream/Replay.lean -- --tstack=131072
```

The runner builds `Solidity.Tools.Upstream` once. Lean runs in batches of 16
mode-specific imports with a 120-second process limit. Results are checkpointed
after each fixture/mode and saved after each batch. `--timeout-ms` and
`--batch-size` adjust those limits. `--resume` reuses completed file verdicts
only when compiler, archive, runner, model and configuration hashes match.
No source changes or test expectation changes are needed to rerun failures.
Exit 0 requires no broken/blocked fixtures; 1 records an incomplete-compatible
suite; 2 indicates an invocation, integrity or initial build error.

If a batch times out, completed mode checkpoints survive, but later fixtures
in that process may not have started. Retry an interrupted fixture with its
entire snapshot path as `--filter`, `--batch-size 1`, and a separate `--out`.
After the full run finishes, merge the isolated reports with:

```sh
node scripts/merge-solidity-upstream-retries.mjs \
  tests/upstream/results /path/to/isolated-retry-results
```

The merger requires identical compiler, snapshot, runner, model and execution
scope. It retains conclusive mode observations, refuses contradictory verdicts,
stores each retry's original report, and records its SHA-256 and configuration.
This prevents an expensive earlier fixture from concealing the results of
otherwise runnable tests.

To recreate the snapshot from Git, initialize the schema submodule and run:

```sh
git -C /path/to/solidity checkout 1835d247de183f23e7b0e2bc4a50732af525b77c
git -C /path/to/solidity submodule update --init test/ethdebugSchemaTests/ethdebug-format
python3 scripts/snapshot-solidity-upstream.py /path/to/solidity
```

## Tests

`node --test --test-isolation=none scripts/solidity-upstream.test.mjs` covers
fixture boundaries, preamble offsets, exact diagnostics, pipeline defaults
(an omitted `compileViaYul` means `also`), malformed calldata, signed ABI
words, the exhaustive partition and retry merging; `tests/upstream/Replay.lean`
covers deployment initializers, stateful sequencing, rollback, real
mismatches and inconclusive fuel/panic outcomes. The new `evalExpr` site of
`Tools/Upstream.lean` is in the trust inventory.

## Group 01: viaIR modifier return slots (2026-10-26)

Task branch `fix/group01-modifier-returns` starts at current `origin/master`,
`006fcd593f5beeb540e7adf2bc76de4638566924`. The managed executor passed the
runtime gate with Lean 4.24.0 (`797c613`), Lake 5.0.0, and
`lake build Solidity.KeySort`. The saved setup is activated with
`source /workspace/.setup/activate.sh`; no scratch toolchain is involved.

Both historical mismatches reproduced on this base, before editing:

| Exact fixture under `test/libsolidity/semanticTests/modifiers/` | Required pipeline | Before | After |
|---|---|---|---|
| `function_modifier_loop_viair.sol` | viaIR | broken: `f()` returned 10, expected 1 | working: 1 |
| `function_modifier_multi_invocation_viair.sol` | viaIR | broken: false returned 1, true returned 2; expected 1 for both | working: 1, 1 |
| `function_modifier_loop.sol` | legacy | historical working control | working: 10 |
| `function_modifier_multi_invocation.sol` | legacy | historical working control | working: 1, 2 |
| `function_modifier_return_reference.sol` | legacy and viaIR | historical working control | working: 2, 3 in each pipeline |

The last fixture concerns assignments to primitive named returns in modifier
arguments, despite its filename. No assigned case was already fixed on the
current base. Every exact-path run uses `--batch-size 1` and a distinct output
directory. Complete selected reports, fixture SHA-256 values, model/compiler/
runner/archive hashes and exact commands are preserved in
[the Group 01 evidence](../tests/upstream/group01/validation.json).
Historical `tests/upstream/results`, the pinned archive, source bytes and
expectation bytes remain unchanged. The first loop attempt stopped during an
overlapping runner build with Lean exit 135; the isolated sequential retry
completed and supplies the before observation. This build failure is not a
semantic observation.

The pinned legacy `ContractCompiler.cpp` initializes function return slots once,
then recursively emits modifier/body blocks from `appendModifierOrFunctionCode`
without reinitializing them at placeholders. The pinned `IRGenerator.cpp`
functions `generateModifier` and
`generateFunctionWithModifierInner` distinguish incoming return slots from
latest result slots. Every placeholder receives the modifier's incoming
slots and fresh parameter slots. Results initialize before modifier arguments;
arguments can change incoming named returns; a skipped body leaves the initial
result. The lowering now mirrors those boundaries using typed declarations,
blocks and result assignments. Primitive slots retain their widths and ABI/
function markers; reference parameters and memory returns retain aliases.
The new `EvalOrder.modifierFrames` flag is independent of operand order and
is enabled by `EvalOrder.viaIR` and modern viaIR import provenance.
Legacy keeps its previous expansion.

The finder and independent skeptic reviewed the patch read-only, without
Lean workers. They confirmed fixes for separate configuration, complete nested
slot metadata and memory-return aliases. Their findings prompted enum packed
ABI, nested enum, function-slot, storage-rebinding and memory-return controls.
Native controls also cover argument mutation of named returns, skipped bodies,
nested placeholders, parameter resets, narrow overflow and tuple results.
No further concrete lowering defect was found. General source-lowering
agreement for arbitrary bodies is not established by these controls.

Storage-valued returns under viaIR modifiers are an explicit remaining
exclusion: preserving an unset incoming storage alias needs a representation
that copies its optional binding without reading it. Such calls now fail
elaboration with a pinned diagnostic instead of inheriting legacy slot reuse.
This is a compatibility restriction, not passing coverage. Memory returns
are supported. Core statement/run/rule representations and their soundness
proofs are unchanged; no dependency enters the core or optional Bridge.
The configuration record gains one flag and generated frames add local
copies, so dependent modules rebuild and proof terms may grow. Inspection of
`git log` for the lowering found no speed-motivated change being reversed.
No proof limit is raised.

Reference and regression commands (after activation):

```sh
node scripts/check-modifier-frames.mjs \
  /tmp/soljson-v0.8.38+commit.1835d247.js /tmp/group01-reference/node_modules
lake env lean --tstack=131072 tests/upstream/ModifierFrames.lean
lake env lean --tstack=131072 tests/upstream/ModifierFrameProofs.lean
node --test --test-isolation=none scripts/solidity-upstream.test.mjs
lake --no-build lean tests/upstream/Replay.lean -- --tstack=131072
node scripts/check-automatic.mjs --strict
node scripts/check-orphans.mjs
node scripts/check-layers.mjs
./scripts/check-testsuite.sh --solkey tests/migration/solkey/keyext.solidity.examples
```

The optional EVM runner uses external EthereumJS vm/common/util 10.1.3 and
ethers 6.17.0, outside the Lean package. All **40** vectors pass, 20 per
pipeline, with SHA-checked solc 0.8.38, optimizer enabled and Cancun. These
are separate compiler/EVM observations; the upstream Lean runner retains its
recorded Osaka configuration and fuel 1,000. All 14 JavaScript tests, existing
Lean replay checks, reachability (667 modules), layering (143 core modules),
strict automation (0 pending) and frozen TestSuite audit pass. Documentation
paths retain the 13 baseline missing references. Long build/diagnostic logs
are retained under `.lake/upstream/group01-logs/`.

Final proof/build/sort/corpus outcomes are recorded in the evidence manifest;
resource exhaustion or incomplete checks are not counted as passing.

### Group 01 final gate evidence

The final per-file checks pass for Raw (6.0 s), Lower (27.9 s), Arms
(93.9 s) and Import (19.3 s). The 34 native runtime/configuration/exclusion
controls pass (16.5 s). Four fixed-program semantic validity proofs pass,
with exact axiom-output pins allowing only `propext`, `Classical.choice`
and `Quot.sound` (47.1 s). They establish the model's outcomes for the two
affected programs and their distinct legacy controls; they are not a
source-lowering simulation for arbitrary bodies. No Lean MCP tools were
exposed, so checks used the configured per-file Lean commands.

All three existing focused source regressions pass (195.1 s): modifiers,
inheritance modifier dispatch and constructor wrapping. Their deliberately
false/narrow-overflow obligations retain the expected pending statuses.
This existing harness uses the frozen 0.8.34 compiler; the assigned upstream
fixtures and independent EVM controls use SHA-checked 0.8.38.

The complete current modifier family has 31 verdicts: **9 working, 17 broken,
5 blocked**. Both assigned cases now work, and all seven historically working
family fixtures still work. The other cases remain missing getter adapter
entries, library state-type visibility gaps, transient-state exclusion, or
unadapted aggregate/host/revert-data observations. Actual `variants[].gaps`
were inspected and the complete report is retained in `group01/after-family.json`.
Comparison with historical statuses is not a fresh base rerun of the
unassigned gaps, and none are called passing by dropping their observations.

The TestSuite build passes all 249 jobs (725.4 s observed), and current
artifacts pass a no-build confirmation after an environment refresh detached
its original controller. The frozen sort gate reports 377 taclets, 131
read-bearing annotations and zero mismatches. `SolidityCorpus` builds
(64.2 s), and the frozen corpus gate passes without verdict drift (24.2 s).

The first cold default build completed 642/649 targets in 71m37s without
semantic errors before a controlled resource stop. OpenLoops completed in
1186 s immediately before the stop; DecisionHashes remained active while
the combined workers approached this executor's 16 GiB cgroup memory cap. The
historical baseline also left the broader decision-example build inconclusive;
that is not a fresh current-base performance comparison. A bounded single-worker
tail retry is recorded separately in the evidence manifest.

Shared integration changes are limited to Raw's configuration flag, Import's
legacy constructor arity, Arms' flag selection and Lower's frame implementation;
apply these together. No upstream runner edits or unpublished sibling patches
are required. Historical corpus inputs/results, proof limits, core dependencies
and optional Bridge remain unchanged.

The single-worker tail retry passed `Examples/DecisionHashes.lean` in 417 s,
then reached its fixed 900-second timeout while checking the unchanged
`Examples/Decision.lean`. At that handoff the default build remained **resource-blocked at
643/649**, not passing; the completion below supersedes that status. No semantic error was emitted. Its source files are
unchanged by this patch; the historical baseline had an inconclusive broader
decision-example build, but no fresh current-base timing comparison was made.
All focused, formal, source, TestSuite, frozen sort and frozen corpus gates
passed. Long logs and process/resource records are retained, with log digests
in the evidence manifest.

The final read-only finder and independent skeptic passes found no remaining
concrete defect or overclaim, opened no Lean workers, verified report/control
hashes and the exact Node model digest, and confirmed the stated proof,
exclusion and resource limits. No historical input/result was modified, no
axiom or proof-limit override was added, and no push or merge to master was
performed.


### Group 01 default-build completion (2026-10-27)

Resumed the same branch at `bfad51e3`, preserving its implementation, reports
and historical inputs. The managed Lean/Lake/KeySort runtime gate passed again.
No stale Lean worker existed. The configuration field invalidated downstream
artifacts, but the decision examples do not exercise modifier frames.
`Solidity/Examples/Decision.lean` is byte-identical to the base. No fresh base timing A/B was
performed, so these measurements do not establish a performance regression
or its absence. No Lean source, algorithm, proof limit or representation
changed during this completion.

Scratch boundary profiling located the existing `sortedLe` verdict at 198 s
and the later ledger verdict group at about 105 s. Profiling also injects
timing messages into `#guard_msgs`; that diagnostic was stopped and is not
a passing check. Uninstrumented builds supply the final evidence.

All remaining modules were then built separately with `LEAN_NUM_THREADS=1`,
one Lean worker at a time, a 90-minute per-target ceiling and a 14,500 MiB
process-tree RSS ceiling. Neither ceiling was reached; RSS and worker counts were sampled every two seconds:

| Target | Result | Elapsed | Sampled peak process-tree RSS |
|---|---|---|---|
| `Solidity.Examples.Decision` | pass | 758.7 s | 5.14 GiB |
| `Solidity.Examples.DecisionKInt` | pass | 6.0 s | 1.63 GiB |
| `Solidity.Examples.DecisionMemory` | pass | 56.3 s | 1.45 GiB |
| `Solidity.Examples.DecisionArrays` | pass | 2383.1 s | 11.74 GiB |
| `lake build` | **pass, 649 jobs** | 4.0 s after those builds | 0.53 GiB |

Fresh exact-path fixture runs, each with `--batch-size 1` and a distinct output
directory, pass both assigned viaIR cases and all three existing control
fixtures. Every fresh report is byte-identical to its preserved committed
after-report, including all observations, pipelines and provenance hashes.
The model digest remains `56dd5f976067a9756c551481228d26769877179c03f75e87cf69c5ae27ab4402`.
The compiler lost from `/tmp` at reconnect was restored and SHA-checked.

The 34 native controls and four semantic proofs with exact standard-axiom
pins pass again, as do all 14 runner tests, existing replay, strict automation,
reachability, layering, cached TestSuite build/audit, frozen sort and corpus
build/check. The prior 40 EVM vectors and three focused source regressions
remain retained evidence; they were not rerun in this completion.
Storage-valued modifier returns remain excluded, generic source-lowering
agreement remains unproved, and the unassigned family gaps remain outside
this lane. No broader family rerun or universal compiler theorem is claimed.

Exact commands, terminal results, fixture/report hashes, resource measurements
and log digests are in [the completion evidence](../tests/upstream/group01/resume-validation.json).
The old incomplete attempts remain recorded. The documentation-path gate
retains the same 13 missing references; none were introduced here.

The final read-only finder and independent skeptic verified the terminal logs,
commands, report/model/compiler hashes, five byte-identical fixture reports,
proof scope and remaining exclusions. Neither opened Lean workers. Their
precision fixes distinguish the 16 GiB cgroup limit and sampled RSS peaks.
The original implementation commit remains intact; the completion commit
records evidence only. No push or merge to master was performed.

## Group 02 callable-entry repair

The group 02 branch starts at `006fcd593f5beeb540e7adf2bc76de4638566924`.
The historical result directory and pinned archive remain unchanged. All 67
assigned missing imported-function rows were reproduced before editing, with
one exact fixture filter and `--batch-size 1` per output directory. New replay
results distinguish resolved entrypoints from deeper initialization mismatches
and explicit getter/import limitations. Runtime agreement remains observational.
Implementation and read-only review details are recorded in
[the declaration milestone](feature-work/declarations-metadata.md#group-02-upstream-callable-entry-replay-2026-10-26).

The additional source controls run with:

```sh
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
lake build Solidity.Tools.Upstream
lake env lean --tstack=131072 tests/upstream/InitializationOrder.lean
lake env lean --tstack=131072 tests/upstream/Entrypoints.lean
lake --no-build lean tests/upstream/Replay.lean -- --tstack=131072
node --test --test-isolation=none scripts/solidity-upstream.test.mjs
```


Final assigned result after initialization-order completion: **67 working,
zero broken, zero blocked, zero exclusions**, across all 131 required pipeline
runs (65 legacy, 66 viaIR). Neither upstream inputs nor expectations changed.
The viaIR constructor-order case now returns `x = 2`; the independent legacy
companion still returns `4`. The state-initialization case now completes all
eight expected calls, including `c = 51` and the five previously unobserved calls.

The complete [per-fixture handoff](../tests/upstream/repairs/group02.md) links
all before/after reports, exact commands, required pipelines, raw and compiled
source hashes, compiler/archive/runner/model hashes and timings. Historical
model hash `c042a72f…` belongs to the imported `cadb628c` run; fresh master
reproduction uses `c86945ed…`, the first repair `87539855…`, and completed repair
`4def0e38…`. Every earlier report remains retained as a distinct phase.
Runtime agreement is observational, with no claim of universal compiler
correctness. Eleven kernel-checked initialization controls are in
`tests/upstream/InitializationOrder.lean`; their source is independently pinned
for both legacy and viaIR. Reproduce the completed 67-fixture run with
`bash tests/upstream/repairs/group02-init-commands.sh`.

The Group 10 continuation from `c31e76b6` is recorded separately in
`tests/upstream/group10-resume-results.json`: all 437 original fixture paths,
175 agreements / 102 failures / 160 blocks, with 57 new agreements and no
regression of the previous 118. Its source/model/compiler hashes, per-fixture
commands and complete required-pipeline observations are retained there;
`tests/upstream/group10-resume-validation.json` records final checks. Previous
Group 10 evidence and historical imported results remain unchanged. See
[ABI M4](feature-work/abi-hashes.md#m4-group-10-continuation-from-c31e76b6-2026-10-27)
for soundness boundaries, independent reviews and remaining actionable failures.

The five admitted execution mismatches from that replay are repaired in the
separate [ABI M5 continuation](feature-work/abi-hashes.md#m5-repair-the-five-admitted-execution-mismatches-2026-10-27).
Its fresh inventory covers all 175 prior agreements, the five exact failures,
and six directly affected elaboration failures. The other 251 prior reports
are retained explicitly as not rerun; their behavior after the shared changes
is not certified. New evidence uses `tests/upstream/group10-five-results.json`
and `tests/upstream/group10-five-validation.json`, preserving all earlier
reports, source bytes and expected observations.

The [Group10 ABI M6 continuation](feature-work/abi-hashes.md#m6-aggregate-custom-errors-and-compound-decoder-metadata-2026-10-27)
repairs the two aggregate custom-error failures and three reproduced compound
decoder metadata gaps. New results and validation use separate
`tests/upstream/group10-aggregate-results.json` and
`tests/upstream/group10-aggregate-validation.json`; every earlier report and
export is preserved. Selected fresh replay never certifies retained unrun
import/profile/host/configuration/resource cases against a changed model.

## Coverage step 2: source-unit replay (2026-10-28)

The current-master reproduction and compilation-unit increment are recorded in
[step2-source-units-results.json](../tests/upstream/step2-source-units-results.json)
and [step2-source-units-validation.json](../tests/upstream/step2-source-units-validation.json).
The unchanged 39-fixture family moves from 39 provenance blocks to 31 working,
one broken excluded-assembly case and seven retained host/format blocks.
All 64 prepared legacy/viaIR jobs retain their checkpoints; no gas, log,
host, assembly or expected-failure observation is removed to claim agreement.
The remaining 14 required variants are explicitly unexecuted. The full
repository Lake build was initially blocked by the no-fork validation cap.
A later existing-Docker retry solves process creation but stops at the
documented memory reserve (exit 137 after job 246/688), so the combined build
still is not passing evidence; see the
[runtime audit](../tests/upstream/step2-source-units-runtime-audit.json).
The frontend closure, new kernel controls and focused/static gates have
separate evidence. These model observations are not compiler/EVM equivalence.
