# VA1 decision lane: setup and open work

Status: **partial; VA1-Q1 boundary revision authorized; AU01/AU02 work active**, 2026-11-01. Base `8bd8742ad987d566f7ba7624372cec1c020be07c`,
branch `codex/solidity-automation-20261031/va1-decision`, checkout
`/workspace/solidity-lean`. Exact AQ1/AQ2 receipt is recorded in
[solidity-scope.md](../solidity-scope.md), checkpoint
`717069361a21755914e78caf13d1df2ca76a0284`. No full implementation/completion claim.

## Runtime recovery

Existing official release `/workspace/.setup/tools/lean-4.24.0-linux`:
Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake 5.0.0-src+797c613. No installation required. The existing activation
script remains unchanged; task commands override threads to 1 and open files to 2.

The local managed Docker daemon reports 28.4.0. Unprivileged task containers
use UID/GID 1000:1000, network none, identical `/workspace` mount and
`--memory=12g --memory-swap=12g`. Actual cgroup files report
`memory.max=12884901888`, `memory.swap.max=0`. No LSP/build overlap.
Writer lock held outside the container. No daemon changes or other containers touched.
Image: Debian bookworm-slim digest
`sha256:99c0b25c46d0214d5a2091092e7908907dcaecd6a962cde0ac700acee222b6f3`.

First KeySort command failed: `lake lean -j1 --tstack=131072 Solidity/KeySort.lean`,
exit 1, unknown short option `-j`. Corrected per `lake help lean`:
`lake lean Solidity/KeySort.lean -- -j1 --tstack=131072`, exit 0, `KEYSORT_PASS`.
A measurement rerun passed with sampled aggregate peak RSS 305800 kB
(sum of process RSS, including shared pages), cgroup charged-memory peak
116174848 bytes, host MemAvailable 17557116 kB before and 17549608 kB after.
This is **RUNTIME_GATE_PASS for setup**, not an assignment completion gate.
Full commands, selected container inspection and raw logs are retained under
`/workspace/va1-evidence/docker-recovery`; prior setup failures remain retained.

## Source audit started

`Calculus/Decision.lean` already separates non-hash `Covered` completeness from
`hashCovered` completeness. The bridge must account for both routes:
`decideGoal_complete` requires no hash; `decideGoal_complete_hash` handles hashes.
The integrated handoffs describe closed original pins for two-anchor KeY int,
ledger quantifiers, negative memory block, parameter/struct witnesses and
written-memory hashing. These must be reused, not reimplemented. Runtime
reproduction of those pins remains pending.

## Queue accounting

- Baseline: approvals recorded; source audit and baseline timings incomplete.
- AU01 theorem: meaningful reasoned decidable Residue, target bridge,
  nonvacuity/negative controls and theorem axiom audit pending.
- AU01 performance: checked hash/main-file splits are recorded below; overall
  performance milestone and final import-closure gates remain open.
- AU02: fixed arrays, arrays below keys/fields, arrays of structs/arrays, broader
  memory blocks, halting OR operand, program-free coverage inclusion and
  formula-derived fuel/511-node bound all pending reproduction and proofs.
- Backfill: residue census/bridge controls, profiling/splits, independent fixed-array
  and program-free coverage lemmas, negative/axiom controls all outstanding.
- Per-file, affected/full run-lean, strict automatic, trust/axiom and docs-versus-base
  gates pending. No timeout or failed check counted as a pass.
- No AU05/AU06 or compiler work; no changed exclusions, hash premises or budgets.

## Reviews and delivery

Approval setup: independent finder and skeptic found no issues. Docker recovery:
independent read-only finder and skeptic verified actual limits, exit codes and
formatting without Lean/server. Skeptic noted missing build peak RSS; the
measurement rerun above supplies a sampled aggregate peak, distinct from charged memory.
Implementation milestone reviews remain pending. No push, merge, PR or tag.
The persistent goal was not changed during recovery; get_goal is unavailable
to this worker. Coordinator owns journaled status-only reactivation.

## VA1-Q1: false reverse-inclusion obligation

The standalone [kernel counterexample](after-roadmap-va1/coverage-counterexample.lean)
is `∀ uint x; (1 + 1) * x = x + x`, containing only a value quantifier and
an equation, hence no program or update. Its two kernel certificates prove
`inTarget {} = false` and `Covered = true`. Both use `decide +kernel`; axiom
sets are `[propext]` and `[propext, Classical.choice, Quot.sound]`.
Bounded per-file MCP returned complete diagnostics with success=true, no errors
or dependency failures. Existing MCP dependency cleanup warnings are retained.

`Tm.litValue?` recognizes direct literals only: source `(1+1)` and `x` are
both nonliteral for multiplication admission. Preparation folds `(1+1)` before
coverage checking. Thus the assigned unconditional program-free inclusion
`Covered ⊆ inTarget` is false with the required unchanged predicates. This
does not refute AU01's forward target-to-coverage obligation or soundness.
No target, waiver, hash/validity premise or budget was changed.

The cold Decision closure passed (259 jobs; Decision itself 31s). The
notation import passed (72 jobs). The initial ternary probe had unsupported
notation; the unused-update candidate was not Covered. Those failures are
retained, not counted as counterexamples. Only the folded-factor witness
above is certified.

Independent read-only finder and skeptic both confirmed the witness, its
program-free syntax, exact kernel certificates and impossibility of the
unconditional inclusion; neither used Lean/server/build or wrote files.

**VA1-Q1** (sources: AU02 program-free inclusion; frozen Decision definitions;
standalone kernel witness): should the false reverse-inclusion requirement be
replaced by the certified boundary/counterexample while preserving both
predicates and completing the other assigned obligations, or retained
unchanged (which keeps the full lane blocked)? No option is recommended.
This is a scope correction, not approval to change a semantic premise.

All remaining queue entries above remain open. This evidence checkpoint
is not an AU01/AU02 implementation milestone or final gate pass.

## Independent AU01 hash performance work (2026-11-01)

VA1-Q1 is still pending. The false reverse inclusion, frozen predicates,
committed witness and original requirements are unchanged. Other work does not
depend on that decision. VA2 sharing/notation ownership was not touched.

The original hash file failed before profiling due to stale Constructibility
artifacts; the affected Hashing import closure rebuilt successfully (230 jobs,
401.48 s total; its final module 117 s). No source repair was made there.
Trace profiling polluted guard messages; dedicated profiling and an ordinary
full-file check hit the 12 GiB host-reserve guard. All failures are retained.
The first six original verdicts in an IO timing harness took 0.8764 s combined.
Flushed command markers then located compilation/inlining and kernel coverage
reductions. Scheduling alone was not established as a complete repair.

`DecisionHashes` remains a facade; all public fixture names, definition bodies,
theorem conclusions and 15 original guarded evaluations/expected messages are
preserved. `noinline` changes only its verdict observer's compilation. New
files use the existing serial-elaboration convention. Splitting may add import
overhead; speed history and exact replays were reviewed before changes.

The five-string family is checked per kind and composed; `famBound = 4`,
algorithms, budgets and the original five-string inputs are unchanged. Coverage
proofs select actual existing hash routes. Function-level projection equalities
and structural list membership avoid an observed recursion-depth failure
without increasing that limit. The mixed-kind coverage proof reuses its
original `coveredK2` certificate. All nine printed axiom sets are standard.

| Module | Per-file MCP seconds | Affected build seconds | Sampled peak RSS kB | Minimum available host GiB |
|---|---:|---:|---:|---:|
| DecisionHashCore | 45.91 | 41.46 | 5355456 | 12.63 |
| DecisionHashUpdates | 27.63 | 24.37 | 5370996 | 12.76 |
| DecisionHashFamilyCheck | 29.80 | 28.77 | 4214224 | 13.15 |
| DecisionHashFamilies | 44.59 | 42.50 | 5628552 | 12.51 |
| DecisionHashQuantifiers | 15.95 | 14.88 | 3368952 | 14.68 |
| DecisionHashThreeKinds | 30.94 | 29.70 | 5993368 | 12.12 |
| DecisionHashMixed | 28.77 | 27.61 | 5721100 | 12.40 |
| DecisionHashKeys | 54.88 | 50.98 | 5446052 | 12.04 |
| DecisionHashKinds | 3.18 | 2.07 | 1077032 | 16.28 |
| DecisionHashes | 3.15 | 2.07 | 1220464 | 16.16 |

These are fresh file checks with warm dependency artifacts, not a clean full
build. Each run verifies cgroup `memory.max=12884901888`, `memory.swap.max=0`,
uses one Lean thread and explicit `-j1`, holds the original writer lock and
monitors aggregate RSS and the 12 GiB available-host reserve. No LSP/build
overlap. Logs, exact commands, source hashes and measured samples are under
`/workspace/va1-evidence/independent-20261101`. Stopped checks remain failures.
Scratch probes were preserved outside the library tree for the orphan gate.

Core/updates/family/quantifier/three-kind/mixed/key modules and both facades
have complete passing MCP results and builds below 300 s. This verifies the
hash-file subtask only. Downstream consumer/full gates and the entire AU01
performance checkpoint remain open; no milestone or full assignment pass is
claimed. The published memory-loop prerequisite was not needed or consumed;
no other VM's performance is credited as this VM's result.

Remaining independent work: Decision/DecisionArrays profiling and splits; the
meaningful decidable Residue, forward target/coverage/hash bridge and nonvacuity
controls; all AU02 array/memory/halting-OR/formula-fuel children; independent
array/coverage backfill and final validation. Only the false unconditional
reverse-inclusion obligation is held specifically for VA1-Q1.

### Static and preservation checks for this partial checkpoint

- Registration: 1041 reachable, zero orphaned. Layer gate: 180 core modules,
  zero elaborator reachability. Strict automatic gate: 491 automatic, 61
  step-budget proofs, 11 refuted, zero manual/pending. Trust: 1056 sources,
  248 inventoried sites, zero findings. All four commands exited 0.
- Source comparison against `8bbd5606`: all 82 original declarations, all
  definition bodies, all theorem signatures and all 15 guarded observations
  are preserved. Only the three documented coverage-proof bodies changed.
- The nine printed axiom sets passed the automatic standard-axiom audit.
  Full `check-axiom-pins.mjs` still exits 1: 404 unrecorded changes, zero
  axiom errors, versus 403 at the frozen base. Tracked pins/sets are identical.
  The extra untracked pin is `foo []` in the pre-existing optional
  `Bridge/.lake/packages/mathlib/MathlibTest/SplitIfs.lean` cache. The cache
  and inventory were preserved. This full gate is not reported as passing.
- Strict documentation paths still exit 1 with 48 missing references and 37
  ambiguous references, exactly the frozen-base findings after qualifying
  this lane's ambiguous `Calculus/Decision.lean` citation. Differential result:
  zero new findings. No unrelated references were rewritten.
- KeySort passed again under the current container cap and 12 GiB host
  reserve in 2.08 s, with actual Lean/Lake versions and `KEYSORT_PASS` retained.

The baseline comparison uses the clean detached read-only worktree
`/workspace/va1-doc-base-8bd8742a` at the exact frozen commit. Raw failed
validation-driver attempts remain retained alongside the corrected comparisons.
Downstream consumer/full builds, final strict inventories and the remaining
original queues are still open; this is checked owned progress, not completion.

### Downstream consumer and final review

The unchanged direct consumer `Solidity.Examples.Decision` was checked with
`timeout 300 lake -f .va1-lakefile.toml build Solidity.Examples.Decision`.
It exited 124 after 300.68 s, without a host-reserve stop. This is a failed
required affected check, not a pass. Main Decision profiling/splitting remains
the next independent AU01 child; Hash/DecisionArrays/full-milestone completion
is not claimed.

Independent final read-only finder and skeptic reviews found no code or
documentation issues in the checked hash split. They confirmed source/hash
identity, the 82 original declarations and 15 guards, standard axiom sets,
actual typed route membership and narrow acyclic registrations. They used no
Lean server or build and wrote no files. The final consumer timeout is retained
as an explicit open obligation.

## Independent main Decision performance checkpoint (2026-11-01)

Parent `90572ad37459f12dc560e9f3b8fd646263da2d3f`; frozen base and prior
approval/counterexample/sealed deliveries are preserved. VA1-Q1 remains pending.
This checkpoint completes the main-file split subtask, not AU01/AU02 or the
whole performance milestone. No other producer's source was changed.

The unchanged main consumer timed out after 300.68 s. A marked copy of the
exact frozen-base source also timed out (124, 301.64 s, no resource stop):
markers measured about 50.54 s for the original lines 309–371 coverage block,
112.71 s for ledger-payment controls and 66.13 s for the next APF controls.
Those are section wall times including elaboration/compiled guards, not a
clean arithmetic-search benchmark. Speed history `0cd7a473` and `12240168`
was inspected; the existing exact sorted/array replay certificates remain.

`Examples/Decision.lean` is now a compatibility facade over 13 serial sections.
Every original public name, definition, theorem statement and all 56 guarded
commands/expected messages remain. The only original proof body changed is
`gapThreeKinds_covered`: exact `tk3`/`swPrefix` outputs are certified as `some`,
and the eight unchanged `coveredK3` conjuncts are checked separately before
selecting the existing RIPEMD-first `HashTry` list entry. Private `getD .tt`
values have explicit `*_some` certificates, so their fallbacks cannot establish
coverage on failure. No predicate, hash/validity premise, decision default,
expected observation, algorithm budget or heartbeat/recursion limit changed.

The first split mistakenly reused the existing `Examples/DecisionKInt.lean`
filename. Independent finder and skeptic caught it before dependent checks;
the original file was restored byte-identical and the new section renamed
`DecisionGapKInt`. All new destination paths were checked against HEAD.
The restored original consumer now builds successfully.

### Actual bounded gates

All checks use the original writer lock, one Lean thread, explicit `-j1`,
`--tstack=131072`, the existing task container hard 12 GiB/no-swap bound and
12 GiB available-host reserve; no LSP/build overlap. Per-file MCP results are
complete, with no warnings/errors/dependency failures. Commands are
`timeout 300 .venv/bin/python …/diagnostic.py Solidity/Examples/<module>.lean`
and `timeout 300 lake -f .va1-lakefile.toml build Solidity.Examples.<module>`,
inside the recorded runner. Each raw JSON retains the exact Docker/command
argv, versions, source SHAs, elapsed time, actual exit and resource samples.

| Module | Fresh-file MCP seconds | Subsequent module build seconds |
|---|---:|---:|
| `DecisionCore` | 5.33 | 4.25 |
| `DecisionArithmetic` | 88.32 | 87.14 |
| `DecisionMapping` | 26.60 | 24.33 |
| `DecisionGapCore` | 6.34 | 5.29 |
| `DecisionGapKInt` | 7.42 | 6.34 |
| `DecisionLedger` | 109.00 | 108.44 |
| `DecisionAPF` | 61.76 | 61.58 |
| `DecisionBlocks` | 13.95 | 12.77 |
| `DecisionRefutations` | 10.88 | 8.55 |
| `DecisionOperators` | 105.92 | 103.17 |
| `DecisionThreeKindCoverage` | 28.73 | 27.62 |
| `DecisionGapHashes` | 50.27 | 45.67 |
| `DecisionStorageArrays` | 47.77 | 46.74 |
| `Decision` | 3.16 | 2.10 |

These are dependency-warm fresh-file checks, not a clean full build. The warm
same-source facade rebuild passed in 1.01 s. Actual versions remain Lean
4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`) and Lake 5.0.0-src+797c613.
Across the selected passing module runs, peak sampled aggregate RSS was
5,665,384 kB (sum of process RSS including shared pages); minimum sampled host
available memory was 12.0115 GiB. Each run verified `memory.max=12884901888`
and `memory.swap.max=0` before Lean. The previously passing bounded KeySort
output remains retained; no new runtime pass is inferred from installation.

The original `Examples/DecisionArrays.lean` consumer passed complete MCP in
38.23 s and build in 36.11 s. Its existing 280-line coherent certificate and
`@[csimp]` exact replay were reused without source edits; these timings do not
benchmark or rerun its potentially enormous original arithmetic search.
The unchanged `Examples/DecisionKInt.lean` consumer built in 23.33 s.
A single bounded `lake env lean -j1 --tstack=131072 …/axioms.lean` audit passed
in 116.72 s: all 141 moved public theorem names were checked, and every axiom
set is a subset of `[propext, Classical.choice, Quot.sound]`.

### Retained failed experiments and review

The original and marked main-file 300 s timeouts remain failures. Hash-gap
checks and isolated route attempts stopped on the host reserve (actual Docker
143, wrapper 75); none is counted as a pass. Conjunction unfolding hit the
unchanged recursion limit, and a composition initially left a literal true
conjunction unsolved; the corrected proof uses explicit `Bool.true_and`.
Lean's temporary recovery `sorryAx` in that failed probe is retained, and is
absent from the final 141-theorem audit. The marked hash copy located the
later whole-module stop after the first certificate, at the mixed-kind proof;
a separate certificate module resolves the retained-heap accumulation.
A two-instance partition also stopped; the verified shared-instance proof
was retained. An initial native route timer did not force the value before
the stop timestamp; its timings were discarded. Correct forced timing gives
0.080–0.145 s per compiled route, all true; this is external profiling, not a
kernel certificate. Two extracted family-word numeral candidates were not
incorporated. A probe outside the Lean project returned a tool path error
(despite process exit 0); it was not a passing diagnostic. All raw failures
and owned probe sources are preserved outside the library tree.

Independent read-only finder and skeptic reviews confirmed the repaired
filename, exact original source/guard preservation, unreachable certified
fallbacks, all eight unchanged conditions, existing route membership and
absence of semantic/budget changes. Neither used Lean/server/build or wrote
files. Final documentation/source review is recorded in the evidence directory.

Evidence: `/workspace/va1-evidence/decision-next`, with actual runner logs under
`/workspace/va1-evidence/independent-20261101/va1-ind-main-*`. The source audit
binds every passing target to its final SHA; the original main file is verified
byte-identical to the frozen base. Scratch probes were preserved outside the
library before final static gates. Delivery staging after this checkpoint commit is
`/workspace/va1-evidence/decision-next/delivery`; packaging and checksum
verification must complete before the final report claims those artifacts.

### Remaining obligations after this checkpoint

AU01's meaningful decidable Residue/reason census, nonvacuity controls and
forward target-to-coverage/hash bridge are still open and independent of Q1.
The overall performance milestone, broader Decision consumers and final full
affected import closure/run-lean gates are not complete. AU02 fixed/nested
arrays, broader memory, halting OR, formula-derived fuel/511-node bound and
all corresponding positive/refuted/unknown controls/proofs remain open or
unreproduced. Backfill independent array/coverage lemmas and residue census
remain open. Only the false unconditional program-free reverse inclusion is
held for VA1-Q1. Neither frozen predicate nor that original requirement was
changed. No milestone eligibility, publication, full goal completion or other
VM's workload pass is claimed. The persistent goal was not reset or stopped.

Final static checks for the main split: registration/layer/strict automatic/trust
commands passed (1054 reachable, zero orphans; 180 core modules, zero elaborator
reachability; 491 automatic, 61 step-budget, 11 refuted, zero manual/pending;
1069 sources, 248 inventoried sites, zero trust findings). Axiom inventory still
exits 1 with 1206 pins, zero errors and 404 unrecorded changes, byte-identical
to the previous checkpoint output. Strict doc paths still exit 1 with the
exact frozen-base 85 findings (48 missing, 37 ambiguous), zero added/removed.
Neither failed full gate is reported as passing. The final finder and skeptic
found only premature artifact-sealing wording; it was corrected to pending
packaging before commit. Actual packaging verification belongs to the external
identity/manifest after commit.

## Frozen-source baseline and kernel gap census checkpoint

Parent `2d70adc0ea5d4b6dbd87c86569a6d4ec2b02b123`; full goal remains
incomplete. The human answered VA1-Q1 during this checkpoint, as recorded in
`docs/solidity-scope.md`: **"Authorize the certified boundary revision"**.
This supersedes only the false unconditional reverse inclusion. Earlier
pending-Q1 statements describe their historical checkpoints; the original
requirement and `8bbd5606` counterexample remain, and earlier seals are untouched.
The supported boundary is not formulated or proved by this census checkpoint.

### Reproduced integrated deliveries, reused without source changes

The following files were checked byte-for-byte against the frozen base
`8bd8742ad987d566f7ba7624372cec1c020be07c`, then passed complete bounded per-file
MCP and affected builds on this VM (same runner, actual cgroup cap/no swap,
threads1/-j1, writer lock and 12 GiB host reserve, no build/LSP overlap).

| Frozen module | MCP seconds | Build seconds |
|---|---:|---:|
| `Examples/DecisionMemory.lean` | 65.67 | 65.98 |
| `Examples/DecisionQuantLedger.lean` | 14.90 | 15.11 |
| `Examples/DecisionWrittenMemory.lean` | 20.50 | 14.83 |

The unchanged KeY-int consumer already passed its affected build in 23.33 s.
The six historical unknown pins are reused: two-anchor int and ledger
quantifiers now proved; negative array memory, the given-heap parameter,
fresh struct and written-memory hash now refuted. Exact public certificate
pointers include `gapKIntTwoAnchors_goal_verdict`,
`DecisionQuantLedger.original_goal_proved`, `gapMemParam_verdict`,
`gapMemStruct_countermodel`, and `DecisionWrittenMemory.original_kernel_verdict`
with `original_realized_covered`. The original negative-array verdict guard
also passes; no new exact-verdict theorem is claimed for that native guard.
All existing controls, states, hash premises, definitions and expected outputs
are retained. These Lean guards/native evaluations do not assert external
EVM/compiler agreement. Kernel certificates and native guard evidence are
separate, as recorded by their original sources.

### Actual remaining target gaps, without a Residue shortcut

New `Examples/DecisionGapCensus.lean` imports and reuses the original fixtures.
For each row it kernel-proves `inTarget {} = true`, `decideGoal = unknown`,
and `Covered = false`:

| Existing fixture | Syntactic reason |
|---|---|
| `memParamSame` | Given-heap memory parameter; the finite witness fallback returns countermodels, not global validity from one checked heap. |
| `memStructReversed` | Field/literal equality with the field on the right, outside the exact classifier's orientation. |
| `memStructBuried` | RHS literal below addition, outside the direct-literal schema. |

The hidden-parameter fixture already has the producer's global
`memParamSame_valid` proof and positive local check, while its global verdict
remains unknown. The positive `memStructSame` target pin pairs with existing
coverage/validity certificates; the realized struct countermodel and full
child observations are retained. Thus these are actual inhabited controls,
not a renamed coverage/unknown complement. No `Residue`, bridge or completed
decision theorem is defined or claimed by this module, and the census is not
exhaustive. No other producer's source or old observation was edited.

The ten new facts passed complete MCP in 3.15 s and module build in 2.08 s.
A separate public-name axiom audit passed in 9.55 s: exact ten-name coverage,
only subsets of `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
Actual source SHAs, raw commands/results and baseline identities are saved in
`/workspace/va1-evidence/baseline-next`, with runner logs
`/workspace/va1-evidence/independent-20261101/va1-ind-baseline-*` and
`va1-ind-census-*`. Independent read-only finder and skeptic source reviews
found no issues; neither used Lean/server/build or wrote files. Final docs and
static checkpoint gates are recorded with this checkpoint's delivery.

### Current requirement and remaining queue

VA1-Q1 is answered, not pending. After finishing this safe census checkpoint,
VA1 must formulate and prove the human-authorized precise program-free
boundary, preserve both predicate definitions byte-for-byte and retain the
counterexample, with explicit supported/outside classes and inhabited
positive/negative controls. This is not permission to restate the old false
claim with an unexplained stronger precondition. The exact human receipt and
scope are in `docs/solidity-scope.md` alongside the original obligation.

AU01's meaningful decidable Residue, structural target/coverage/hash bridge,
DecisionTheorem-prime and exhaustive reason census remain open. AU02 array,
memory, halting-OR and formula-derived fuel children and remaining backfill
are still open. Full affected closure/run-lean and strict inventory resolution
remain incomplete. No full-goal completion, milestone eligibility, push,
merge, PR or tag is authorized or claimed. Original VM/thread/branch/goal,
frozen base, checkpoint/seal ancestry and all original unrelated obligations
are preserved.

Census final checkpoint static results: registration 1055 reachable/zero
orphans, layers 180 core/zero elaborator paths, strict automatic 491 automatic/
61 step-budget/11 refuted/zero manual or pending, trust 1070 sources/248
inventoried sites/zero findings; all four passed. Axiom inventory still exits 1
with zero errors and 404 unrecorded changes (output identical to the prior
checkpoint); doc paths still exit 1 with the exact 85 frozen-base findings.
Independent final read-only finder and skeptic found no source, receipt or
documentation issues. They independently confirmed the frozen producer and
predicate file identities. Packaging follows commit; no artifact seal is
claimed until its actual bundle/patch/checksum verification succeeds.
