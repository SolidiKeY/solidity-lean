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
written-memory hashing. These are reused, not reimplemented. The checked
producer-source replays and remaining gap census are recorded below.

## Queue accounting (current)

- Baseline/setup: exact approvals, frozen ancestry, runtime/KeySort, integrated
  producer replays, memory/array gap census and measured checks recorded.
  Exhaustive remaining shape/reason census and baseline reproduction are partial.
- AU01 theorem: meaningful decidable Residue, exhaustive target-to-covered/hash
  bridge and DecisionTheorem-prime remain open. Existing census/nonvacuity and
  countermodel controls and the constructive uint source-grammar bridge below
  are partial progress, not a theorem substitute.
- AU01 performance: hash/main splits and unchanged DecisionArrays replay checks
  pass below 300 s. Array split and replay interpretation profiles are now checked below;
  broader performance/full gates remain open; no milestone eligibility claimed.
- AU02 fixed arrays: seven concrete array shapes reproduced; standalone fixed
  storage-vector reconstruction/negative-block lemmas and controls checked.
  Pipeline integration, fixed/nested array gap closure remain open.
- AU02 broader memory and halting OR: integrated narrower deliveries reused;
  remaining generalized implementation/proofs and controls open.
- AU02 program-free boundary: original false requirement/counterexample retained;
  direct human Q1 revision recorded. Exact coefficient-family boundary checked;
  broader M4 source characterization remains open.
- AU02 formula-derived fuel/511-node bound: open; no fixed budget raised/hidden.
- Backfill: checked splits, independent fixed-vector lemmas, coefficient-family
  boundary, negative/axiom controls delivered; Residue reason census/bridge and
  remaining program-free/coverage work are partial/open.
- Validation: owned per-file/focused gates, strict automatic, layers/orphans and
  trust pass as recorded. Full run fails at host reserve in unchanged frontend
  TypeExamples; ownership Q2 pending. Axiom inventory/docs strict failures remain
  exact-base findings; they are not waived or claimed passing.
- No AU05/AU06/compiler/VA2 work, changed exclusions/premises/budgets or
  publication. Original full persistent goal remains incomplete and unmodified.

## Reviews and delivery

Approval setup: independent finder and skeptic found no issues. Docker recovery:
independent read-only finder and skeptic verified actual limits, exit codes and
formatting without Lean/server. Skeptic noted missing build peak RSS; the
measurement rerun above supplies a sampled aggregate peak, distinct from charged memory.
Completed checkpoint reviews are recorded below; unimplemented milestones still
require their own reviews. No push, merge, PR or tag.
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

## Human-authorized supported coefficient-family boundary

Parent `d17f161d075cf74ff04ecc958eeed8a1bcc02a4a`. The exact human Q1 answer
is recorded with the original requirement in `docs/solidity-scope.md`:
**"Authorize the certified boundary revision"**. This checkpoint proves a
sharp boundary for the explicit family below. It does **not** prove general
program-free reverse inclusion or the broader M4 source characterization.
Those classes and all other original obligations remain outside this result.

### Exact supported class and public statement

For every contract `C`, waiver setting `w` and locally closed typed uint term
`c : Tm C [] (.val .uint)`, `coefficientLeaf c` is the intrinsic program-free
formula `∀ uint x; c * x = x + x`, with `c` weakened under the binder so it
cannot depend on `x`. Locally closed does not mean state-independent: `c` may
read the state. No coverage, source-admission or successful-verdict assumption
is imposed on `c` in the primary theorem.

The public theorem `Solidity.Decide.CoefficientBoundary.coefficientLeaf_inTarget`
in `Calculus/DecisionCoefficientBoundary.lean` has the explicit signature:

```lean
theorem coefficientLeaf_inTarget {C : Contract} (w : Waivers)
    (c : Tm C [] (.val .uint)) :
    (coefficientLeaf c).inTarget w = c.isLitV
```

Thus, **within this family**, source admission is equivalent to direct source
literal shape. The existing `Tm.isLitV` test checks syntax, not whether
preparation can compute a constant. The proof handles weakening, positive
binder traversal, operator admission, mapping-key agreement and the negative
hash-pair restriction separately. It does not call coverage to establish
admission. `covered_boundary` explicitly restricts this stronger family
identity to covered members; its coverage hypothesis is intentionally unused.
That corollary is not the old false unconditional inclusion with a disguised
premise, and arbitrary coefficients are not claimed covered or decidable.

Other formula shapes, different right-hand sides, additional or negative/hidden
binders and updates/programs are outside the supported family. The larger M4
source characterization and all AU01/AU02 completeness claims stay open.
`hiddenParameter_outside_family` certifies an actual separately checked
program-free target/unknown control outside the family by constructor shape;
its target/unknown/not-Covered certificates remain in the census module.

### Inhabited, independently checked controls

`Examples/DecisionCoefficientBoundary.lean` uses notation for the concrete
formulas and named exact equalities to the family. The actual observed triples
`(inTarget {}, Covered, verdict)` were reproduced before adding the new guard:

| Source coefficient | Triple | Kernel semantic certificate |
|---|---|---|
| `2` | `(true, true, "proved")` | Exact proved verdict, `ValidH`, then ordinary `Valid` using the existing no-hash equivalence. |
| `3` | `(true, true, "refuted")` | An inhabited returned state with exact refuted verdict and `¬ holdsH`; ordinary countermodel follows from the existing no-hash equivalence. |
| `(1+1)` | `(false, true, "proved")` | Exact proved verdict and validity; retains the coverage/source-admission mismatch. |

Coverage and all three target flags are independently kernel checked.
Semantic certificates use exactly `decideGoal_sound`, `decideGoal_refutes`,
`Fml.validH_iff` and `Fml.holdsH_iff`; the no-hash facts are kernel proved for
these controls. No new validity/hash premise, default or source exclusion is
introduced. Existing examples/expected observations, predicates, strategy,
fuel/node/time/test/heartbeat/recursion budgets and unrelated profiles are
unchanged. These are model/kernel and native Lean controls, not an external
EVM/compiler agreement claim.

The original `coverage-counterexample.lean` remains byte-identical to
`8bbd5606e55f6ceadcbe611c2475370466d88ae9`. The public standalone
[retained-source link](after-roadmap-va1/coefficient-boundary-link.lean) embeds
that entire original file verbatim after one import and proves
`retained_family_eq` plus `retained_family_boundary`. Its original false/true
observations and both old certificates replay successfully. No earlier seal
or failure was erased. The entire `Calculus/Decision.lean` file, including both
predicate definitions, remains byte-identical to the frozen base; source hashes
are retained in the evidence directory.

### Actual gates, trust and failures

All commands use the same task-owned local Docker runner, actual 12 GiB
aggregate cgroup cap/no swap, explicit `-j1`, threads1, original writer lock and
12 GiB host reserve, without LSP/build overlap. The evidence runner adds only
source hashing for the new files; resource checks and policies are unchanged.
Actual Lean 4.24.0/Lake 5.0.0-src+797c613 versions are recorded before each run.

| Source | Complete MCP seconds | Build seconds |
|---|---:|---:|
| `Solidity/Calculus/DecisionCoefficientBoundary.lean` | 6.52 | 5.40 |
| `Solidity/Examples/DecisionCoefficientBoundary.lean` | 8.68 | 6.34 |
| `docs/feature-work/after-roadmap-va1/coefficient-boundary-link.lean` | 6.55 | standalone MCP |

The public axiom audit checked all 27 boundary/control theorem names in 20.37 s,
with only subsets of `[propext, Classical.choice, Quot.sound]`. The retained-source
link separately prints the two old and two new public axiom reports. Selected
passing runs peaked at sampled aggregate RSS 2,343,272 kB (including shared
pages) and stayed above 15.5145 GiB host available. These are dependency-warm
fresh-file checks, not a cold full project build.

Raw failed probes remain retained: the first helper lacked explicit
`Option.isSome` reduction; a broad unfolding probe hit the unchanged recursion
limit and looping-simp warnings; a new ordinary-countermodel signature used the
wrong `Fml.holds` namespace, then was corrected to the existing `holds`.
No failed probe is counted as a passing theorem. The completed proofs use
explicit signatures/typed intermediates and `simp only`; no `sorry`, new axiom,
new dependency or native-trust shortcut was introduced. Diagnostic probes were
preserved outside the library before static gates.

Independent read-only finder and skeptic source reviews found no issues in
the sharp family identity, substantive bridges, separate semantic controls or
retained-source link. Both required and confirmed the family/general-M4
limitation and the intentionally redundant covered corollary. Neither used
Lean/server/build or wrote files. Final delta/docs/static reviews and packaging
are recorded with this checkpoint; sealing follows commit and is not claimed
until actual patch/bundle/checksum verification.

Evidence and public reports: `/workspace/va1-evidence/boundary-next`.
The exact-source passing gates are verified against the final file hashes.

### Full assignment remains incomplete

This supported-family result is useful checked progress under the approved
revision, not completion of the broader M4 source boundary. AU01 Residue,
DecisionTheorem-prime, structural target/coverage/hash bridge and exhaustive
reason census are still open. AU02 fixed/nested array, broader memory,
halting-OR and formula-derived fuel/511-node obligations, corresponding controls,
remaining independent backfill and final affected/full gates remain open.
Existing strict axiom/documentation inventory failures are not waived. No
milestone eligibility, publication, push, merge, PR/tag or whole-goal completion
is claimed. The original goal identity/objective was not reset or stopped.

Boundary checkpoint final resource rechecks also explicitly print aggregate RSS,
host MemAvailable and cgroup current/peak **before** Lean/LSP starts. They retain
the same 12 GiB/no-swap cap and 12 GiB host reserve. All five warm rechecks
passed: core MCP/build 6.56/2.23 s, controls MCP/build 9.80/2.08 s, retained link
MCP 6.59 s. Pre-build RSS snapshots were 2960–3288 kB; host MemAvailable was
17,240,320–17,261,308 kB. Raw output retains actual `memory.max=12884901888`,
`memory.swap.max=0`, versions and measurements. This adds observability to the
owned runner; no installed guard policy or resource/proof budget changed.

Final boundary static gates: 1057 reachable/zero orphans; 180 core modules/zero
elaborator paths; strict automatic 491 automatic/61 step-budget/11 refuted/
zero manual or pending; trust 1072 sources/248 inventoried sites/zero findings.
All four pass. Axiom inventory still exits 1 with 1206 pins, zero errors and
404 unrecorded changes, byte-identical to the previous checkpoint output.
Strict doc paths still exit 1 with the exact 85 frozen-base findings and no
added/removed findings. Neither full failed gate is reported as passing.
Independent final read-only finder and skeptic found no source/docs findings,
confirmed the ordinary semantic and outside-family proofs, original byte
identities, source-hash/gate matches, exact class limitation and open queue.
Neither used Lean/server/build or wrote files. Packaging remains post-commit,
with actual verification required before claiming a seal.


## Array reproduction and full-gate checkpoint (2026-11-01)

`Examples/DecisionArrayGaps.lean` distinguishes seven current AU02 shapes:
fixed-array bounded blocks (positive and false), arrays below mapping keys,
fixed arrays below keys, arrays below fields, arrays of structures, and arrays
of arrays. Each has separate kernel proofs of `inTarget {} = true`,
`Covered = false`, and actual `decideGoal = .unknown`. These are new named
reproduction inputs, not edits to existing verdict expectations. Fixed-array
reads already have an existing covered route; the reproduced blocks do not.

Six positive inputs have ordinary `Fml.Valid` proofs by their index-one
instance. The seventh constructs an intrinsic `[0,0,1]` root, proves its exact
storage shape, proves `¬ holds fixedBadState fixedBad`, and hence proves
`¬ Fml.Valid fixedBad`. This separates semantic truth/falsehood from the
current incomplete pipeline. No hash premise is needed for these hash-free
inputs. The observer output is external execution; all 21 classifications,
six validity claims and three negative-state claims are kernel theorems.
This census is not a Residue definition, completeness bridge or AU02 fix.

Exact-source per-file MCP passed in 15.96 s, the affected module build in
13.78 s, and all 30 public axiom reports in 20.12 s. The reports contain only
subsets of `[propext, Classical.choice, Quot.sound]`. Evidence, source hashes,
commands, actual versions, cgroup/pre-build measurements and sampled aggregate
RSS are retained in `/workspace/va1-evidence/array-next`; `verified-gates.json`
checks the final source against all three runs. The runner enforces aggregate
12 GiB/no swap and the 12 GiB host reserve, one Lean check at a time, thread
one and explicit `-j1`. The unchanged 300 s guard and all proof budgets remain.
Earlier failed `rfl`/countermodel probes are retained, not counted as passes.
Scratch probes were preserved outside the library before static gates.

Independent read-only finder and skeptic reviews found no issues in the
seven classifications, six semantic proofs or intrinsic countermodel. Both
confirmed that this is reproduction, not pipeline completion, and neither
used Lean/server/build or wrote files. Final documentation/static review and
post-commit packaging are recorded separately below when complete.

### Actual full validation failure and VA1-Q2

The stock `./run-lean.sh` was attempted at head
`3b07ff8e08be6f7564abf3d9cce6ec330617f97d` through the owned bounded
runner. `.va1-full-lakefile.toml` adds only weak `-j1` options to each existing
library/executable; its normalized configuration is otherwise identical.
No installed wrapper, guard or tracked lakefile was changed.
The full run stopped after 366.51 s when host MemAvailable fell below the
required 12 GiB reserve: actual Docker exit 137, wrapper exit 75, no OOM kill,
maximum observed Lean processes one. Sampled aggregate RSS peaked at
3,973,344 kB; minimum host available was 12,862,623,744 bytes. The active
TypeExamples job was inferred from the newest setup timestamp. A separate
fresh focused `Solidity.Frontend.Checked.TypeExamples` check confirmed that
module independently crosses the reserve: 53.59 s, actual exit 143/wrapper 75,
peak sampled aggregate RSS 4,190,480 kB, minimum host available
12,766,621,696 bytes. Both gates FAILED; neither is a timeout/resource pass.
Raw commands/output/measurements are in `/workspace/va1-evidence/full-next`,
especially `failure-summary.json`. No unchanged stopped build was repeated.

Fetched published master `099bfbe185731c354b12a40f28ccf5d98534c779` remains
a descendant of the frozen base and contains no TypeExamples repair. The
assigned branch was not rebased or reset. TypeExamples is byte-identical to
the frozen base and belongs to the frontend source lane. No other lane file
was edited and no foreign host performance is credited as a local pass.

**VA1-Q2 — pending**, sources: full-validation gate, frontend ownership,
12 GiB host reserve. Should the source lane repair TypeExamples, or may VA1
perform a narrow exact-preservation performance split?

1. Keep source-lane ownership: full validation waits for a published repair;
   independent VA1 proof work continues. Recommended because the launch
   explicitly reserves frontend work to other producers.
2. Authorize VA1 only TypeExamples/split modules/necessary registrations:
   preserve every input, observation and budget, with gates and reviews.

This is an ownership question, not a request to weaken the reserve, theorem
or any exclusion/premise. No answer is inferred. VA1-Q1 is already answered
by the direct human approval recorded above; it is not this blocker. All
remaining original queue and backfill obligations remain incomplete.

Array checkpoint static gates: 1058 reachable/zero orphans, 180 core modules/
zero elaborator paths, strict automatic 491 automatic/61 budget/11 refuted/
zero manual or pending, and trust 1073 sources/248 inventoried sites/zero
findings all pass. A direct trust-script invocation initially failed because
it lacked the required NUL-delimited file list; that raw failure is retained
and the sanctioned `bash scripts/check-trust.sh` passed. Axiom inventory
continues to fail with 1206 pins/zero errors/404 unrecorded changes, identical
to the prior checkpoint. Doc paths continue to fail with the exact 85
frozen-base findings, with zero added/removed. The entire Decision source and
original 8bbd5606 counterexample remain byte-identical. Independent final
finder and skeptic documentation/evidence reviews found no issues; neither
used Lean/server/build or wrote files. All original open obligations and Q2
remain. Export verification follows the commit; no full-goal pass is claimed.


## Fixed storage-vector reconstruction backfill (2026-11-01)

`Calculus/FixedArrayFloor.lean` reuses integrated `MemFloor` index laws and
`ArrayCut.vecOf`; those deliveries are unchanged. For all types `E`, lengths
`n`, vectors `v : SVec E n`, breakpoints `B` containing `(n : Int)` and natural
indices `k`, `fixedFloorVec_slot` proves
`(fixedFloorVec B v).toList[k]? = v.toList[mxFloorIndex B k]?`.
This preserves optional reads even beyond length; the default used during
construction is unreachable below length. `fixedFloorIndex_toNat` certifies
the corresponding uint index; `fixedFloorVec_find` proves actual
`SVal.findM` equality along `.atF i q` for every typed continuation
`q : Path E U`, including nested array/struct elements.

`fixedFloorVec_block_reads` realizes a finite block and exterior reads in one
reconstructed vector. `fixedFloorVec_negative_iff` quantifies over all
`v : SVec E n`, with vector-dependent breakpoint lists retaining length and
every exterior read. The full universally quantified block implication is
equivalent to its finite-instance counterpart. `P : Option (SVal E) → Prop`
sees the optional element, not its index; `Q` sees only retained optional
reads. The forward proof applies its full-block hypothesis to a potentially
different vector, then transfers `Q` back by retained-read equality. No
completion/decision premise is assumed. This vector-level boundary does not
recognize arbitrary intrinsic formulas, establish whole-state/alias
agreement, transfer arbitrary guards or change a closer verdict. It does
not replace AU01 or present a stronger premise as the original theorem.

`Examples/FixedArrayFloor.lean` proves inhabited changed/retained uint reads,
reads at/past length, empty bool and nested-array controls. Omitting the
length breakpoint demonstrably changes definedness and invalidates the read
identity. The Boolean input `[true,false]` fails its full block; its different
reconstruction satisfies it. `bool_finite_boundary` specializes the
quantified iff to that inhabited type. These are kernel proofs, not
source/EVM test evidence or pipeline coverage.

Core per-file MCP passed in 3.15 s and fresh focused build in 2.08 s
(final warm source-record recheck 1.02 s). Controls MCP/build passed in
4.27/2.08 s. All 20 public theorem axiom reports passed in 3.21 s with only
standard axioms. Exact commands, versions, source hashes, cgroup/pre-build
measurements and sampled aggregate RSS are in
`/workspace/va1-evidence/fixed-floor-next/verified-gates.json` and raw logs.
The one-second warm recheck finished before an in-container RSS sample,
recorded as null; its pre-build measurements remain. Other checks retain
aggregate RSS samples. The unchanged 300 s/proof budgets, hard 12 GiB/no-swap
cap, 12 GiB host reserve, serial thread-one/explicit `-j1` checks remain.
Failed empty-vector `rfl` and open-lambda inference/decide probes are retained,
not counted as passes. No predicate, pipeline, old pin, model, dependency or
other-lane source changed.

Independent read-only finder and skeptic found no logical issues, confirming
the exact length/retention premises, index-independent `P`, read-only `Q` and
vector-level scope. The skeptic suggested an inhabited specialization; the
Boolean specialization and changing reconstruction address it. Neither
reviewer edited or used Lean/server/build. Final delta/static review and
packaging follow below when actually checked.

This completes the standalone fixed-array backfill lemma/control increment,
not AU02 implementation. AU01 Residue/DecisionTheorem-prime/structural bridge,
broader M4 boundary, AU02 pipeline children including formula-derived fuel
and final full validation remain incomplete. Q1 is answered; Q2 remains
pending and blocks only frontend repair/full validation. Prior seals and
failures remain.

Fixed-vector final static gates pass: 1060 reachable/zero orphans, 180 core/
zero elaborator paths, strict automatic 491 automatic/61 budget/11 refuted/
zero manual or pending, trust 1075 sources/248 inventoried sites/zero findings.
Axiom inventory still fails with 1206 pins/zero errors/404 unrecorded changes,
byte-identical to the prior checkpoint; doc paths still fail with the exact
85 frozen-base findings and no added/removed findings. Decision and retained
counterexample byte identities pass. Final independent finder/skeptic delta
and handoff reviews found no issues. The cumulative export includes prior
raw evidence and seals, with actual post-commit verification required.

The first commit attempt failed with actual Git exit 128: `No space left
on device`. Root overlay was full (32 GiB); source/evidence survived.
Saved non-secret state/cap/driver evidence for the eleven stopped
`va1-ind-fixed-floor-*` containers, then removed only those task-owned
temporary containers. All bind-mounted files, images/caches and other
containers were preserved; free space recovered to 746 MiB. Exact commands
and before/after `df` are retained in `fixed-floor-next/disk-recovery`.
The failed commit is retained as a setup failure, not a passing gate.


## DecisionArrays split and interpreted replay profile (2026-11-01)

Inspected speed history before the warned refactor, especially `12240168`
(`Check array replay`): the exact normalized `normalized2 := .tt` certificate
and closed `@[csimp]` replay intentionally avoid the expensive original
arithmetic search. Both are preserved. A fresh-file baseline profile of the
unchanged source passed in 38.42 s: tactic execution 15.9 s, kernel type
checking 16.7 s, interpretation 73.8 ms. This is the existing certified
closed regression, not a benchmark of unreplayed generic countermodel search.

`Examples/DecisionArrayCore.lean` now owns the original fixtures and eight
public coverage/answer certificates. `Examples/DecisionArrayReplay.lean` keeps all
private arithmetic templates, reduction proofs, replay certificate and
unchanged guarded `['proved','refuted','proved']` observation together.
`DecisionArrays.lean` is the compatible import facade. All 26 declarations,
their signatures/bodies/budgets and the csimp/guard suffix are preserved;
`source-preservation.json` records exact block comparisons. Only wrappers,
imports and the stale module-doc certificate location changed. No private
identifier is used across modules, no other producer file was edited, and
shared module-map registrations are narrow additions.

Dependency-warm checks with initially fresh module files: Core MCP/build
6.32/5.23 s, Replay MCP/build 40.58/36.14 s, facade MCP/build 4.19/3.13 s,
array-gap consumer MCP/build 15.98/14.81 s. After the review doc correction,
Core/facade MCP rechecks passed in 7.43/42.58 s; the latter also refreshed
its changed import. The final combined facade/consumer closure build passed
in 15.88 s. Final replay profiling passed in 37.18 s: tactic execution
16.8 s, type checking 15.1 s, interpretation 49.8 ms. Each checked file is
below the unchanged 300 s guard; the split adds import overhead, and no
overall speedup or cold full-build time is claimed. These are measured
cache/source identities, not another host's results.

A public/private Lean axiom audit passed in 25.49 s, printing all eight
public certificates and every original private proof, including the exact
csimp theorem, plus generated theorem reports. All use only subsets of
`[propext, Classical.choice, Quot.sound]`. Final source hashes and measured
aggregate RSS/headroom are checked in
`/workspace/va1-evidence/array-split-next/verified-gates.json`; raw stdout,
stderr, profiler categories, commands and actual Lean/Lake versions remain.
The hard aggregate 12 GiB/no-swap cap, 12 GiB host reserve, one thread,
explicit `-j1`, writer lock and no LSP/build overlap remain. New containers
are task-owned ephemeral checks so temporary layers do not refill the disk;
all mounted caches, source and evidence remain. No proof/time/search budget,
decision pipeline, frozen predicate, old expected verdict or premise changed.

Independent read-only finder and skeptic confirmed exact code/replay
preservation and acyclic imports. Finder caught a stale 'certificate below'
reference; skeptic caught the facade's extra EOF blank line. Both were
corrected before final gates. Neither edited or used Lean/server/build.
Final documentation/static review and sealing follow when actually complete.
The original AU01 theorem/Residue/bridge and AU02 integrations remain open;
this finishes the requested array-example split increment, not the full lane.

Array-split final static checks: 1062 reachable/zero orphans, 180 core/zero
elaborator paths, strict automatic 491 automatic/61 budget/11 refuted/zero
manual or pending, trust 1077 sources/248 inventoried sites/zero findings
pass. A new shorthand path reference was corrected; its raw failed output
remains. Final doc paths fail only with the exact 85 frozen findings and
zero added/removed; axiom inventory still fails with the identical 1206 pins/
zero errors/404 unrecorded changes. Neither failure is waived or passing.
`cache-identity.json` records source and retained build-artifact hashes for
the affected import closure; the whole-project cold gate remains failed.
Final independent read-only documentation/evidence reviews found no remaining
issues. Frozen Decision source is byte-identical, as are both predicates.
No whole-goal completion or publication is claimed.


## Fixed storage-root agreement backfill (2026-11-01)

`Calculus/FixedArrayRoot.lean` lifts the checked vector reconstruction to
actual `Storage.set` and `State.withStorage`. For every contract `C`, root
name `a`, intrinsic element type `E`, length `n`, root-type witness
`h : C.rootType a = some (.ref (.fixed E n))`, storage and breakpoints
containing `(n : Int)`, `fixedFloorRoot_find` proves optional path equality
through `.atF i q` for every uint `i` and typed continuation `q : Path E U`.
`fixedFloorValue` uses the intrinsic value view, not an indexed runtime
match. `fixedFloorRoot_word`/`fixedFloorRoot_has` derive actual storage
observations. `fixedFloorIndex_fix` and `fixedFloorRoot_retained` separately
prove unchanged reads when the natural uint index is a retained breakpoint.

`fixedFloorRoot_get_ne` preserves every other typed root without requiring
a length breakpoint; `fixedFloorRoot_other_word`/`_other_has` specialize
this to observations. `fixedFloorState_frame` quantifies over every context
and retains the actual heap typing, heap, environment, ledger, self balance
and transaction. Only the selected storage root is rebuilt. These are
construction/agreement proofs, not arbitrary formula or alias agreement,
APF recognition or pipeline completeness. A future integration still needs
its scoped source/reconstruction relation and index-set proof.

`Examples/FixedArrayRoot.lean` reuses existing Probe/vector fixtures. It
checks changed/retained/halted root reads and a non-default mapping entry
at a different root, plus general retained-path agreement. The original
state satisfies `fixedArr[1] = 9`; the rebuilt state refutes that same
formula. This kernel countercontrol prevents extending the preservation
claim to unretained observations. No existing input or verdict is changed.

Core per-file MCP/build passed in 4.19/3.10 s; controls MCP/build passed in
5.25/3.12 s. All 18 public theorem axiom reports passed in 3.21 s with only
standard axioms. Exact commands, source hashes, versions, cgroup/pre-build
measurements and aggregate RSS/headroom samples are retained in
`/workspace/va1-evidence/fixed-root-next/verified-gates.json` and raw logs.
The unchanged 300 s/proof limits, aggregate 12 GiB/no swap, 12 GiB host
reserve, serial one-thread/explicit `-j1` checks and writer lock remain.

Independent read-only finder and skeptic found no issues in the typed root
update, precise length/retention premises, optional continuation reads,
other-root frame or concrete negative control. Neither edited or used
Lean/server/build. Final docs/static review and sealing follow when checked.
This completes the storage-root agreement backfill stage, not AU02
integration or a Residue shrink. AU01 theorem/Residue/bridge and all
remaining original AU02/full gates stay open. Q1 is answered; Q2 remains
pending for frontend repair ownership only.

Fixed-root final static gates pass: 1064 reachable/zero orphans, 180 core/
zero elaborator paths, strict automatic 491 automatic/61 budget/11 refuted/
zero manual or pending, trust 1079 sources/248 inventoried sites/zero
findings. Axiom inventory still fails with the identical 1206 pins/zero
errors/404 unrecorded changes; doc paths still fail with exactly 85 frozen
findings and zero added/removed. Neither is a pass or waived. Decision and
retained counterexample byte identities pass. Both final independent
read-only documentation/evidence reviews found no issues. Post-commit export
verification follows; original goal/branch/base and all previous seals remain.


## AU01 constructive uint source bridge (2026-11-01)

Independent read-only design reviews identified that the existing gap list
is not exhaustive: admitted updates/local histories, formation/compound
terms, additional binder sorts, nondefault waiver settings, KeY-int shapes,
separate normalization/prefix/lifting/node/OR bounds and independent hash
routes all need accounting. No complement-of-Covered/unknown test or
'outside this first grammar' catch-all was introduced as Residue. The
first constructive source-to-prepared-grammar increment follows those reviews.

`Calculus/DecisionUIntGrammar.lean` defines `Tm.UIntLinear` as an intrinsic
predicate on existing scoped uint terms: local/literal, checked addition/
subtraction, multiplication with one direct literal operand. No new IR,
operator or semantic model is introduced. Every member is admitted by the
frozen term predicate for every waiver setting and hash-position flag.
It is hash-free, contains no mapping keys and satisfies existing Theory/
interpreter agreement. `fold2_preserves_num` handles actual literal
folding, including failures retained as `.err`.

`UIntSourceLocs ρ` states that each typed uint local binding is present and
in the existing numeric source grammar. It is independent of any verdict
or coverage test. Its empty-initialization and actual `pushQ .uint`
preservation proofs supply inhabited environments, rather than assuming
translation succeeds. For every contract/context/source term in this
grammar and every such environment, `uintLinear_toL`/`uintLinear_toLT`
construct an actual output `l` with `t.toL ρ = some l` (respectively `toLT`)
and `l.Src false true .num`.

`Calculus/DecisionUIntFormula.lean` defines the intrinsic quantifier-free
logical source grammar over these equations (`tt`, equality, negation,
conjunction, implication). `qfUIntLinear_toLS` constructs one actual `ψ`
with **both** `φ.toLS true ρ = some ψ` and `φ.toLS false ρ = some ψ`, plus
`ψ.Src false true`. The proof retains exact optional equality where both
checked arithmetic operands may halt. Structural target, mapping-key and
negative-hash checks establish `qfUIntLinear_inTarget` for closed members,
for every waiver setting. Closed members are ground arithmetic; scoped
local-variable results are exercised under a real pushed uint binder.

This is a source-translation/admission bridge increment. It does not yet
prove program/update normalization, quantified-prefix closure, parameter
binding, source-derived resource bounds, `leafOf?` success, generic
`Covered` or target-to-coverage completeness. It is not a Residue definition
or replacement for DecisionTheorem-prime. Reads, state terms, comparisons,
updates and binders remain outside this first grammar, without being
new exclusions from the original assignment or frozen target.

`Examples/DecisionUIntBridge.lean` verifies a pushed local and the actual
translated output, missing-binding failure with a false environment
invariant, nonlinear syntax outside the grammar, and logical combinations
at both polarities. Two **different** checked subtractions (`x-1`, `x-2`)
both halt at zero and their source equation holds; at one only the right
term halts and the equation fails. The exact `LFml.optEq` output is pinned.
The quantified negative leaf has a concrete State.init countermodel and a
certified actual refuted verdict, derived using existing Covered completeness
and that semantic countermodel; this is not an arithmetic-search timing.
Positive controls reuse the existing exact direct-two source/certificate
and kernel-compute the actual proved tag of a closed logical combination.
Decision-result validity/refutation statements retain `Fml.ValidH`/
`Fml.holdsH`; ordinary concrete countermodels are stated separately. The
negative leaf explicitly checks hash-freedom before the no-hash completeness
and ordinary-validity specialization. Existing unknown array/
memory pins, observations and decision functions remain unchanged.

Final exact-source MCP checks passed in 12.78 s (terms), 6.31 s (formulas)
and 5.26 s (controls). Focused builds passed in 12.69/5.20/4.16 s. All
52 public theorem axiom reports passed in 13.74 s with only standard axioms.
Commands, source hashes, actual versions and aggregate RSS/headroom are in
`/workspace/va1-evidence/uint-bridge-next/verified-gates.json` and raw logs.
The same hard 12 GiB/no-swap cap, 12 GiB host reserve, serial thread one/
explicit `-j1`, writer lock and unchanged 300 s/proof budgets remain.
Failed constructor-spelling, tactic-probe, polarity reduction, refutation
case-equality and unavailable verdict-equality-instance attempts are retained,
not counted as passing checks. Scratch was preserved outside the library
before static gates; final source has no unfinished proof or new axiom.

Independent read-only finder and skeptic source/control reviews found no
issues. Both explicitly confirmed that the local-binding invariant is
substantive/noncircular and that normalization, prefix/atom closure, bounds,
coverage and the exhaustive residue/bridge remain open. The added pushed-
local and distinct both-halting controls address the skeptic's requested
nonvacuity cases. Neither reviewer edited or used Lean/server/build. Final
documentation/static review and sealing follow when actually checked.
The full original goal remains incomplete; Q1 is answered and Q2 remains
pending for frontend repair/full validation only.

Uint-bridge final static gates pass: 1067 reachable/zero orphans, 180 core/
zero elaborator paths, strict automatic 491 automatic/61 budget/11 refuted/
zero manual or pending, trust 1082 sources/248 inventoried sites/zero
findings. Axiom inventory still fails with identical 1206 pins/zero errors/
404 unrecorded changes; strict doc paths still fail with exactly 85 frozen
findings and zero added/removed. Neither is waived or passing. Entire
Decision source and original counterexample byte identities pass. Final
independent read-only handoff/evidence reviews found no issues. Cumulative
post-commit patch/bundle/checksum export follows; full goal stays incomplete.


## Positive uint-prefix pipeline checkpoint

`Calculus/DecisionUIntPrefix.lean` connects the constructive arithmetic
source grammar to the existing pipeline for exactly one positive uint
binder over one equation. For every contract C, binder name x, and terms
`a b : Tm C [.val .uint] (.val .uint)` satisfying the intrinsic UIntLinear
grammar, `uintPrefix_sourceReduction` constructs a body ψ with the actual
source reduction projected by `.map (·.leaf)` equal to
`some (LFml.all 0 .uint ψ)` and
`ψ.Src false true`. `uintPrefix_leafOf` proves the actual prepared result is
`some (LFml.all 0 .uint ψ).elim.condSimp.prenex`. It assumes neither coverage
nor translation/verdict success. A generic conditional composition helper
is discharged using the independently proved actual normalizer and reducer
facts for this family. Equal-polarity comparison uses structural reflexivity
of existing typed terms/formulas, with no new comparison or trust shortcut.

The normalizer proof has two formula nodes (one binder, one equation),
independently of term size; it makes no arbitrary-term timing claim. Its
all-primitive signature is normalization only; constructive arithmetic
source reduction is specialized to uint. The Src conclusion describes the
reducer body **before** preparation. This checkpoint does not prove Src
preservation through preparation, parameter closure, inExact, resource bounds,
Covered, broader M4 boundary or the exhaustive Residue/DecisionTheorem-prime.
No complement of this first grammar is designated Residue. Original AU02
pipeline children and formula-derived fuel remain open; vector/root backfill
lemmas are not presented as their completion.

`Examples/DecisionUIntPrefix.lean` pins the exact `.all 0` translation of
actual distinct partial subtractions and the precise prepared output. It
reuses their semantic countermodel and certified refuted verdict, preserves
the missing-local/nonlinear refusals, and supplies both literal-multiplication
directions and an unused binder. The direct-two positive reuses its existing
proved result and ValidH certificate. No expected verdict or semantic/default
observation changed. Both frozen predicates and the original 8bbd5606
counterexample remain byte-identical. Human Q1 remains answered by the exact
recorded approval; Q2 is pending only for frontend repair/full validation.

Final per-file MCP, focused serial builds and public axiom commands/timings,
source hashes, versions and sampled aggregate RSS/headroom are retained in
`/workspace/va1-evidence/uint-prefix-next`. The hard 12 GiB/no-swap cap,
12 GiB host reserve, thread one/explicit -j1, writer lock and original budgets
remain unchanged. Failed dependent-rewrite/map-bind transport probes are
retained as failures. Independent finder and skeptic reviewed the source
statements read-only without Lean/server/build and found no substantive issue;
their requested exact output, partial, multiplication and unused-binder
controls are now present. Final reviews and static results follow below once
actually checked. Whole-goal and milestone eligibility remain incomplete.

Final prefix reviews found no substantive issue; the finder requested precise
`.map (·.leaf)` wording for the certified reducer result and it was applied.
All 21 public theorem axiom reports contain only propext, Classical.choice
and Quot.sound. Final exact-source MCP passed in 5.26 s (core) and 5.20 s
(controls); focused builds in 4.17/3.10 s; axiom audit in 13.78 s. Static
checks pass with 1069 reachable/zero orphans, 180 core/zero elaborator paths,
491 automatic/61 budget/11 refuted/zero manual or pending, and trust
1084 sources/248 inventoried sites/zero findings. Axiom inventory remains
FAIL (1206 pins/zero errors/404 unrecorded), byte-identical to the preceding
gate. Strict doc paths remain FAIL with exactly the same 85 frozen findings
(48 missing/37 ambiguous), zero new findings. Full validation's actual source-
matched resource failures remain failures; no unchanged stopped full build
was repeated. The owned stopped array-check containers were removed only
after saving nonsecret state/bounds/mount metadata to recover disk; all
mounted caches, artifacts, failures and other containers are preserved.
The whole original goal and remaining queue are incomplete.


## Halting-OR APF census checkpoint

`Examples/DecisionHaltingOrGaps.lean` reproduces the actual remaining guard-
floor gap, distinct from already-covered Boolean lowering. Intrinsic FloorProbe
has a uint mapping and uint scalar. Its negative block quantifies uint i,j with
guard `((i <= j && i < value - 1) || i <= i)` and conclusion `balances[i] = 0`.
The block implying `balances[1] = 0`, the zero-index variant and the false
companion implying `balances[1] = 1` each have public kernel target=true,
Covered=false and actual decideGoal=unknown certificates. These new baseline
pins change no previous expected observation or pipeline behavior.

`floorClaim_one_valid` proves the positive claim at every intrinsic state by
the (1,0) instance, which skips the partial subtraction. `floorBad_countermodel`
proves that the inhabited default State satisfies the entire negative block
and falsifies the false companion. Its arbitrary-key mapping read uses the
existing typed total-path/default-storage theorem, not a postulated state or
new premise. The zero-index pin receives no unsupported semantic claim.

The default-state guard returns `some true` at keys (2,1) and `none` at collapsed
keys (1,1); `floorIn 0 [0,1]` actually collapses them. This set is illustrative,
not proved to be the collector's set or a complete reconstruction Setting.
It does not refute GuardP.floors: its definedness premises exclude this shape.
Unknown/noncoverage pins do not identify the sole failing stage. The AU02
instantiation/floor repair and meaningful Residue shrink remain open.

Separate closed/binder Boolean cases retain public kernel proved/refuted
certificates through existing soundness/refutation interfaces, an inhabited
countermodel and ordinary-false versus halt controls. A halted outer-OR left
operand is not recovered by either right literal; optional reflexive equality
retains both-halting equality. The finder rejected Boolean-only probes as
sufficient APF reproduction, and this correction is retained. No arbitrary OR
completeness, new exclusion or weakened premise is claimed.

Final exact-source MCP passes in 23.59 s, focused affected build in 20.25 s,
all 23 public axiom reports in 17.99 s, with only standard axioms or none.
Commands, source hashes, actual versions, hard-cap verification, prebuild and
sampled aggregate RSS/host headroom are in
`/workspace/va1-evidence/halting-or-next/verified-gates.json` and raw logs.
Hard 12 GiB/no-swap, host reserve 12 GiB, thread one/explicit -j1, writer lock
and all original budgets remain unchanged. Failed missing-scratch, operator-
spelling, type-inference, tactic-insertion and path-law attempts are retained.
An evidence parser initially rejected the valid no-axioms report form and
exited 1; corrected aggregation verifies all names/forms without altering the
passing Lean audit. Scratch is preserved outside the library before gates.

Independent final read-only finder and skeptic source reviews found no issues;
neither edited or used Lean/server/build. No compiler, semantics/default,
predicate, pipeline, premise or previous verdict changed. Q1 remains answered;
Q2 remains pending only for frontend repair/full gates. Global Residue/theorem/
bridge, broader revised boundary and AU02 pipeline/fuel work remain open. This
census is not AU02 completion or milestone/full-goal eligibility. Final static
and documentation reviews follow once actually checked.

Final halting-OR static gates pass: 1070 reachable/zero orphans, 180 core/
zero elaborator paths, 491 automatic/61 budget/11 refuted/zero manual or
pending, trust 1085 sources/248 inventoried sites/zero findings. Axiom
inventory remains FAIL with byte-identical 1206 pins/zero errors/404
unrecorded changes. Strict docs remain FAIL with the same 85 frozen findings,
zero added/removed. Entire frozen Decision source and retained counterexample
identities pass. Final independent read-only finder/skeptic documentation/
evidence reviews found no issues. Full validation's earlier actual source-
matched resource failures remain failures; Q2 and all remaining original
obligations stay open. This checked checkpoint is census progress only.


## Numeric leaf-preparation checkpoint

`Calculus/DecisionLeafPreparation.lean` proves closure of the **existing**
intrinsic LTm.Num P E grammar through actual storage-read elimination and
conditional simplification, for every contract, primitive type, parameter
predicate P and environment predicate E. The unchanged predicates survive;
no new IR, term representation, preparation function or budget is introduced.
The seq case explicitly constructs the Boolean definedness guard using two
seqL closures. It does not treat Boolean false as failure. The resulting
numeric evidence supplies the existing Src grammar and has zero conditionals.

`uintLinear_toL_numeric` constructs actual numeric translation from intrinsic
UIntLinear syntax and numeric local bindings; it is not inferred from the
broader Src grammar, which admits additional cut operators. The real initial
uint prefix discharges the binding premise. For every typed source term in
that grammar under one uint binder, `uintLinear_prefix_prepared_numeric`
constructs an actual toLT output l whose eliminated/simplified term remains
Num with parameter predicate `q = (.uint,0)` and false environment predicate.
This means **only the permitted atom**, not that every term mentions it:
literal-only terms may mention no parameter. No coverage/verdict success is
assumed in this family theorem.

The controls prove that a false-but-returning Boolean seq guard returns seven,
a failed guard still halts before/after preparation, nested numeric sequencing
preserves the same restrictions, and optional equality holds for two halted
operands while strict leaf equality rejects them. Timestamp input retains its
specific allowed-environment predicate; msgValue is rejected under that
predicate. An orElse term remains outside Num. The actual source decrement
reuses the constructive preparation theorem. A kernel node-growth witness
explicitly prevents interpreting grammar closure as size preservation.

These are term-level closure/source-transport proofs. Formula/prefix closure,
prepared parameter enumeration/bounds, full revised M4 boundary, Residue,
DecisionTheorem-prime and exhaustive target-to-coverage/hash bridge remain
open. This does not close AU02 pipeline children or formula-derived fuel.
Both frozen predicates, old counterexample, old verdicts and proof budgets
remain unchanged. Q1 remains answered; Q2 holds frontend repair/full gates
only. The original full goal remains incomplete.

Final exact-source per-file MCP passes in 4.23 s (core) and 4.21 s (controls),
focused builds in 3.09/3.16 s, all 28 public axiom reports in 4.15 s with only
standard axioms or none. Full commands, source-hash matches, actual versions,
verified hard cap/prebuild and measured aggregate RSS/host reserve are in
`/workspace/va1-evidence/leaf-preparation-next/verified-gates.json` and raw logs.
The same 12 GiB/no-swap, 12 GiB host reserve, thread one/explicit -j1 and
writer lock remain. Initial missing explicit Boolean sort and redundant simp
argument diagnostics are retained; final diagnostics have no errors/warnings.
The blank-line goal probe is not counted as a proof. Independent read-only
finder/skeptic source/control reviews found no issues; the skeptic's permitted-
atom wording correction was applied and rechecked. Neither reviewer edited or
used Lean/server/build. Final static/documentation checks follow.

Final numeric-preparation static gates pass: 1072 reachable/zero orphans,
180 core/zero elaborator paths, 491 automatic/61 budget/11 refuted/zero
manual or pending, trust 1087 sources/248 inventoried sites/zero findings.
Axiom inventory remains FAIL with byte-identical 1206 pins/zero errors/404
unrecorded changes. Strict docs remain FAIL with the same 85 frozen findings,
zero new findings. Frozen Decision and original counterexample byte identities
pass. Final independent read-only finder and skeptic documentation/evidence
reviews found no issues. Exact cumulative patch/bundle/checksum sealing follows.
Whole goal and all outstanding queue obligations remain incomplete.


## Actual numeric formula/prefix bridge checkpoint

`Calculus/DecisionNumericFormula.lean` connects numeric preparation to the
actual formula and prefix pipeline. The supported family is precisely one
positive uint binder over `a=b`, with typed scoped a,b in the intrinsic
UIntLinear grammar. The theorem quantifies every contract and binder name.
`uintPrefix_inTarget` proves admission by the **entire unchanged** inTarget
predicate for every Waivers setting; `uintPrefix_hashFree` proves hash-freedom.
Neither changes validity/hash premises for other formulas or the frozen
DecisionTheorem, Waivers, predicates, exclusions or observations.

`uintPrefix_prepared_facts` constructs a body ψ such that the **actual**
leafOf? result is `some (LFml.all 0 .uint ψ)`, ψ is in the existing Src grammar
for either conditional flag (cut operators enabled), its actual enumerated
parameters satisfy `q=(uint,0)`, and its condMax is two. The permitted atom
need not occur: literal-only terms produce no body parameters. This composes
actual numeric toLT/toL outputs, both polarity translations, the checked
comparison/source reducer, the unchanged normalizer and full leaf preparation.
It does not assume coverage, verdict success or translation success in the
family theorem. The conditional helper's actual translation hypotheses are
discharged by the independent source grammar construction.

`uintPrefix_prepared_liftedExact` proves that this actual prepared leaf passes
the existing liftedExact depth/source/parameter check. A dependent recognizer
result is explicitly transported across stripAll's body equality. This is
**not** Covered or a general node/cut bound. condMax measures conditional
lifting weight, not nodes; optional equality repeats operands across several
equations/implications. The unchanged 511-node/cut obligation, formula-derived
fuel, other source classes, broader revised M4 boundary, exhaustive Residue/
DecisionTheorem-prime/target-to-covered-or-hash bridge remain open. No complement
of this first grammar is called Residue. Other original AU02 children remain
open; the APF unsafe-OR unknowns are retained unchanged.

Generic lower-level numeric equation helpers prove source, parameter and
lifting facts for supplied numeric operands. They do not assert arbitrary
operands semantically translate arbitrary source a,b. The actual source-family
construction explicitly closes that gap. Source grammar has no body binders;
the prenex reasoning here is not arbitrary quantified-formula closure.

`Examples/DecisionNumericFormula.lean` exercises the real distinct partial
subtractions, their actual source/fragment result, all-waiver/hash facts,
both-halting semantics and existing certified refutation. A strict literal
prefix has an exact prepared leaf, **empty** parameter list, unused binder,
actual kernel proved tag, ValidH and separate ordinary validity. Nested
sequencing tests the generic lower-level helper explicitly separately, and
an extra atom is rejected by the exact permitted-parameter predicate.

Final exact-source MCP passes in 5.23 s (core), 4.16 s (controls), focused
builds in 4.15/3.21 s, all 27 public axiom reports in 13.79 s with only standard
axioms or none. Source hashes, commands, versions, verified hard cap/prebuild
and measured aggregate RSS/host reserve are retained in
`/workspace/va1-evidence/numeric-formula-next/verified-gates.json` and raw logs.
The same 12 GiB/no-swap, 12 GiB host reserve, thread one/explicit -j1, writer
lock and all budgets remain. Failed singleton/forall simplification, optional
parameter tuple, conditional-weight reduction, dependent strip recognizer and
empty-context length rewrites are retained as failures. No unfinished proof,
new axiom, dependency, evaluator or premise change is introduced.

Independent read-only finder and skeptic final source/control reviews found
no issues, including the actual source connection, unused binder and clear
node-bound limitation. Neither edited or used Lean/server/build. Q1 remains
answered, Q2 pending for frontend repair/full gates only. This is AU01 bridge
progress, not whole-lane completion. Final static/documentation checks follow.

Final numeric-formula static gates pass: 1074 reachable/zero orphans,
180 core/zero elaborator paths, 491 automatic/61 budget/11 refuted/zero
manual or pending, trust 1089 sources/248 inventoried sites/zero findings.
Axiom inventory remains FAIL with byte-identical 1206 pins/zero errors/404
unrecorded changes. Strict docs remain FAIL with the same 85 frozen findings,
zero added/removed. Frozen Decision and original counterexample byte identities
pass. Final independent finder/skeptic documentation/evidence reviews found
no issues; neither edited or used Lean/server/build. Latest-head full build is
pending; prior exact-source resource failures are retained and not relabeled.
Q2 and the remaining original queue remain open. This reviewed proof checkpoint
is not milestone publication eligibility or full-goal completion.


## Sufficient source-derived body-node bound checkpoint

`Calculus/DecisionNumericBounds.lean` uses the existing intrinsic Tm.size,
without changing any representation, evaluator or runtime/proof/node budget.
Literal folding never increases its original binary node. For every actual
UIntLinear term under the real fresh uint prefix, the translated numeric
output is elimination-fixed, conditional-simplification-fixed, and has no
more nodes than its source. The local shape/size hypotheses of the generic
helper are explicitly discharged by that fresh binding; the family theorem
assumes only the intrinsic source grammar. This is narrower than general Num
sequencing, which earlier controls showed can grow under elimination.

`optEq_nodes` counts **seven copies of each operand plus thirteen nodes**.
`uintPrefix_prepared_sourceBound` constructs the actual prepared body ψ with
its source/parameter/lifting facts and
`ψ.nodes <= 7*(a.size+b.size)+13`. The sufficient corollary derives the existing
511 body cap from source sum <=71 (in fact <=510). It is not a necessary
criterion, a new exclusion, a runtime/fuel increase or completion of AU02's
formula-derived fuel obligation. It bounds the stripped body, not the outer
universal node. Literal magnitude is not counted by Tm.size, so no uniform
runtime claim follows. Separate cut identity/bound, lift identity, relevant
resource booleans and generic Covered remain open.

The actual controls expose the following distinct boundaries:

| Source case | Raw size sum | Prepared body | Covered | Actual outcome |
|---|---:|---:|---|---|
| near symbolic limit | 70 | 503 | true | Coverage and direct ordinary validity certified; search not profiled |
| larger symbolic pair | 72 | 517 | false | **proved**, with public kernel tag, ValidH and ordinary validity |
| larger literal source | 82 | 27 | true | proved, with kernel tag and separate validity |
| both literal subtractions fail | 6 | 27 | true | optional equality valid |
| one subtraction fails, other side returns | 4 | 3 | true | concrete State.init countermodel and certified actual refutation |

The 517-node formula also has hashCovered=false and is hash-free. Guarded
execution reports both original dependentReduction? and quantReduction?
return some; decideLeafA takes the first successful route. These route
observations are external guarded executions; the actual global proved tag,
coverage/hash flags, body count and validity have separate public kernel
proofs. Covered is sufficient, not a complete characterization of every
answered input. The initial expectation that an over-cap leaf might be unknown
was rejected by reproduction before any pin: its **proved** outcome is
retained. It is not inferred to lie in Residue. Similarly the larger source
that folds small proves source sum >71 cannot classify a gap or unknown.
No previous expected verdict/observation was changed.

Final exact-source per-file MCP passes in 4.23 s (core) and 28.89 s (controls),
focused builds in 4.12/24.40 s, all 40 public axiom reports in 23.40 s with only
standard axioms or none. Initial classification/route executions pass in
7.45/8.61 s. Full commands, source hashes, versions, hard-cap/prebuild outputs,
measured aggregate RSS and host reserve are in
`/workspace/va1-evidence/numeric-bounds-next/verified-gates.json` and raw logs.
The same 12 GiB/no-swap, 12 GiB host reserve, thread one/explicit -j1, writer
lock and unchanged proof/300 s guards remain. Typed-match reduction,
reflexive-inequality and tactic-layout failures are retained; final diagnostics
have no errors/warnings. No sorry, axiom, dependency or predicate/function
change is introduced.

Independent read-only finder and skeptic final source/control reviews found
no issues. Both emphasized sufficient-not-necessary sizing and preservation of
the uncovered-but-proved control; no unexplained Residue/unknown classification
follows. Neither edited or used Lean/server/build. Q1 remains answered; Q2
pending only for frontend repair/full gates. Full Residue/theorem/bridge,
broader revised M4 and all other open AU02/full-gate obligations remain open.
This checked source bound is not whole-lane completion. Final static/docs
reviews follow once actually checked.

Final source-bound static gates pass: 1076 reachable/zero orphans,
180 core/zero elaborator paths, 491 automatic/61 budget/11 refuted/zero
manual or pending, trust 1091 sources/248 inventoried sites/zero findings.
Axiom inventory remains FAIL with byte-identical 1206 pins/zero errors/404
unrecorded changes. Strict docs remain FAIL with the same 85 frozen findings,
zero added/removed. Frozen Decision and original counterexample byte identities
pass. Final independent finder/skeptic documentation/evidence reviews found
no issues; neither edited or used Lean/server/build. Latest-head full gate
remains pending; earlier source-matched resource failures remain failures.
Q2 and all remaining original obligations stay open. This is a reviewed
source-bound checkpoint, not milestone eligibility or full-goal completion.


### Actual source-to-coverage bridge checkpoint (2026-11-01)

`DecisionNumericCoverage` proves the actual existing parser accepts numeric
terms at either conditional flag and that cutting them introduces no definition
or fresh atom. Strict and optional equality preserve these facts, including the
existing optional equality's nested definedness implications. Actual preparation
also has zero conditionals; existing conditional-lift identities then preserve
the full prefix. These are proofs about the original functions, not added
recognizers, axioms, premises on success, or a second calculus.

`uintPrefix_Covered` has explicit quantifiers over every contract C, binder name,
and a,b : Tm C [.val .uint] (.val .uint), with a.UIntLinear, b.UIntLinear and
**a.size + b.size ≤ 71**. It proves (primitivePrefixEq name a b).Covered=true by
constructing actual leafOf? output, both parser modes, bound parameters, the
original lifting-weight check, body bound and cut bound. The raw size condition
implies the existing 511-node conditions by the previously checked exact copy
count; it is sufficient only. It is not a new limit, exclusion, general fuel
bound, Residue definition or necessity assertion. Larger sources that fold small
and the uncovered-but-proved 517-node example remain outside this theorem's
premise without being classified as unknown.

`uintPrefix_decided` discharges original hasHash=false structurally and invokes
existing completeness. `uintPrefix_certified` proves the actual returned verdict
is proved with **Fml.ValidH**, or refuted with an explicit State C [] and
**¬Fml.holdsH** at that state. No hash or validity premise is weakened. The
existing `uintPrefix_inTarget` theorem supplies target admission for all Waivers;
this checkpoint establishes a constructive target-to-coverage subfamily, not the
exhaustive target/Residue theorem or unconditional reverse inclusion. The Q1
human-controlled revision, both frozen predicates and original counterexample
remain unchanged.

Controls apply the generic theorem to the inhabited symbolic 70-node/503-body
case, strict literal equality with an unused binder, partial subtraction equality,
both failed operands, and a genuinely false failed/returned pair. Actual positive
and refuted certificates and the both-halt/one-halt semantic distinction are
retained. Countercontrols reuse the 72-node/517-body uncovered-but-proved result,
82-node source folding to covered, and an existing admitted memory unknown.
No previous pin or expected observation changes.

Exact-source per-file MCP is clean in 8.45 s (core) and 5.18 s (controls), focused
builds pass in 6.32/3.10 s, and all **30 public axiom reports** pass in 25.48 s
with only propext/Classical.choice/Quot.sound or none. Commands, source hashes,
actual Lean 4.24.0/Lake 5.0.0-src+797c613 output, cgroup memory.max=12884901888,
memory.swap.max=0, prebuild resources and aggregate measurements are retained in
`/workspace/va1-evidence/numeric-coverage-next/verified-gates.json` and raw logs.
Maximum sampled aggregate RSS across these checks is 1971140 KiB; minimum host
available is 16623378432 bytes, above the required 12 GiB reserve. All use the
original writer lock, thread one, explicit Lean -j1 and unchanged 300 s budget;
there is no LSP/build overlap. Intermediate dependent-transport, optional-form
shape and Boolean-interface failures are retained. No proof-budget increase,
sorry, new axiom, dependency, default or predicate change occurs.

Independent read-only finder and skeptic final source/control reviews both found
no issues; neither edited or used Lean/server/build. Static gates pass: 1078
reachable/zero orphans, 180 core/zero elaborator reachability, 491 automatic/61
budget/11 refuted/zero manual or pending, and trust 1093 sources/248 inventoried
sites/zero findings. Axiom inventory remains FAIL1 with byte-identical 1206 pins,
zero errors/404 unrecorded changes. Strict docs remain FAIL1 with the same 85
frozen findings and zero added/removed. The entire original Decision source and
8bbd5606 counterexample pass byte-identity checks. Raw failures are preserved.
Final independent finder and skeptic documentation/evidence reviews found no
discrepancies; exact source hashes match the passing records and all unfinished
obligations/failures remain explicit. Neither edited or used Lean/server/build.

The original full queue remains incomplete: meaningful global Residue and
DecisionTheorem-prime/exhaustive target/hash bridge, broader revised program-free
M4 boundary, full baseline/performance validation, fixed/nested array pipeline
integration, broader memory blocks, actual halting-OR guard-floor repair, general
formula-derived fuel, and affected/full final gates remain open. Existing checked
vector/root reconstruction, source subfamily bridges, module splits and controls
are completed backfill, not substitutes for those children. Q1 is answered; Q2
holds only frontend repair/full validation. Latest-source full ./run-lean.sh is
pending; earlier source-matched resource failures remain failures. No milestone
eligibility, publication or full-goal completion is claimed.


### Parallel interface checkpoint (2026-11-01)

The human authorized concurrent implementation scheduling. The concrete numeric
coverage and fixed-array interfaces are specified in
[parallel-interface.md](after-roadmap-va1/parallel-interface.md), including exact
checked producer head, source hashes, typed signatures, witnessed clients, real
premises and outstanding combined-tree gates. VA2 needs no future VA1 theorem
to consume this package privately. It does not imply full Residue/AU02 closure
or authorize integration/publication. Q2 remains held only for frontend repair.
The immutable incremental Git bundle and committed-source archive will be
exported under /workspace/va1-evidence/parallel-interface-next after review and
commit; no changing checkout is presented as a checked dependency.
