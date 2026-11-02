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


### One-way negative-chain instantiation component (2026-11-01)

`Calculus/DecisionNegativeInstantiation.lean` implements negativeChainInst on
actual intrinsic LFml C formulas. It instantiates only negative quantifier-free
chains of a chosen primitive K, through the original LFml.inst. Positive chains
remain unchanged; traversal stops at unselected binders. Original per-sample
strict definedness guards and substitution are reused. No future producer fact,
array-root recognition or floor reconstruction premise is assumed.

LFml.negativeChainInst_sound is quantified over every contract, primitive K,
typed sample list List (LTm C (.val K)), formula, polarity, State C [] and AEnv.
At positive polarity, satisfaction of the finite instance implies the original;
at negative polarity, the original implies its finite instances. The proof
handles negation/conjunction/implication and uses existing LFml.inst_sound at
the chain. LFml.valid_of_negativeChainInst transports global validity in that
one direction only. Quantifier-free formulas are preserved at both polarities.
The generic negativeChainInst_instance_client proves a chain implies its actual
guarded finite instances for arbitrary typed body contents.

`Examples/DecisionNegativeInstantiation.lean` applies the component to a bounded
read of the actual fixedArr storage root of the existing Probe contract. Its
index-one sample is inhabited at State.init; proof uses holds_subst1, the
index_fixed/empty-prefix path interface, default storage fields and fixed-vector
list laws, preserving the concrete witness. Positive-chain and halted-sample
controls retain the original behavior. A Boolean formula is globally valid
while its one-point finite instance is false: original_valid,
finite_instance_invalid and no_equivalence explicitly refute the converse.
The old fixedBlock global unknown is reused unchanged.

This is an independently implemented one-way proof interface for future
array/memory positive-instance consumers, not exact Prep, refutation transport,
a decision branch, new coverage or a Residue shrink. It does not close the
source fixedBlock pin or the entire AU02 fixed/nested-array child. Exact floor
reconstruction, source/pipeline integration, complete target coverage and other
original obligations remain open. No decision predicate/model/default/pin,
observation, refusal, hash premise or proof/test/resource budget changes.

Exact-source per-file MCP is clean in 5.28/5.26 s, focused builds pass in
4.20/3.11 s and all 14 public axiom reports pass in 5.22 s with only standard
axioms or none. Actual Lean 4.24.0/Lake 5.0.0-src+797c613, hard memory.max
12884901888/swap.max 0, thread one/explicit -j1, prebuild resource checks and
measurements are retained in
/workspace/va1-evidence/negative-inst-next/verified-gates.json and raw logs.
Maximum sampled aggregate RSS is 1362820 KiB; minimum host available is
17103032320 bytes, above 12 GiB. All checks are serial under the original
writer lock, with no LSP/build overlap and unchanged 300 s bounds. Initial
congruence-name and concrete conversion/substitution/path/vector failures are
retained; final diagnostics have zero errors/warnings.

Independent read-only finder and skeptic final source/control reviews found
no issues; neither edited or used Lean/server/build. Static gates pass:
1080 reachable/zero orphans, 180 core/zero elaborator paths, strict automatic
491/61 budget/11 refuted/zero manual or pending, trust 1095 sources/248 sites/
zero findings. Inventory FAIL1 remains byte-identical 1206 pins/zero errors/
404 unrecorded changes. Strict docs FAIL1 retains the same 85 frozen findings,
zero added/removed. Original Decision source and counterexample byte identities
pass. Final finder documentation/evidence review found no issues. Skeptic
found the AU02 paragraph appended under unrelated cancellation tests; it was
moved into the owned M7-next section before commit. No other findings. Neither
reviewer edited or used Lean/server/build.

The PARALLEL-INTERFACE export is already committed at
144a2a9db73067e67e778515ccd932630070fea6 with the checked numeric implementation
at 782dcff93a13fd1a19f0f45e6246146815555ef5. Its immutable 367-file committed
import-closure archive and incremental bundle are under
/workspace/va1-evidence/parallel-interface-next. Bundle SHA256:
c49eddeaeaaa5b01512e0d88d8aa831b6979dfe937f4a592138980e8c96caf62;
source archive SHA256:
50c814969bea1f901c429244d51b97e8f152c3eaecb4d55153a52cd6ae9ce60d.
Bundle verify, source-blob hash verification and SHA256SUMS check pass. An initial
raw-SHA range bundle export refused as empty (exit128); the named assigned ref
plus explicit frozen-base exclusion repaired it, with failure retained. No
history reset, producer substitution or changing-checkout dependency snapshot.
VA2 may consume these actual checked interfaces now; combined-tree final gates
remain open. This proof-only component is later than that immutable export and
is delivered separately at its own checked commit.

All original AU01/AU02 obligations, incomplete baseline/performance/general-fuel
work and pending/failed full gates remain as previously listed. Q1 is answered;
Q2/frontend repair remains held without blocking this independent work. No new
goal, reset, stop/completion, push, merge or tag publication is performed.

## AU02 independent fixed-array path reconstruction — 2026-11-01

`Calculus/DecisionFixedArrayPath.lean` adds `fixedFloorAtPath` on the
existing intrinsic `Path T (.ref (.fixed E n))` and actual optional lookup/save
APIs. `fixedFloorAtPath_exists` discharges save success from actual prefix
presence using the existing save theorem. `fixedFloorAtPath_reconstruction`
quantifies every typed element continuation and every diverging path: with
explicit `(n : Int) ∈ B`, successful indexed reads equal original reads at
`fixedFloorIndex B i`; diverging reads are unchanged. Absent prefixes return
none. No default object is installed. Existence itself needs no length premise.

`Examples/DecisionFixedArrayPath.lean` has inhabited mapping-key and nested
fixed-array clients, an actual changed 9-to-7 interior read, unchanged sibling
key, absent outer index refusal and missing-length definedness countercontrol.
These are kernel value/path facts, not EVM tests or an array pipeline certificate.
Only one selected prefix is reconstructed; simultaneous prefixes, collector,
source grammar, finite-instance equivalence and coverage integration remain open.
No decision source, predicate, observation, refusal, expected verdict or budget
changed. Registrations are exactly two additive imports and two module-map rows.

Raw exact-source commands, outputs, versions and resources are retained in
/workspace/va1-evidence/fixed-path-next. Per-file core MCP 4.316s and controls MCP
4.202s pass with zero errors/warnings/dependency failures. Focused core build
3.096s and controls build 3.098s pass. Fifteen public theorem/control axiom reports
pass in 3.125s, using only propext/Classical.choice/Quot.sound. Every Lean command
runs under the original writer lock, threads1/-j1, hard aggregate 12GiB/no-swap,
verified cgroup values and prebuild OS reserve. Maximum sampled aggregate RSS
1371352 KiB; minimum sampled host available 17150767104 bytes, above the 12GiB reserve.
Initial bind-alias and reserved-identifier MCP failures remain retained.

Static gates: 1082 reachable/zero orphans, 180 core/zero elaborator reachability,
strict automatic 491 automatic/61 budget/11 refuted/zero manual or pending,
trust 1097 sources/248 sites/zero findings. Inventory FAIL1 is byte-identical to
prior checkpoint: 1206 pins, zero errors, 404 unrecorded changes. Strict docs
FAIL1 retains existing missing/ambiguous references; no full-gate pass is claimed.
Original Decision source remains byte-exact to the frozen base. Finder and skeptic
read-only reviews found no confirmed issues; neither edited or ran Lean/server/
builds. Skeptic's suspected existential elaboration issue was resolved by the
actual clean diagnostics and standard-axiom reports.

The immutable PARALLEL-INTERFACE export at 144a2a9d remains available unchanged;
this later component will be exported separately after commit and bundle verification.
AU01 meaningful Residue/global DecisionTheorem-prime and exhaustive target/hash
bridge, broader revised program-free boundary, AU02 pipeline children/general
formula-derived fuel, remaining baseline/performance and final full validation
remain open. Q2 producer-owned TypeExamples repair is still held. Independent
owned work continues; the full original goal remains incomplete.

Final documentation review found the new module-map rows outside their table;
both rows were moved beside the existing Decision modules before commit. No
source/proof findings. Original raw failures and earlier seals are preserved.

## AU01 independent decidable source grammar — 2026-11-01

`Calculus/DecisionUIntShape.lean` implements `Tm.uintLinearShape`, exactly
characterizing the existing intrinsic `Tm.UIntLinear` grammar. Generalized
`UIntLinearAt` is false at other sorts. Literal recognition returns a typed
value plus equality with the original term. `uintBinaryEvidence` consumes
actual optional subderivations; main `uintLinearEvidence` follows structural
recursion. `uintLinearShape_sound`, `uintLinearShape_complete` and
`uintLinearShape_iff` prove both directions, supplying a constructive Decidable
instance without a classical decision oracle. `uintShapePrefix_Covered` and
`uintShapePrefix_certified` feed the actual existing numeric coverage/certificate
bridge with unchanged sufficient `a.size + b.size ≤ 71` and exact `ValidH`/
`holdsH` conclusions. No Covered/verdict/complement test defines the syntax.

The accepted syntax is precisely uint locals, literals, addition/subtraction
and multiplication with a direct literal operand. Other sorts, observations,
environment reads, other operators and nonliteral products are outside this
specific grammar. Rejection alone implies neither unknown nor invalidity nor
absence of coverage/target admission. This is a concrete decidable component
for the unfinished residue census, not the global Residue/DecisionTheorem-prime.

Controls check nested addition/subtraction and both literal-product orders,
reject symbolic products and folded nonliteral coefficients, use the Decidable
instance for positive/negative grammar membership, apply the real coverage and
certified-result bridges, and retain the inhabited partial-arithmetic countermodel.
No source/predicate/default/observation/verdict/pin/budget change is made.
Registrations are two additive imports and two adjacent module-map rows.

Finder caught initial kernel-evaluated indexed matches violating Gate G0.
Warned before repair and inspected intrinsic speed history and existing TermEq
recursors. Replaced indexed dispatch with explicit generalized-index Tm/Op0/Op2
casesOn and structural recursion. Remaining matches concern types/operators or
parameter-only Option witnesses. No compiled twin is introduced. Rejected
source is retained in evidence, together with match/equation-generation, proof,
layout and local probe failures. Finder and independent skeptic re-reviewed the
repair read-only and found no remaining source issue; no Lean/server/build/edits.

Exact repaired-source gates in /workspace/va1-evidence/linear-shape-next:
core MCP 5.261s, core build 3.093s, controls MCP 4.275s, controls build 3.099s,
14 public theorem/control axiom reports 8.475s, all pass. MCP diagnostics have
zero errors/warnings/dependency failures; axioms are only standard
propext/Classical.choice/Quot.sound. Every check uses the original writer lock,
thread1/-j1, hard aggregate12GiB/no-swap with actual cgroup verification and
12GiB host reserve. Maximum sampled aggregate RSS 1528452 KiB; minimum host available
17069674496 bytes. Actual Lean4.24.0/Lake5.0.0-src+797c613 versions are retained.

Static gates pass: 1084 reachable/zero orphans, 180 core/zero elaborator reach,
491 automatic/61 budget/11 refuted/zero manual or pending, trust1099 sources/
248 sites/zero findings. Inventory FAIL1 remains byte-identical to the preceding
checkpoint (1206 pins, zero errors, 404 unrecorded changes); strict docs FAIL1
retains existing missing/ambiguous references. Original Decision source remains
byte-exact to frozen base. These failures and the TypeExamples full-gate failure
remain failures; no unchanged failed heavy gate was repeated as an endpoint.

The earlier fixed-path checkpoint is committed at
4d44b034dddd81a1bfa2acb02478552e7db2d23d and sealed at
/workspace/va1-evidence/fixed-path-next/delivery. Initial sealing rejected a
stale all-source hash from the pre-rename controls; this failure is retained,
focused core check refreshed, then all274 source hashes matched committed blobs.
Patch/bundle/handoff/evidence/checksums verify. The immutable parallel-interface
export at144a2a9d remains unchanged and usable independently.

All original global residue/theorem/hash bridge, broader revised M4 boundary,
AU02 fixed/nested-array pipeline, memory/halting-OR/general-fuel children,
remaining baseline/performance/backfill and final concrete full gates remain
incomplete. Q1 approval is retained; only Q2 frontend ownership repair remains
held. This checkpoint does not claim a residue shrink or lane completion.

Final finder and skeptic documentation reviews found one shared label incorrectly
calling the AU01 recognizer AU02; changed to AU01/AU02 proof components before
commit. No other findings. Both reviews remained read-only without Lean/server.

## AU02 independent numeric logical formula bounds — 2026-11-01

`Calculus/DecisionNumericLogic.lean` extends the numeric preparation component
to quantifier-free logical combinations, using a proof predicate on actual
`LFml` rather than a replacement IR. `LFml.UIntQF` has tt, strict numeric uint
equality, not, and, imp; optional source equality uses the existing expansion.
It retains exact parameter/environment predicates on existing Num evidence.
Structural proofs establish parser acceptance, parameter closure, no cuts,
zero conditionals, conditional weight at most two and preparation preservation.
The tt weight is zero, handled without assuming every body has equality weight.

`Fml.uintQFWeight` uses generalized-index casesOn/structural recursion. Each
source equation contributes `7 * (a.size + b.size) + 13`, counting optional
copies; logical constructors add their subweights and one node. Unsupported
constructors return zero, which is explicitly NOT admission evidence: every
bound theorem independently requires the intrinsic `QFUIntLinear` predicate.
`qfUIntLinear_prefix_sourceBound` proves both actual source-polarity translations,
numeric logical shape, elimination/simplification fixedness and a node bound
from the original scoped source. `qfUIntLinear_formula_bound` derives the
unchanged 511-node exact tests when the original source weight is at most511.
No fuel/node/conditional/proof budget is changed or hidden.

`qfUIntPrefix_inTarget` and `qfUIntPrefix_hashFree` establish the frozen source
boundary for every admitted logical body and waiver setting. The conditional
interface `qfUIntLogic_Covered_of_leaf` still requires the actual `leafOf?`
equation; no assumed future theorem or semantic oracle substitutes for it.
General source-reducer traversal and normalization remain open. This is NOT
the global target bridge, Residue theorem or full formula/fuel completion.

`Examples/DecisionNumericLogic.lean` has nontrivial positive/refuted logical
clients. Their actual leaf equations are kernel proofs. Coverage consumes
nodes derived from the ORIGINAL source: source weights141/197 conservatively
bound actual lowered bodies117/173. Ordinary validity and an inhabited
State.init countermodel are proved. Separate kernel `positive_verdict` and
`negative_verdict` certify .proved and an actual returned refuting State with
not holdsH, using original completeness/soundness/refutations and discharged
hash-freedom. Executable guard observations remain separate native evidence.
A foreign-parameter numeric body is rejected by the unchanged exact admission
check; shape alone cannot waive closed-prefix parameters. No verdict changes.

Raw commands/results/source identities are in
/workspace/va1-evidence/numeric-logic-next. Core MCP 5.254s, focused core build
2.032s, controls MCP 7.396s, focused controls build 6.325s, and46 public axiom reports
11.655s pass. MCP diagnostics contain zero errors/warnings/dependency failures;
axioms are standard propext/Classical.choice/Quot.sound only. Checks hold the
original writer lock, thread1/-j1, hard aggregate12GiB/no-swap with actual
cgroup values verified before Lean and12GiB host reserve. Maximum sampled
aggregate RSS 2043800 KiB; minimum host available 16707321856 bytes. Actual pinned
Lean4.24.0/Lake5.0.0-src+797c613 versions retained. Initial parser-strip,
root-namespace, congruence-name and missing-sort failures are retained.

Independent read-only finder and skeptic source/control reviews found no
confirmed issues, including the added exact kernel verdict certificates.
Neither edited or used Lean/server/build. Static gates pass:1086 reachable/
zero orphans,180 core/zero elaborator reach,491 automatic/61 budget/11 refuted/
zero manual or pending, trust1101 sources/248 sites/zero findings. Inventory
FAIL1 remains byte-identical prior1206 pins/zero errors/404 unrecorded changes;
strict docs FAIL1 retains the same85 frozen findings. Decision source is
byte-exact to frozen base. Full run remains failed/pending as already recorded;
no unchanged resource-stopped heavy gate is repeated as an endpoint.

This separately exportable component needs no VA2 sharing implementation.
General traversal proofs for the concrete existing normalizer/source compiler
are identified next dependencies within the owned proof work; no whole lane
wait, API simulation or foreign source change is assumed. The existing immutable
parallel-interface export remains available; newer committed components are
exported cumulatively at their own heads.

All global AU01 Residue/DecisionTheorem-prime/exhaustive target/hash bridge,
broader revised program-free boundary, AU02 fixed/nested-array pipeline,
remaining memory/halting-OR/general-fuel, baseline/performance/backfill and
required final gates remain incomplete. Q1 is answered; Q2/frontend repair
stays held without blocking independent work. Goal/VM/branch remain unchanged;
no push, merge, PR or tag.

## AU02 actual numeric logical source traversal — 2026-11-01

`Calculus/DecisionNumericTraversal.lean` proves traversal of the existing
public `ExactAt.ofFormula?`, without changing any reducer/normalizer API or
budget. For every intrinsic QFUIntLinear body over the fresh uint context,
`qfUIntLinear_exact_source` takes any fuel at least the original-source
`uintQFWeight` and returns an actual ExactAt certificate, its exact leaf and
both real toLS polarity equations. The proof is induction on the existing
fuel and actual source constructors, not a simulation or assumed oracle.

`qfUIntPrefix_sourceReduction` proves the actual public sourceReduction?
route on the positive prefix at the unchanged2048 budget, assuming explicitly
`φ.uintQFWeight ≤ 2047` and reserving one step for its binder.
`qfUIntPrefix_source_coverageFacts` instead requires `φ.uintQFWeight ≤ 511`
and joins that actual certificate to numeric logical shape, fixed preparation
and the formula-derived511-node body bound.
The general program-normalizer traversal that precedes leafOf? remains open;
no complete source-to-leaf, global Residue/DecisionTheorem-prime or full fuel
completion is claimed. This discharges one previously explicit conditional
integration obligation, independently of VA2 sharing and held frontend work.

`Examples/DecisionNumericTraversal.lean` has actual source certificates for
the nontrivial positive/refuted logical clients and identifies the positive
certificate leaf exactly. Source weight141 supplies a real certificate; fuel3
actually refuses that nested body while fuel4 succeeds. Hence the structural
bound is sufficient, not necessary/minimal and never an unknown classifier.
Zero fuel refusal and the previous exact kernel proved/refuted certificates
are retained. No native guard is presented as a kernel verdict proof.

The normalizer implementation is unchanged and its concrete source identity
recorded in producer-identity.json: ProgramReduction SHA256
46fa4337ca525f3347eadab053c3458385b73a56bb7aef0d06d21e68a3c6f7e2.
An inspection-only probe of its generated private numeric name failed exit1
with identifier/parser errors; the actual public ofFormula? signature printed.
The failure is retained. No private alias, producer replacement, frontend
repair or source/API edit was introduced or assumed. Decision, ProgramReduction
and ExactUpdates remain byte-exact to frozen base. General normalization is
still an owned proof obligation, not a whole-lane wait or new semantic hold.

Raw gates at /workspace/va1-evidence/numeric-traversal-next: core MCP 5.269s,
focused core build 3.107s, controls MCP 4.232s, controls build 2.098s,14 public
axiom reports 11.716s, all pass. Diagnostics contain zero errors/warnings/failed
dependencies, axioms standard propext/Classical.choice/Quot.sound only. Actual
Lean4.24.0/Lake5.0.0-src+797c613 observed in bounded task containers; every check
holds original writer lock, thread1/-j1, verified12GiB aggregate/no-swap and
12GiB host reserve before Lean. Maximum sampled aggregate RSS1538380 KiB, minimum
host available17120419840 bytes. Initial parameter-index reduction failure retained.

Independent read-only finder/skeptic source/control reviews found no issues;
neither edited or used Lean/server/build. Static gates pass:1088 reachable/
zero orphans,180 core/zero elaborator reach,491 automatic/61 budget/11 refuted/
zero manual or pending, trust1103 sources/248 sites/zero findings. Inventory
FAIL1 remains identical1206 pins/zero errors/404 unrecorded changes; strict docs
FAIL1 retains same85 frozen findings. Original full TypeExamples resource failure
remains a failure and latest concrete full validation remains pending. No
unchanged failed heavy check was repeated as an endpoint.

New exact interfaces and nontrivial clients will be exported after commit and
verification, separately from immutable144a2a9d export. The planned exact-head
PARALLEL-INTERFACE package is under /workspace/va1-evidence/numeric-traversal-next.
All global AU01 obligations, broader revised program-free boundary, AU02 array
pipeline/memory/halting-OR/general-fuel/normalizer obligations, remaining baseline/
performance/backfill and final gates remain incomplete. Q1 answered; Q2 held
only for frontend repair/full gates. No goal/VM reset, push/merge/PR/tag.

## AU02 independent simultaneous fixed-array pair — 2026-11-01

`Calculus/DecisionFixedArrayPair.lean` proves typed path divergence symmetry
and extension through every typed continuation, then composes two actual
fixedFloorAtPath saves. `fixedFloorPair_exists` derives both saves from actual
prefix presence plus divergence; it assumes no future save theorem.
`fixedFloorPair_reconstruction` constructs both original-floored lookup
equations and the complete frame for queries diverging from both prefixes.
Element types E/F, lengths n/m, breakpoint lists and every result type remain
intrinsic and independent. Each indexed equation retains its own length
membership premise; existence itself requires no breakpoint-membership premise.
`fixedFloorPair_second_absent` preserves refusal of a missing second prefix.

`Examples/DecisionFixedArrayPair.lean` inhabits the generic API with actual
mapping-key values and saves. Both selected observations change (11→9 and
9→7), a third key retains9, and an absent fixed-array sibling refuses. An
overlapping-prefix counterexample breaks the first lookup equation even with
both length breakpoints retained. Thus length membership cannot replace the
explicit divergence premise. These are kernel value/path facts, not EVM tests,
arbitrary-family reconstruction, overlapping nested composition, collector
integration or decision/Residue closure. No source predicate, model, default,
observation, verdict, refusal or budget is changed.

Raw gates at /workspace/va1-evidence/fixed-pair-next: core MCP 5.388s, core
build 4.172s, controls MCP 6.322s, controls build 3.179s,18 public axiom reports
4.207s, all pass. Complete diagnostics have zero errors/warnings/dependency
failures; axioms standard propext/Classical.choice/Quot.sound only. Original
writer lock, thread1/-j1, verified hard12GiB aggregate/no-swap and12GiB host
reserve apply to each check. Actual Lean4.24.0/Lake5.0.0-src+797c613 retained.
Maximum sampled aggregate RSS1211216 KiB; minimum host available17203998720 bytes. Initial
escaped-constructor and dependent-induction failures are retained.

Independent finder and skeptic source/control reviews found no issues, read-only
without edits/Lean/server/build. Static gates pass:1090 reachable/zero orphans,
180 core/zero elaborator reach,491 automatic/61 budget/11 refuted/zero manual or
pending, trust1105 sources/248 sites/zero findings. Inventory FAIL1 remains
byte-identical prior1206 pins/zero errors/404 unrecorded changes; strict docs
FAIL1 retains same85 frozen findings. Original Decision is byte-exact to base.
Prior full TypeExamples resource failure remains retained, latest full gate
pending; no unchanged stopped heavy build was repeated as an endpoint.

The numeric logical source-traversal checkpoint is committed/sealed at
0a773e1130eb75c073cb129431343de7532be541. Its new immutable PARALLEL-INTERFACE
bundle and370-file complete local import-closure source archive are under
/workspace/va1-evidence/numeric-traversal-next. Bundle SHA256:
14d4d92f0a3564b4fac68ff042d616d439cecdd6374c67f65093fb463c83d7e7;
archive SHA256:
0f53bc6039428dc21a5ef3a1c48aae2f0099d0517c4cd8e84cccbb96767e425e.
Both independent reviewers verified every file against exact committed blobs,
bundle/base/head and checksums; no findings. Source-only/combined-final-gatefalse
limits and unresolved normalizer identity are explicit, never assumed. Finder's
first relative checksum invocation used the wrong directory; its corrected
export-directory invocation passed. Neither reviewer ran Lean/server/build.

All global Residue/theorem/bridge, broader revised program-free boundary,
AU02 actual fixed/nested-array pipeline, broader memory/halting-OR/general-fuel/
normalizer proofs, remaining baseline/performance/backfill and final gates
remain incomplete. Q1 answered; Q2 remains only frontend repair/full-gate hold.
Next array pipeline work must reuse these checked components and audit existing
bounded/boolean preparations before implementing any additional expansion.
Goal/VM/branch unchanged; no push, merge, PR or tag.

## AU02 exact literal-bounded uint preparation — 2026-11-01

`Calculus/DecisionBoundedUInt.lean` proves `boundedUInt_inst_iff` for every
Contract/state/valuation/binder/canonical uint literal bound and every
quantifier-free LFml body. The body may contain arbitrary existing typed
storage/memory/ledger/hash terms and partial operands. Its actual guarded
finite instances are equivalent at every starting state; no flooring, new
validity/hash premise, semantic oracle or assumed future fact is used.
Complete samples use the real canonical uint round-trip, not a guessed domain.

Term and formula literal-substitution node counts and the real conjunction
builder yield the proved estimate `bound.val.toNat * (body.nodes + 5) + 1`.
`boundedUIntStep` checks that estimate against the unchanged511-node limit
BEFORE allocating samples. This is a per-expansion guard, not a bound on the
whole recursively prepared formula: all original whole-result checks remain
required. An oversized or unsupported quantifier is retained after its children
are prepared; its body may already have changed pointwise-equivalently. No budget
is raised.
Candidate extraction uses generalized-index LTm/Op2 casesOn and the existing
literal inspector, then `boundedUIntGuard?` verifies equality with the actual
strict guard through LFml.same. It cannot infer meaning from candidate data.

`boundedUIntExpand` builds an actual existing LFml with pointwise equivalence
bottom-up. `boundedUIntPrep` uses that theorem to preserve both polarities and
return the SAME original refuting state. This is a concrete semantic reduction,
not a new formula IR or a completion certificate. It is NOT hooked into the
decision pipeline in this checkpoint. Decision/ArrayBlock/HashPremise remain
byte-exact to frozen base; both frozen Covered/inTarget definitions, Waivers,
DecisionTheorem, observations and expected verdicts remain unchanged.

`Examples/DecisionBoundedUInt.lean` has actual frozen-source fixedBlock/fixedBad
leaves that become quantifier-free with exact pointwise meaning. Controls cover
zero-bound truth, oversized preservation, wrong binder/truth value/nonvariable
left operand refusals, strict versus optional halting, and a missing-sample
counterexample: truncated samples pass while the original universal is false;
complete samples retain that refutation. Kernel facts are distinct from native
classification/performance observations. Before-pipeline probe reproduces both
assigned pins as `(true,false,unknown)`; raw output and exact source identities
are retained. No verdict improvement/array-child completion is claimed yet.

Raw gates at /workspace/va1-evidence/bounded-uint-next after the review wording
correction: final core MCP 5.308s, focused core build 4.168s, final controls MCP
5.245s, controls build 4.221s,37 public theorem/runtime-definition axiom reports
7.369s and executable warm profile 4.161s, all pass. Complete MCP diagnostics have zero errors/warnings/
dependency failures. Axioms standard propext/Classical.choice/Quot.sound only;
no sorry/admit/native trust shortcut. Original writer lock, thread1/-j1,
verified hard12GiB aggregate/no-swap and12GiB host reserve apply. Actual pinned
Lean4.24.0/Lake5.0.0-src+797c613 observed. Maximum sampled aggregate RSS1708188 KiB;
minimum host available17002926080 bytes.

Initial successful warm executable preparation measurements (single invocation, imports/cache
already warm, noinline wrapper/IO input and forced output): real fixed leaf
qf=true 628067 ns; oversized1000 qf=false 57927 ns; oversized2^128 qf=false 31677 ns.
The wording-only exact-source repeat measured316116/23065/23245 ns respectively.
These are preparation timings, not full decision/cold-build/EVM results. Initial
list API, missing node import/argument order, conjunction arithmetic, candidate
elaboration and free-variable kernel-decision failures are retained. The local
probe initially targeted a declaration line instead of its tactic; corrected
positioned probes selected the closed arithmetic proof. The external profiler
initially had a missing namespace/name collision; original source/failure retained,
corrected profiler passes. No failed/stopped gate is relabeled passing.

Independent finder and skeptic source/control reviews found no issues, including
added refusal controls and exact allocation/meaning boundaries; neither edited
or ran Lean/server/build. Static gates pass:1092 reachable/zero orphans,180 core/
zero elaborator reach,491 automatic/61 budget/11 refuted/zero manual or pending,
trust1107 sources/248 sites/zero findings. Inventory FAIL1 unchanged1206 pins/
zero errors/404 unrecorded changes; strict docs FAIL1 same85 frozen findings.
Original full TypeExamples resource failure retained; latest full gate pending.

Next owned integration must first inspect speed history and warn, retain the
irreducible slot/length/APF preparation boundaries, then check a narrow concrete
pipeline change. Before/after classifications and kernel proved/refuted controls
are required before changing any assigned expected unknown pin. Unrelated
expectations and all budgets remain frozen. No producer-owned frontend repair.
All global AU01 residue/theorem/exhaustive target/hash bridge, broader revised
program-free boundary, remaining AU02 array/memory/halting-OR/general-fuel/
normalizer work, baseline/performance/backfill and final gates remain incomplete.
Q1 answered; Q2 only frontend repair/full-gate hold. Original goal/VM/branch
preserved; no stop/reset/new goal, push, merge, PR or tag.


## Checked bounded-array pipeline increment (2026-11-01)

Parent a878df9d84e9485728ad668e92f4b885c3740ace; frozen base and assigned branch
unchanged. Before changing ArrayBlock, inspected speed history
7c044e6a22b226be8b9a810c795a104ac4c87820 and warned about checking costs.
The old irreducible length/APF implementation is retained as baseBlockPrep.
blockPrep preserves that exact Prep when its body is quantifier-free or the
original OR-guarded folded array parser succeeds; only unsupported shapes try
the committed exact boundedUIntPrep followed by the original length/APF stages.
The old OR cap precedes fallback lifting. blockPrep_preserves_qf and
blockPrep_preserves_parsed certify equality of the entire original preparation,
including normalized forms. All whole-result budgets, source predicates,
DecisionTheorem, Waivers, hash premises and observations remain unchanged.
Decision and HashPremise are byte-exact to frozen base; the existing replay
sources/templates are unchanged from this checkpoint's parent.

Initial hook FAIL1 after911.379s: prepending finite preparation changed two old
replay normal forms. Raw failure and first source variant retained. Conservative
repaired affected build FAIL1 after954.361s with resource_stop=false: every old
consumer, including original ArrayReplay in39s, passed, then four obsolete
fixed-block noncoverage/unknown assertions failed. This is the observed assigned
improvement, not a hidden failure: fixedBlock/fixedBad now have inTarget=true,
Covered=true. All five other assigned array pins remain inTarget=true,
Covered=false, unknown, with their kernel certificates unchanged.

Only those two assigned classifications changed. fixedBlock_covered and
fixedBad_covered are kernel facts. fixedBlock_proved derives the actual .proved
verdict from coverage, structural hash-freedom and the original fixedBlock_valid.
fixedBad_refuted returns an actual state with decideGoal fixedBad = .refuted σ
and ¬ Fml.holdsH σ fixedBad, using completeness and the original false-control
semantics. That returned state is not asserted equal to the independent
fixedBadState countermodel, which remains intact. Both original formulas are
unchanged. The owned negative-instantiation consumer now uses
original_fixed_block_proved; its no_equivalence counterexample remains intact.
All zero/oversized/wrong-guard/partial-equality/omitted-sample controls remain.
This closes the two concrete fixed bounded-block pins, not arbitrary fixed-array
formulas or the whole AU02 fixed-array child.

Final exact-source gates in /workspace/va1-evidence/bounded-pipeline-next:

- ArrayBlock MCP19.157s; gap MCP18.088s; negative-consumer MCP4.281s;
  bounded-controls MCP5.261s: pass, no errors/warnings/dependency failures.
- Gap target build16.928s pass; serial affected consumer build138.128s pass
  (377 jobs; includes memory, numeric traversal, negative instantiation, bounded
  controls, fixed pairs, memory census and halting-OR controls). Previous changed
  source rebuild used warm upstream caches; no cache-clearing/full-cold claim.
  All rebuilt files remained below unchanged300s; largest observed109s ledger.
- 16 public axiom reports19.135s pass: standard propext/Classical.choice/Quot.sound
  only. Actual executable verdict observer3.110s pass: fixedBlock proved,
  fixedBad refuted. Warm per-call/output observations14629093/15252752ns;
  these are interpreted Lean runtime observations, not kernel or EVM evidence.

Every Lean operation used the original writer lock, LEAN_NUM_THREADS=1/-j1,
verified aggregate memory.max12884901888 and memory.swap.max0 before Lean,
and12GiB host reserve. Actual Lean4.24.0 commit797c613 and Lake5.0.0-src+797c613
observed. Final gates' maximum sampled aggregate RSS2522128KiB;
minimum host available16335290368bytes. No resource stops.
Original KeySort setup pass remains separate from final full gate completion.
Independent finder and skeptic final reviews found no additional issues after
the known consumer update; neither ran Lean/server/build or edited files.
Full notes, initial failures, source identities and reason census retained.

Original queue accounting: baseline/reason census partial; AU01 meaningful
Residue/DecisionTheorem-prime/exhaustive target-and-hash bridge open; module
split/performance checkpoints delivered but overall milestone eligibility open.
AU02 concrete fixed pins improved, standalone fixed/path/pair lemmas delivered;
general fixed/nested arrays, broader memory blocks, halting-OR repair, broader
human-revised program-free boundary, general formula-derived fuel/normalizer
closure and final full validation remain open. Backfill numeric source traversal,
shape/coverage bounds, fixed-path reconstruction, negative controls and axiom
checks delivered incrementally; remaining global bridge/reason census, complete
profiling/baseline and final affected/full gates remain. Q1 approved only the
certified boundary revision; Q2 frontend repair ownership remains pending.
Do not repeat the unchanged stopped frontend full build or claim another VM's
published workload as a local gate. No whole-goal completion, stop/reset/new
objective, push, merge, PR or tag. The immutable numeric PARALLEL-INTERFACE at
0a773e11 with370-file concrete closure, typed interfaces, clients and explicit
normalizer premise remains available unchanged. Further owned normalizer/Residue
implementation is ready independently of Q2; persistent full goal incomplete.

Static checkpoint gates:1092 reachable/zero orphans;180 core/zero elaborator
reach; strict automatic491/61 step budgets/11 refuted/zero manual or pending;
trust1107 sources/248 sites/zero findings: all pass. Inventory FAIL1 unchanged
1206 pins/zero errors/404 unrecorded changes. Strict docs FAIL1 same85 frozen
findings (48 missing/37 ambiguous); no added/removed findings. Exact source
comparison confirms frozen Decision, HashPremise and ProgramReduction bytes,
and replay/Core/facade unchanged from parent. Reviews caught automation text
appended outside M7-next and list spacing; both routine doc issues fixed.
All proof and full-goal limits above remain.


## Actual numeric normalizer/coverage bridge (2026-11-01)

Parent7092917807ce3918f5196028093fd210db36f069. New owned modules
Calculus/DecisionNumericNormalization and Examples/DecisionNumericNormalization;
shared edits are exactly two additive imports in Solidity.lean and two module-map
rows. No producer source, frozen predicate, premise, observation or budget change.

A proof-local actualNormalization captures the real private normalizeCore through
its public ProgramNormalization.ofFormula? wrapper. Typed unification/change
assigns the actual function; the saved probe prints that exact private function.
Concrete constructor equations and public proofs kernel-check against it. This
is not a copied algorithm, an oracle, or an assumed future producer API.

The initial identity plan failed: DeclarationReduction.andFormula/impFormula
remove tt operands. Raw errors/source retained. The public counterexample
normalization_changes_syntax certifies a five-node tt conjunction collapses to tt.
Rather than strengthen the input class or change the producer, the proved
invariant keeps both depth and shared node state explicit. With original source
weight≤each resource, the actual returned certificate has QFUIntLinear formula,
weight≤original weight, and initial budget≤remaining+original weight. Sequential
branches use the real remaining state from the first child. Original traversal
weight, not smaller normalized output weight, bounds consumption.

Public interfaces, for every contract/context and intrinsic source φ:
qfUIntLinear_normalization budget h hw returns actual d with ofFormula? budget φ
=some d, d.formula.QFUIntLinear and d.formula.weight≤φ.weight. For one positive
uint binder with original body source weight≤511, qfUIntPrefix_normalization
reserves one node/depth step of unchanged
2048 and returns an actual normalized body χ with the same grammar/bound.
leafOf_of_normalized_to composes through the possibly different normalized source.
qfUIntPrefix_logic_Covered derives Covered directly from φ.QFUIntLinear and
φ.uintQFWeight≤511, with no supplied leaf/normalizer equation. The source-derived
bound feeds actual lowering/preparation node proofs. qfUIntPrefix_logic_boundary
adds inTarget w=true under every frozen waiver setting and structural hash-freedom.
qfUIntPrefix_logic_answered and qfUIntPrefix_logic_certified give an actual nonunknown
answer with unchanged ValidH or returned-state ¬holdsH certificate. No reversed
unconditional inclusion or global DecisionTheorem-prime is claimed.

Inhabited positive/refuted clients use truth conjunction/implication around the
existing partial-arithmetic logical bodies (source weights143/199), consume only
the syntax/bound interface, and retain ordinary semantic proof/countermodel.
Actual smart normalization equations are separate controls, not supplied bridge
premises. Five-node collapse with depth4 but sharedbudget4 refuses;budget5 returns
tt. A short implication succeeds at actual budget3 while source weight>3,
showing the sufficient bound is not minimal. Zero-budget refusal and a retained
keyed-array unknown are kernel checked. No expected existing verdict changes.

Raw gates /workspace/va1-evidence/normalizer-next: core bridge MCP10.624s;
core target9.496s (new file7.3s); final controls MCP7.394s; controls/import-closure
build6.454s (367jobs,new file4.2s);27 public axiom reports19.155s; executable
warm verdict observer3.118s: all pass under unchanged300s per-file limit.
MCPs have zero items/dependency failures. Existing dependency warning replays are
retained; no new module warnings. Axioms are subsets of standard
propext/Classical.choice/Quot.sound only. Actual observations proved/refuted take
6623234/6273696ns including output. These interpreted Lean observations are
separate from kernel certificates, no EVM/full-cold/cache-clearing claim.

Original writer lock, LEAN_NUM_THREADS=1/-j1, verified hard aggregate12GiB/no-swap
and12GiB host reserve before every Lean process. Lean4.24.0 commit797c613,
Lake5.0.0-src+797c613 observed; maximum sampled aggregate RSS2149556KiB,
minimum host available16453763072bytes; no resource stops. Initial private-name probe,
false identity attempt and Option bind/map equation failures remain raw failures;
constructor equations were repaired against the actual computation. Both
independent read-only source reviews found no logical/scope issues; no Lean/server/
build or edits by reviewers. Exact producer ProgramReduction stays frozen.

This removes the previous numeric PARALLEL-INTERFACE's normalizer premise for
this bounded logical family. Old immutable packages/seals remain unchanged; new
committed interface package will record exact new head/source closure, signatures,
clients and remaining limits. Global meaningful Residue/DecisionTheorem-prime/
exhaustive target/hash bridge, remaining array/memory/halting-OR/revised-M4/general
fuel work, census/performance/backfill and final affected/full validation remain
open. Source-derived sufficient traversal/node bounds are proved for this family;
runtime fuels remain unchanged and full AU02 formula-derived-fuel work remains
open. Earlier TypeExamples resource stops and pending Q2
frontend ownership hold remain; no unchanged failed full build was repeated.
Q1 only revises the false reverse inclusion. Original full goal stays incomplete,
with independent work ready; no stop/reset/new goal, VM, push, merge, PR or tag.

Static gates:1094 reachable/zero orphans,180 core/zero elaborator reach, strict
automatic491/61 step budgets/11 refuted/zero manual or pending, trust1109 sources/
248 sites/zero findings: pass. Inventory FAIL1 same1206 pins/zero errors/404
unrecorded changes; strict docs FAIL1 same85 frozen findings, none added/removed.
Frozen Decision/HashPremise/ProgramReduction bytes confirmed. Final skeptic asked
for explicit≤511 on the prefix-interface description and precise fixed-fuel
sufficiency wording; both clarified, with no source or semantic change.


## Exact decidable reversed-field reason component (2026-11-01)

Parentc2b5d00f7f05292a00f86c87de314807c4b05d7d. New owned modules
Calculus/DecisionResidueReasons and Examples/DecisionResidueReasons; shared
registration edits exactly two additive imports and two module-map rows.
Audited integrated memory handoffs/APIs first. MemStructCut, MemStructWitness,
MemoryWitness and original DecisionMemory fixtures/observations remain unchanged;
no heap witness or parameter enumeration delivery is recreated. Decision,
HashPremise, both frozen predicates, all budgets and global strategy unchanged.

ReversedFreshField is an intrinsic source witness for every contract/context:
exactly one map-free fresh struct, a direct primitive literal on the left, and
a primitive field read on the right. It records x/s/f/p/value, actual field lookup,
existing map-free admission and complete syntax equality. The parser reuses
producer allocView/eqView/literalTerm and full typed-term equality, then enumerates
actual struct fields. No target, coverage or verdict is queried. The one-line
reason is that the existing fresh-struct schema requires the field on the left
and a direct literal on the right.

reversedFreshField_witness proves recognition soundness;
reversedFreshField_complete proves every exact typed source witness is recognized,
using successful lookup membership and finite field search. reversedFreshField_iff
identifies the Boolean with Nonempty(ReversedFreshField φ); a computable Decidable
instance decides that proposition without a coverage/unknown oracle. This is one
precise named reason component, not the exhaustive Fml.Residue union or its bridge.
Matching does not assert that every global decision must remain unknown.

The same typed witness yields an independently usable MemoryWitness.Answer.
counterState reuses exactly the producer children/adopted heap BEFORE parent
allocation; counterState_refutes transports its existing field countermodel by
equation symmetry at the SAME state. hashFree and counterState_refutesH expose
structural hash-freedom and unchanged ¬holdsH, with no new validity/hash premise.
The global pipeline is deliberately unchanged at this reason-component checkpoint.

Inhabited controls: original reversed0, another literal5 and Boolean reversal
all classify true. Supported normal/reflexive/fixed/Boolean equations, another
real compound-RHS gap, given-heap parameters and map-bearing sources classify
false. Exact Decidable positive/negative propositions execute under kernel decide.
originalState = producer gapMemStruct_state by kernel equality, with ordinary and
hash-premised refutation plus nonvalidity. Original target/notCovered/unknown
certificates are reused unchanged. A covered reflexive source stays outside this
class, so it is neither fixture equality nor all fresh memory.

A new control initially guessed mappingReversed.inTarget=false; the kernel
proved that assertion false. Saved failed source/raw retained. The actual control
now proves inTarget=true, while the existing map-free class guard rejects it.
This distinguishes target admission from producer recognition; no predicate,
expected existing verdict, premise or exclusion changed. This map-bearing target
shape remains unaccounted for in the eventual exhaustive reason census.

Raw gates /workspace/va1-evidence/residue-reasons-next: final core MCP5.278s
(clean, actual core source SHA retained); final core target4.125s (67jobs,newfile
1.5s); final controls MCP5.258s; new import-closure target3.187s (350jobs,newfile
1.3s);29 public theorem/decider/state/answer axiom reports8.423s; actual classifier
observer3.102s: pass. All below unchanged300s; dependencies cached, no full-cold
or cache-clearing claim. Axioms subsets of propext/Classical.choice/Quot.sound.
Warm observer with output original/five/bool=true, supported/otherGap/mapping=false;
per-call/output1761496/69455/105289/9454/2714/43746ns. These are source-class
observations, not kernel or EVM evidence and not global verdict timings.

Original writer lock/thread1/-j1, verified hard aggregate12GiB/no-swap and12GiB
host reserve before Lean; Lean4.24.0 commit797c613/Lake5.0.0-src+797c613 observed.
Maximum final sampled aggregate RSS1437456KiB/minimum host available17204912128bytes,
no resource stops. Initial structure-field syntax, dependent-body rewrite,
Option/true-guard completeness and new false mapping-admission assertion failures
retained. Multi-attempt tool process exited0 but candidates had parser errors
because replacement removed a constructor closing bracket: NOT proof passes.
Final source uses explicit equality composition; all complete-file MCPs are clean.

Both independent read-only source reviews found no remaining issues after adding
completeness/Decidable; neither ran Lean/server/build or edited files. Exact source
family, producer state/premises and limits retained. Global Residue/theorem/exhaustive
target/hash bridge, other array/memory/OR/revised-M4/formula-dependent-fuel children,
remaining census/performance/backfill and final affected/full validation remain
open. Q2 frontend repair held, old TypeExamples resource failures retained; no
unchanged full failure repeated. Original full goal incomplete with ready work;
no stop/reset/new goal/VM, push, merge, PR or tag. Existing concrete numeric
PARALLEL-INTERFACE atc2b5d00f remains immutable and independently audited.

Static gates:1096 reachable/zero orphans,180 core/zero elaborator reach, strict
automatic491/61 step budgets/11 refuted/zero manual or pending, trust1111 sources/
248 sites/zero findings: pass. Inventory FAIL1 unchanged1206 pins/zero errors/404
unrecorded changes; strict docs FAIL1 same85 frozen findings, none added/removed.
All29 actual axiom sets independently parsed/audited as standard-only. Frozen
Decision/HashPremise/ProgramReduction and all three memory producer modules
byte-exact; original DecisionMemory unchanged from parent. Final finder caught
resource aggregation missing the final source-matched core MCP; corrected to
include all six final passing checks. Both source/docs reviews otherwise clean.


## Exact nonliteral uint-field reason component (2026-11-01)

Parent6cae581963831b65de639e0a79e81dfd79f18243. New owned modules
Calculus/DecisionCompoundFieldReason and Examples/DecisionCompoundFieldReason;
shared registrations exactly two additive imports and two module-map rows.
Existing reason, arithmetic decoder, memory producer and global decision code
are unchanged. No predicate, premise, observation or budget change.

NonliteralUIntFreshField is a second exact source family, distinct from reversal:
one map-free fresh struct, direct uint field on the left, and an actual RHS in
the existing Tm.UIntLinear grammar whose root is not a direct primitive literal.
The witness carries complete source equality. Existing uintLinearShape evidence
is reused rather than duplicating arithmetic parsing. The parser uses producer
alloc/eq views, field lookup and full typed term comparison. Soundness,
completeness, iff Nonempty and a constructive Decidable instance kernel-check
for every intrinsic contract/context. No coverage, target or verdict is queried.
One-line cause: the existing field schema expects a direct literal RHS, whereas
this uint-linear RHS has a nonliteral root. Structural hash-freedom is proved.

Controls: original memStructBuried,2+3 and partial0-1 classify true; direct
literals/reflexivity/reversal/Boolean/fixed/given-heap/map-bearing controls false.
Both reason tags remain distinct on the actual old fixtures. Exact witness-family
positive/negative decisions execute under kernel decide. Map-bearing input stays
target-admitted while the existing map-free schema refuses it; no exclusion added.

The actual buried fixture is now proved false at the UNCHANGED producer
child heap gapMemStruct_state. Pointwise sum01_eval/denote (for every contract/
context/state) transports0+1 to literal1, then the existing producer fieldEq_refutes
supplies the same before-parent counterstate. Ordinary and exact hash-premised
countermodel/nonvalidity follow. zeroMinusOne.eval=none is separately checked;
classification does not imply a terminating/literal-valued RHS. Original target,
notCovered and globalunknown pins remain unchanged. No generic countermodel for
every class member or global pipeline integration is claimed.

Important acyclic integration boundary: this proof-layer module depends on
Decision through UIntShape→NumericCoverage→NumericBounds→NumericFormula→
LeafPreparation→UIntPrefix→UIntFormula→UIntGrammar. It cannot be imported directly
back into Decision. Actual dependency path is saved in integration-dependency.json;
a concrete lower-level interface is required before production integration.
The earlier reversed-field component has no such dependency and can progress
independently. No cyclic import or assumed future API was introduced.

Raw gates /workspace/va1-evidence/compound-reason-next: final core MCP5.252s,
core target3.179s (270jobs,newfile1.6s), controls MCP5.292s, controls/import-closure
build3.159s,25 public axiom reports6.300s, actual source-class observer3.100s:
pass. MCP zero items/dependency failures; all below unchanged300s, warm dependency
caches retained. Axioms standard-only. Class observer original/another/partial=true,
direct/reversed/mapping=false; per-call/output1781756/41632/23245/14461/4056/35433ns.
These source-class runtime observations are separate from kernel/EVM evidence
and global verdict profiling. Initial hash lemma Boolean grouping failure/source
retained, fixed with explicit typed equality composition; no theorem weakened.

Writer lock/thread1/-j1, verified hard aggregate12GiB/no-swap and12GiB host reserve
before every Lean process. Lean4.24.0 commit797c613/Lake5.0.0-src+797c613 observed.
All-six final gates maximum aggregate sampled RSS1614752KiB/minimum host available
17127366656bytes, no resource stops. Both independent read-only reviews found no
source issue; neither used Lean/server/build or edited files.

Global Fml.Residue/DecisionTheorem-prime/exhaustive target/hash bridge, remaining
AU02/backfill/performance/full gates remain open. The next ready independent
implementation is reversed-field Answer integration with exact old-answer/state
preservation. Producer handoff explicitly permits certified mxTop=none fallback
composition; keep cut-first routing and preserve producer implementation/heap
observations. Compound integration remains the narrow dependency above, not a
whole-lane block. Q2 frontend repair held; original full goal incomplete. No
stop/reset/new goal/VM, push, merge, PR or tag.

Final source strengthening: NonliteralUIntFreshField.schema_refuses proves the
actual producer fieldEquation returns none on every class member. Typed
UIntLinear evidence excludes its reflexivity branch; nonliteral root excludes
its literal branch. This certifies the one-line cause for that schema only,
not globalunknown. Both independent reviewers found no issue.

Exact strengthened-source final gates supersede the initial25-report timings
above: core MCP5.350s/core build4.206s; controls MCP4.246s/closure4.156s;26 public
axiom reports7.377s; observer3.103s, all pass. Final warm observer outputs unchanged,
times1834515/34933/20771/13210/3936/32789ns including output. All-six final resource
aggregate maxRSS1664380KiB/minhost17153732608bytes; no stops. Initial raw gates/profile
remain retained. Full global obligations and production-cycle limits above unchanged.

Final static gates:1098 reachable/zero orphans;180 core/zero elaborator reach;
strictautomatic491/61 budgets/11 refuted/zero manual or pending; trust1113 sources/
248 sites/zero findings: pass. Inventory FAIL1 unchanged1206 pins/zero errors/404
unrecorded changes; strictdocs FAIL1 same85 frozen findings. All26 actual axiom
sets audited standard-only. Both final docs reviews clean; finder independently
recomputed all-six resource extrema. Frozen decision/hash/program/memory producer
bytes unchanged. No full-gate or whole-goal completion claim.


## Checked reversed-field global route (2026-11-01)

This closes the assigned orientation gap, not AU01/AU02 as a whole.
Calculus/DecisionMemoryExtension preserves every successful original producer
Answer, including its state transformer, and lazily consults the exact reversed
source witness only on none. Decision changes only the shared helper in
decideStruct/memCovered and matching completeness proof; the original public
decideStruct_complete signature and array-cut-first route remain. No producer
implementation or heap-observation graph is rewritten.

Calculus/DecisionMemoryCoverage proves for every C, closed φ:Fml C [], and
w:ReversedFreshField φ: actual preparation/hoist identities, cut_none,
hasAllocAll, memCovered, Covered, inTarget under every waiver setting,
answeredness and an actual returned refutation under the unchanged holdsH
reading. No coverage/route/verdict premise is supplied. The generic existential
does not identify a chosen countermodel. Separately, the original fixture
kernel-proves decideGoal memStructReversed = .refuted gapMemStruct_state by rfl;
decideGoal_refutes certifies that exact before-parent child-heap state. UInt-five
and Bool clients prove actual Covered/returned refutation. Mapping, buried and
given-heap unknowns, and all old normal/signed/fixed/heap observations remain.
Only the assigned guarded tuple changes [unknown,unknown,refuted] to
[refuted,unknown,refuted], after actual improved output and matching certificates.
Earlier unknown seals remain historical evidence superseded for this one pin.

Exact-name Covered/inTarget/Waivers/DecisionTheorem declaration slices are
byte-identical frozen base. Covered behavior intentionally expands through
memCovered; no unchanged-extension or false reverse-inclusion claim is made.
An initial prefix selector matched CoveredA: preservation-selector-failure.json
records the evidence bug and the corrected exact-name check. HashPremise,
ProgramReduction, MemStructCut, MemStructWitness and MemoryWitness whole files
remain byte-identical frozen base. Shared registrations are two additive root
imports and two module-map rows; no Rules edit.

Evidence: /workspace/va1-evidence/reversed-integration-next. Initial affected
build FAIL1 after891.866s only on the observed improved tuple; raw output kept.
Its certified update passed memory MCP/build69.261/68.193s. Review found a stale
comment; its fix invalidated dependencies. Refreshed MCP auto-setup overlapped
LSP and dependency compilation and stopped at host reserve: FAIL137/wrapper75,
102.066s, resource_stop=true, max sampled RSS6100448KiB, minimum host available
12852588544bytes. Repair: sanctioned explicit-j1 affected build without LSP
first, then warm diagnostics; no guard or proof budget changed.
Affected376-job build PASS953.647s; largest reported file110s (ledger),
arithmetic95/operators106/memory67/array replay36s, all below300s. This is an
affected cache invalidation, not a claimed fresh/full project gate. Each raw
metadata JSON retains actual command, source hashes, toolchain and cache context.
Final warm MCP helper4.240/coverage4.177/Decision33.250/Memory69.149/census5.247/
controls5.246s pass; low-level reason MCP5.215s passes. Public24-theorem axiom
report PASS22.300s, only existing propext/Classical.choice/Quot.sound, no new axioms.

Runtime-only profile PASS3.095s: original/literal-five/Bool refuted and
buried/mapping/given-heap unknown. Observation timings include printing:
3.988/.291/.262ms and .394/.156/1.335ms respectively. Initial harness FAIL1
mixed StandardExample/Gaps in one typed list; exact failing source/output kept,
repaired only in that external harness. Kernel certificates are separate;
no compiler/EVM check or other-VM timing is claimed.

Final checks hold original writer lock, threads1/Lean-j1, one task child,
actual memory.max12884901888/swap.max0, host reserve12884901888bytes. Passing
sampled aggregate RSS max5313100KiB (shared pages included), charged cgroup peak
4470992896bytes, host available min13200699392bytes. resources.json retains
all extrema and failed measurement samples. Initial metrics aggregation failed
parsing OCI error text as an integer; fixed to use only successful numeric
samples and retained failed samples/error description. The failed LSP auto-setup
overlap above is not hidden; final diagnostics used already emitted dependencies.
Strict automatic491/61budgets/11refuted, layers180core, reachability1100 and
trust1115sources/248sites pass. Same85 docs and404 inventory findings remain
FAIL, identical to retained frozen-base analysis; no findings/pins deleted.

Independent read-only finder: no source findings; suggested UInt/Bool clients
implemented and checked. Skeptic: stale comment confirmed/fixed, final no
findings; independently verified exact-name frozen declarations, nonvacuity,
old Answer/state preservation and retained controls. Neither used Lean/server,
builds or edits. reviews.txt retains results. PARALLEL-INTERFACE export remains pending until commit; it must use
only the checked committed tree: actual modules/signatures, exact producer
hashes/premises, nontrivial clients, complete import closure and immutable
bundle/archive/checksums. Source-only handoff; final combined/full closure open.

Every original open queue remains accounted for: global meaningful Residue,
DecisionTheorem-prime/exhaustive target/hash bridge, nested/general arrays,
compound/given-heap broader memory, halting OR, broader revised M4 boundary,
formula-derived runtime fuel, remaining profiling/backfill and final/full gates.
Held VA1-Q2/producer TypeExamples repair is not resumed. Next independent child:
given-heap literal-read reflexive source family using existing MxObs syntax and
extractor, with validity over every heap/binder value. No whole-goal completion,
goal mutation, publication, push/merge/PR/tag.


## Given-heap literal-read source certificate (2026-11-01)

Independent owned AU01 reason-census/AU02 broader-memory progress. Low-level
Calculus/DecisionGivenHeapReason.lean imports only existing MemObserve,
MemStructCut and HashPremise. For every contract C/context Γ, its intrinsic
GivenHeapLiteralReadReflexive witness retains the complete equation for one
box-bound dynamic uint array, with the same direct literal-index read on both
sides. Parser reuses producer eqView and mxObsReadKey?, checking both entire
terms against MxObs.read reconstruction. Exact soundness/completeness/iff and
computable Decidable membership are proved without target/Covered/verdict tests.
One-line reason: the existing finite given-heap fallback searches countermodels
at one heap, which cannot establish validity over every heap and binder value.
Generic validity explicitly quantifies over every State C Γ and optional binder
value, including unset; Theory equality reflexivity needs no evaluation-definedness
premise. hashFree and validH preserve the existing interpretation, and .answer
provides MemoryWitness.Answer.proved from that universal proof. No one-state
checker result is promoted to validity.

Proof-layer Calculus/DecisionGivenHeapBoundary.lean separately imports Decision,
keeping the low-level Answer acyclic and ready for later pipeline consumption.
Its target theorem proves closed-family admission for every waiver setting.
Additional candidate_answer and candidate_route certify existing negative-state
selection: the actual checkMemoryAt negative branch returns exactly the producer
candidate; hashfalse/LeafAunknown/noalloc/checker-isNo premises explicitly select
that existing global route. Both old parameter and alias clients discharge every
premise by rfl/kernel decide and retain exact candidate-state equality plus
returned holdsH refutations. No coverage/pipeline extension is claimed here.
Decision, Covered/inTarget/DecisionTheorem/Waivers, producer implementations,
semantics/defaults and all old observations are unchanged since2e992aaf.

Examples/DecisionGivenHeapReason.lean supplies original/another-index inhabited
source decisions, universal validity and actual targets; the original remains
unknown/notCovered and the second remains unknown. Generic actual fixed-array,
diamond and fresh-allocation refusal theorems cover every body. Clients refuse
unequal keys, computed index, direct literal reflexivity, fresh source and old
negative parameter/alias forms. Valid computed/literal refusals distinguish
classification from validity. Actual read observations pin a defined value1,
out-of-bounds none and unset none, over the unchanged producer candidate heap
and initial heap. Both empty/nonempty root states satisfy the proved family.

Actual new fixture correction: dl![.diamond] on a leaf-only hidden declaration
elaborates to exactly memParamSame (box source), kernel rfl equality checked;
it is therefore a positive classification. The initial combined negative claim
was kernel-disproved and retained with exact failing source/hash. The correction
records actual source identity, not a changed default or notation; the genuine
intrinsic diamond refusal remains universally proved. Initial generic refusal
signatures also required explicit Fml constructor receivers. Completeness needed
one final Option.pure reduction; MCP blank-line/multiline replacement probes had
syntax errors, which are not counted as proof passes. Raw diagnostics and exact
hash-verified failing snapshots are in /workspace/va1-evidence/given-heap-reason-next.

Both optional exact old returned-state rfl proofs failed. They were not treated
as passing observations or weakened: candidate_answer now normalizes the producer
let and splits the real checker; candidate_route establishes the memory verdict
before collapsing outer fallback matches. An intermediate rewrite had already
been discharged by cases; its failed raw/source is retained. Final client proofs
preserve the original exact-state statements and certify actual returned holdsH.
Reviewers explicitly distinguished earlier source targets from kernel validation.

Final gates: core MCP5.250s, boundary MCP5.274s, clients MCP5.332s, emitted affected
client/import closure3.095s pass. Core/boundary emissions4.125/3.096s passed at
the corresponding stages. All use pinned Lean4.24.0 commit797c613/Lake5.0.0,
original writer lock, threads1/Lean-j1, one task container, no LSP/build overlap,
actual memory.max12884901888/swap.max0 and host reserve12884901888bytes. Exact
sampled resource extrema: RSS1463088KiB (shared pages included), charged peak
630624256bytes, minimum host available17068548096bytes; resources.json retains
10 failed measurement samples, excluded only from numeric extrema, never from raw evidence.
Public36-declaration axiom audit PASS16.948s contains only existing standard
propext/Classical.choice/Quot.sound subsets; no new axioms/sorry/trust shortcuts.
Runtime profile PASS3.163s: original/another-index true+unknown; computed-index
false+unknown; diamond-notation true+unknown; parameter/alias negatives false+
refuted. Timings including printing2.996/.355/.250/.310/.613/.217ms respectively.
Kernel proofs and runtime-only profiling are distinguished; no EVM result claimed.

Static reachability1103, layers180core, strict automatic491/61budgets/11refuted,
trust1118sources/248sites and whitespace pass. Same85 docs and404 inventory
findings remain FAIL, identical to prior exact-frozen-base analysis. Three root
imports and three module-map rows are narrow additions, no Rules changes.
Independent read-only finder/skeptic final source reviews report no findings;
real syntax identity, universal certificate, explicit routing premises, exact
old counterstates and remaining unknowns all reviewed without Lean/server/builds
or edits. reviews.txt retains results. Immutable checked committed export/seal
remains pending until this checkpoint commits; existing2e992aaf artifacts stay.

Original full queue remains incomplete: global Residue/DecisionTheorem-prime and
exhaustive target/Covered/hash bridge, general/nested arrays, wider memory beyond
these exact families, halting OR, broader revised M4 boundary, formula-derived
runtime fuel, remaining performance/backfill and final/full gates. The new valid
Answer is not yet consumed by decideMem; that integration is ready owned work,
not blocked by held producer TypeExamples/VA1-Q2. No goal/status reset, whole-lane
completion or publication authorization is inferred.


## Certified given-heap pipeline integration (2026-11-01)

The ready4feb9c source certificate is now consumed. New
Calculus/DecisionGivenHeapExtension.lean lazily wraps every successful existing
countermodel as an Answer.refuted with exactly that state; only none consults the
exact all-heap reflexive literal-read Answer. Decision adds decideGiven with
sound/refutes/complete and exact countermodel-state preservation, uses it only
in the no-allocation memory branch, and adds the exact source class to
memCovered. Fresh-array cut and fresh-struct fallback order are unchanged.
Both Covered/inTarget direct definitions, Waivers and DecisionTheorem signatures/
bodies remain byte-identical frozen base; adjacent documentation is corrected.
Covered behavior intentionally expands via memCovered. Producer implementations,
HashPremise, ProgramReduction, MemObserve and held frontend TypeExamples remain
whole-file byte-identical base (static-differential.json). No producer API,
semantics/default, exclusion, hash premise or proof/resource budget changes.

Generic GivenHeapLiteralReadReflexive.noAlloc is derived from full source syntax.
The proof layer now proves actual memCovered/Covered and decideGoal φ=.proved
for every C, closed φ:Fml C [], witness w of this exact source class. No coverage,
verdict or route premise is supplied. Actual completion plus hash freedom rules
out unknown; w.validH plus existing refutation soundness rules out refuted.
Existing negative candidate_route retains all its original explicit premises,
now using decideGiven_preserves_countermodel to retain exact states.

Original memParamSame and another literal-index source improve
(target=true,Covered=false,unknown)→(true,true,proved), with actual positive
holdsH certificates. The parent guard changes only its assigned first tag:
[unknown,refuted]→[proved,refuted]. Its all-state source certificate is proved
before that update; no truth at one checked heap is promoted. NumericCoverage's
assigned memory conjunct and Census/own example aliases use the actual proved
certificate; the entire preceding numeric prefix (including517-node
Covered=false/hashCovered=false/proved and folded-large controls) is byte-identical.
The prior4feb9c unknown/noncoverage seals remain immutable historical evidence.
Computed-index, buried-field and mapping target controls remain unknown/noncovered;
old parameter/alias actual returned candidate states and holdsH refutations,
reversed exact child-heap refutation, all given-heap defined/OOB/unset observations
and all existing signed/array/heap outputs remain.

Raw evidence: /workspace/va1-evidence/given-heap-integration-next. Warned before
core import/cache invalidation and inspected06a8d16/f31-related speed history.
Helper MCP3.159/build3.261s pass. First Decision MCP FAIL34.135s on invalid
Bool.or_eq_true.mp use; elaboration-recovery sorryAx cascades were nonpasses,
not source axioms or changed expected reports. Fixed proof MCP34.303/build31.906s
pass unchanged guards. Generic bridge MCP4.170/build3.096s passes.
Finder/skeptic found stale comments and one missed numeric consumer. Stopped only
our first affected container at211.373s/exit137, resource_stop=false; explicit
stop command/reason retained. Repaired source, verified four frozen direct
definitions and numeric prefix, then Decision MCP37.684s passed before restarting.
This was a changed-tree repair, not an unchanged stopped-build endpoint.

Cold changed-tree affected run FAIL1 after1002.578s, resource_stop=false: old
reversed coverage proof expected the prior Boolean shape. Independent consumers
completed (Memory68s, ledger114s, arithmetic90s, remaining files below300s).
Repaired that proof by deriving new given-class=false from the existing exact
fresh witness, preserving its statement. MCP4.242s passes; warm selected closure
PASS380jobs22.358s. Final8 edited-file MCPs pass: helper4.323, Decision36.289,
boundary4.160, Memory74.940, census5.327, given controls5.241, reversed5.262,
numeric30.951s. No file exceeds unchanged300s.

First public68 audit FAIL1/57.421s: the edited NumericCoverage example was checked
in MCP but omitted from emitted targets, leaving an old olean. No theorem/axiom
expectation was changed; explicit complete affected target list now includes it.
Complete affected build PASS3.147s; unchanged68 audit PASS60.736s, all only existing
propext/Classical.choice/Quot.sound subsets. This emission correction, failed
raw report and final actual declarations are retained. Runtime-only profile
PASS3.099s confirms actual target/Covered/verdict for both positives, both exact
negative candidate refutations, reversed refutation and three remaining unknowns.
Timings including printing3.724/.379/.588/.273/.560/.305/1.711/.328/.303ms
(original, another-index, computed, diamond-notation, negative-param, alias,
reversed, buried, mapping). No EVM/other-host performance claim.

All final commands hold original writer lock, one task child, threads1/Lean-j1,
actual memory.max12884901888/swap.max0 and host reserve12884901888bytes. Exact
passing extrema: sampled RSS4611476KiB, charged cgroup peak3427799040bytes,
host available minimum14261637120bytes. resources.json retains19 failed
measurement samples. Each gate JSON
records command/toolchain/head/source hashes and raw output. Passing original
KeySort setup evidence remains separate from full validation. Static strict
automatic, reachability/layers/trust and whitespace pass; same85 docs/404 inventory
findings remain FAIL, compared to frozen-base analysis, with no findings hidden.
Full ./run-lean.sh remains pending the held producer TypeExamples/VA1-Q2 repair;
no unchanged stopped full/frontend gate was repeated or claimed passing.

Independent read-only finder/skeptic source reviews found the missed consumer/
comments and verified their repairs, exact old states, all-heap positive proofs,
remaining unknowns and preserved numeric controls. Final reversed coverage repair
reviewed with no further findings; neither reviewer used Lean/server/builds or
edits. Final documentation/export review and committed package seal are pending
until this checkpoint is committed. Prior2e992aaf and4feb9c seals are retained.

Whole original assignment remains partial: meaningful global Residue union,
DecisionTheorem-prime/exhaustive target/Covered/hash bridge, fixed/nested/general
arrays, broader compound/memory blocks, halting OR, broader revised M4 boundary,
formula-derived runtime fuel, remaining performance/backfill and final/full gates
are open. Ready next owned children: minimal UInt syntax/recognizer de-layering
for the compound-field certificate (warn/inspect history before refactor), and
exact formula-work consumption proof without raising runtime2048/511 budgets.
No AU05/AU06, VA2/compiler/decoder takeover, scope/goal reset or publication.


## Acyclic UInt syntax/recognizer prerequisite (2026-11-01)

Owned compound-field dependency repair after sealedb14b8c77. Warned before
possible cache invalidation and inspected f31bd931/c5952b99 speed history.
Calculus/DecisionUIntSyntax.lean now contains the existing intrinsic
Tm.UIntLinear inductive and Decide.uintLinear_hashFree proof. Lower
Calculus/DecisionUIntRecognizer.lean contains the entire existing typed evidence
parser, shape soundness/completeness/iff and constructive instance. All three
blocks move byte-for-byte exactly once (moved-block-identities.json); no new
arithmetic/decoder or untyped representation. Original Grammar imports Syntax
and retains translations/agreement/admission; original Shape imports Recognizer
and retains the existing coverage/certification wrappers. Public names/types
remain, including generated Solidity.instDecidableUIntLinear, confirmed in both
ilean records. Generalized casesOn/structural recursion layout is unchanged.
CompoundFieldReason now imports Recognizer instead of the high Shape facade.
Its actual69-module local closure no longer reaches Decision; no source imports
are missing (acyclic-low-closure.json). This removes the documented integration
cycle; it does not yet supply the generic compound countermodel or pipeline hook.

All gates pass under pinned4.24.0/5.0.0, original writer lock, serial threads1/
Lean-j1, one child and actual memory.max12884901888/swap.max0 plus12GiB host
reserve: Syntax MCP7.397/build6.298s, Recognizer MCP4.156/build3.089s,
Compound MCP5.263s, Grammar compatibility MCP10.604/build8.440s, complete listed
affected consumers39.522s, Shape compatibility MCP4.167s. Public27 actual type/
axiom declarations checked through original imports pass6.320s, only existing
standard axiom subsets. No budget, verdict, source classification or semantic
observation changes. Every command/source hash/raw output and sampled resource
extremum/failed measurement is retained in /workspace/va1-evidence/uint-layer-next.
Measured sampled RSS2062040KiB, cgroup peak1147629568bytes, host available
minimum16535592960bytes;18 unsuccessful measurement samples remain retained.
No separate runtime speedup claim or EVM evidence is made for a verbatim move.

Reachability1106, layers180core, strict automatic491/61budgets/11refuted,
trust1121sources/248sites and whitespace pass. Same85 documentation/404 inventory
findings remain FAIL and match frozen-base analysis. Decision whole file is
unchanged fromb14; the four frozen direct definitions, hash/validity premises,
producer implementations and all previous controls remain. Shared registrations
are two additive root imports/two module-map rows, no Rules edits.
Independent read-only finder/skeptic source reviews report no findings and verify
actual blocks/names/graph; neither used Lean/server/builds or edits. Final docs/
export review and committed sealing remain pending. Previous seals retained.

Next concrete missing theorem is optional-denotation independence for a UIntLinear
term in a memory-only context, including partial expressions. That proof can
then certify a closed compound fresh-field equation at the producer child heap
before parent allocation, choosing a differing field for some RHS or a defined
field against none. No such theorem is assumed here. Outer scalar contexts need
separate treatment; no all-context countermodel or global memory completion is
claimed. All original Residue/theorem/hash bridge, arrays, memory/OR/M4/fuel,
performance/backfill/full gates and held VA1-Q2 remain incomplete. No publication
or goal reset/completion.


## Closed compound-field countermodel certificate (2026-11-01)

After sealed23ba6991, Calculus/DecisionUIntConstant.lean proves, explicitly for
all C:Contract/R:RefTy/t:Tm C [mem R] (val uint), evidence h:t.UIntLinear and
arbitrary σ/τ:State C [mem R], equality t.denote σ=t.denote τ. This is equality
of full Option readings across different heaps, not only agreement on successful
evaluation. Impossible scalar locals are eliminated structurally; literals and
pure arithmetic use existing actual denotations. No halting/default premise,
evaluator change or fresh arithmetic implementation is introduced.

Calculus/DecisionCompoundCertificate.lean reuses the existing map-free field
realization and defines the exact producer child heap before parent allocation.
For every C, closed φ:Fml C [], NonliteralUIntFreshField witness w and arbitrary
initial σ, it constructs ¬holds(w.counterState σ)φ. Evaluate the constant RHS
option at the child state with unset memory local. In some v, existing
fieldEq_refutes selects a differing parent field; optional-denotation independence
transports the RHS at each parent. In none, a parent with field0 has defined
some0 reading, contradicting RHS none. Thus partial arithmetic is retained;
no value is substituted for an undefined expression. Same-state holdsH refutation
uses the unchanged hashFree/holdsH_iff route, and .answer is a real typed
MemoryWitness.Answer.refuted. CounterState can be formed contextually; refutation/
Answer are deliberately restricted to closed leaves. Outer scalar contexts
require separate invariance arguments and are not claimed here.

Examples/DecisionCompoundCertificate.lean obtains actual parser witnesses for
original buried0+1, another2+3 and partial0-1. All three counterstates kernel-equal
existing gapMemStruct_state before parent allocation. Actual optional Theory
readings are pinned some1/some5/none, alongside ordinary/holdsH countermodels,
inhabited typed Answers and target admission (including partial RHS). All three
global verdicts remain unknown; no producer fixture or expected global verdict
changed. Existing literal/reversed refutations and mapping unknown remain.
Decision and source-class files are whole-file unchanged from23ba; four frozen
direct predicates/statement, hash/validity premises and all budgets remain.

Raw evidence /workspace/va1-evidence/compound-certificate-next. All8 gates pass:
constant MCP4.283/build3.095s, generic certificate MCP5.263/build3.108s,
controls MCP5.210/build4.120s, public13-declaration actual type/axiom audit6.314s,
runtime-only profile3.098s. Only existing standard axioms; no sorry/new axioms or
native trust shortcut. Profile confirms original/another/partial class=true,
Covered=false,unknown; direct/reversed controls class=false,Covered=true,refuted;
mapping class=false,Covered=false,unknown. Timings including printing
2.907/.375/.280/1.113/.455/.556ms. This is not EVM evidence or pipeline integration.
All use pinned4.24.0/5.0.0, original writer lock, threads1/Lean-j1, hard12GiB/
no-swap container and12GiB host reserve; raw metadata/resources.json retains
measured aggregate RSS1444280KiB (shared pages included), cgroup peak612163584bytes,
host available minimum17211600896bytes and16 unsuccessful measurement samples.

Reachability1109/layers180core/strict automatic491/61budgets/11refuted/trust1124
sources/248sites and whitespace pass. Same85 docs/404 inventory findings remain
FAIL, unchanged against frozen-base analysis. Three root imports/three module-map
rows are additive. Independent read-only finder/skeptic reviews find no issues,
including genuine optional-none handling, closed scope, exact producer state and
remaining unknowns; neither used Lean/server/builds or edits. Final documentation/
export review and committed seal remain pending; old seals are preserved.

Ready next owned work: lazily compose this actual Answer after existing struct
answers and prove actual source-to-Covered/returned-refutation routing, then
update only assigned pins with matching certificates. All original global
Residue/DecisionTheorem-prime/hash bridge, arrays, wider memory, halting OR,
broader revised M4 boundary, formula-derived runtime fuel, performance/backfill
and final/full gates remain incomplete. Held VA1-Q2/producer TypeExamples repair
is untouched. No goal reset/completion or publication.


## Closed compound-field pipeline integration (2026-11-02)

After sealed27b3e854, DecisionCompoundExtension lazily composes the actual closed
nonliteral-UInt fresh-field Answer after every original/reversed struct Answer.
The exact existing Answer and state transformer are preserved on success.
Decision uses the combined helper in both decideStruct and memCovered; old
decideStruct_complete/complete_merged signatures remain and a combined lemma is
added. Fresh-array cut-first and given-heap routes are unchanged.
DecisionCompoundCoverage derives preparation/hoist/cut, no-given overlap,
all-waiver target, Covered and actual global returned refutation from each closed
source witness. No supplied coverage/verdict/route premise; holdsH refutation
uses unchanged hash-free completeness and soundness. Generic returned-state
certificates are existential, not equality to a separately chosen counterstate.

Original buried0+1, another2+3 and partial0-1 improve from unknown to certified
refuted. The assigned Memory tuple becomes three refuted results; all controls
have matching kernel certificates. Exact constructed producer-state equalities,
optional some1/some5/none, ordinary/hash countermodels and target pins remain.
Mapping/computed-key unknowns, given-heap proved results, prior reversed exact
returned state and existing negative candidate states remain unchanged. The
517-node uncovered-but-proved control is retained. Four direct frozen
declarations Covered/inTarget/Waivers/DecisionTheorem match the exact base;
memCovered behavior intentionally expands through the helper. No producer,
semantic observation, hash/validity premise, dependency or proof budget changes.
Two root imports/two module-map rows are narrow additive registrations.

Raw commands/source hashes in /workspace/va1-evidence/compound-integration-next.
Final ten per-file MCP checks pass: helper4.313, Decision34.051, certificate4.163,
coverage4.242, reversed coverage4.263, Memory71.147, census5.284, compound reason
5.246, compound controls4.339 and reversed controls5.283 seconds. Repaired
affected build passes391jobs in1038.366s; every module retains the300s guard.
All edited Lean files are explicitly emitted before the public54-declaration
axiom/type audit46.881s and actual verdict profile3.109s, both passing. Axiom
sets contain only existing propext/Classical.choice/Quot.sound subsets. Profile
(target,Covered,tag): compound three=(true,true,refuted); literal/reversed same;
given=(true,true,proved); mapping/computed=(true,false,unknown); existing negative/
alias=(true,false,refuted). Verdict evaluation including printing ranges
0.304–3.545ms. These are interpreted local observations and kernel certificates,
not EVM tests or full import-closure completion.

Original writer lock, pinned Lean4.24.0/Lake5.0.0-src+797c613, threads1/Lean-j1,
one job/container with actual memory.max12884901888 and swap.max0 plus12GiB host
reserve are retained. Initial affected build was intentionally stopped after
confirmed stale comments: Docker137,86.821s, resource_stop=false; exact stop and
raw failure remain. Comments were corrected before repaired build; no unchanged
failed build was repeated. Final sampled aggregate RSS5316616KiB, cgroup peak4431269888bytes and minimum
host available13346336768bytes are recorded in resources.json, retaining22
unsuccessful measurement samples. No runtime/full-gate pass follows merely from these subset gates.

Reachability1111/layers180core/strict automatic491/61budgets/11refuted/trust1126
sources/248sites and whitespace pass. Same85 doc findings (48 missing/37
ambiguous) and404 inventory differences remain FAIL, retained against frozen
base analysis. Earlier full-run/TypeExamples resource failures remain failures;
VA1-Q2 is held and its source is untouched. Independent read-only finder/skeptic
source reviews are recorded in this evidence directory; committed export/package
review remains pending until the immutable export exists. Neither reviewer runs
Lean/server/builds or edits. Their two confirmed
stale-comment findings were corrected before final checks.

Global meaningful Residue union, DecisionTheorem-prime/exhaustive target/hash
bridge, keyed/field/struct/nested arrays, wider memory, halting OR, broader revised
program-free M4 boundary, formula-derived runtime fuel, remaining performance/
backfill and full gates remain incomplete. Existing standalone fixed-array,
numeric and source-work components remain delivered. Ready owned work includes
actual keyed-array syntax/coverage and exact formula-normalizer work; VA2 sharing
is not a prerequisite to those. No whole-goal completion/reset or publication.


## Exact formula-work normalization component (2026-11-02)

After sealed4b8bf63f, owned DecisionNumericNormalization defines intrinsic
Fml.normalizationWork with generalized Fml.casesOn/structural recursion: truth/
equality1, not/positive prefix add1, conjunction/implication add both child work
plus1. Other constructors receive a fallback number without any success theorem.
The exact real private normalizer view already linked to ProgramNormalization
now has a proved shared-state invariant: for all C/Γ/φ.QFUIntLinear and fuel/
budget each at least φ.normalizationWork, an actual reduction d and remainder
rest satisfy actualNormalization fuel φ budget=some(d,rest) and
rest+φ.normalizationWork=budget. Aggregate work is a sufficient depth bound,
not a separately computed minimal height. Both children consume visits before
smart truth collapse; term arithmetic does not consume extra formula visits.

Public qfUIntLinear_normalization_by_work accepts only syntax evidence and a
source-work budget inequality. qfUIntLinear_normalization_at_work removes that
inequality by choosing actual computed work. qfUIntPrefix_normalization_by_work
constructs a real equivalent DeclarationReduction for one positive uint binder
at body-work+1. No supplied output/certificate/normalizer premise, new axiom,
model change or trust shortcut. This certifies real normalization, not the later
source translation/cut/exhaustive decision theorem. Runtime2048 and511-node cut
remain unchanged; deriving the whole requested formula-dependent decision bound
is still open. Existing weight-based APIs/proofs stay unchanged.

Inhabited clients pin counts collapsed5/short3/positiveBody9/negativeBody11;
actual generic certificates for collapsed and both positive-prefix formulas;
5-versus4 truth-collapse consumption; arithmetic weight strictly above visits;
prefix10-versus9 and12-versus11 successes/refusals. Existing positive proved,
negative returned refutation and below-key unknown controls remain unchanged.
No new verdict/default/refusal/profile/pin changes. No imports/registrations or
producer files change in this checkpoint; four frozen direct definitions and
exact hash premises remain intact.

Raw evidence /workspace/va1-evidence/normalizer-work-next. Final current-tree
core MCP12.801s, client MCP7.413s, explicitly emitted affected client/build6.305s
and public11-declaration type/axiom audit9.507s pass. All edited files are emitted
before audit. Existing standard axiom subsets only. Initial recursor positivity
proof used looping simp and failed11.659s; explicit definitional constructor
proofs fix it without budget changes. Initial client all-conjunction decide
failed6.397s because equality of optional proof certificates has no Decidable
instance; exact definitional equalities fix it. Both failure sources and raw
outputs are retained. Neither failed attempt counts as pass.

Same original writer lock, pinned Lean4.24.0/Lake5.0.0-src+797c613, threads1/
Lean-j1, one bounded job and actual memory.max12884901888/swap.max0 plus12GiB
host reserve. Final measured aggregate RSS2245356KiB, cgroup peak1289093120bytes,
minimum host available16426991616bytes;9 failed measurement samples retained.
Strict automatic/layers/trust/reachability/whitespace pass; broad docs85 and
inventory404 differences remain FAIL against frozen base. Existing full-gate/
TypeExamples resource failures remain failures and VA1-Q2 remains held.

Independent read-only finder/skeptic reviews verify real shared-state accounting,
both-branch collapse controls and unchanged later budgets. Skeptic identified
ordinary indexed pattern matching; generalized recursor fixes G0 before final
checks. No final source findings. Reviewers run no Lean/server/build or edits.
Committed package review/export seal remains pending until actual export.

All original global Residue/DecisionTheorem-prime/target/hash completeness,
keyed/field/struct/nested arrays, broader memory, halting OR, broader revised M4
boundary, full formula-derived runtime fuel, remaining performance/backfill and
final/full gates remain open. This independent fuel component does not consume
VA2 sharing ownership or TypeExamples repair. Prior seals/failures and original
goal identity are preserved; no push/merge/tag or whole-goal completion.


## Necessary and sufficient normalizer work (2026-11-02)

After sealede645f435, owned DecisionNumericNormalization strengthens the real
normalizer proof without altering any existing function or sufficient theorem.
For every C/Γ/φ.QFUIntLinear/fuel/budget/d/rest, successful actualNormalization
fuel φ budget=some(d,rest) implies rest+φ.normalizationWork=budget, without
sufficient-budget hypotheses. Success inversion recovers both actual child
computations and their real intermediate remainder. Zero fuel/budget contradict
success. This preserves truth-collapse order and arbitrary partial UInt terms.

Public qfUIntLinear_normalization_iff_work proves, for all such φ and budget,
(ProgramNormalization.ofFormula? budget φ).isSome=true iff
φ.normalizationWork≤budget. Public qfUIntLinear_normalization_below_work derives
actual none for every smaller budget. This is exact minimum shared public budget
(the same number initializes fuel and shared nodes), not minimum independent
depth. Original state-bound proof, source-derived sufficiency/prefix, runtime2048
and later511-node cut remain unchanged. This is not an exhaustive decision-fuel
implementation or a Residue/coverage theorem. No supplied output/coverage/verdict
premise, oracle, new axiom, weakened observation or increased budget.

Clients characterize all budgets, including surplus values: collapsed truth
branches succeed iff5≤budget; numeric positive/negative bodies iff9/11≤budget.
Generic below-work refusal produces the concrete4-node branching failure.
Existing computed source counts, exact/+1 prefix boundaries and original
proved/refuted/below-key unknown controls remain unchanged. No imports, producer
files, registrations or expected verdicts change. Decision/HashPremise/
ProgramReduction and held TypeExamples remain byte-identical to prior checkpoint.

Raw evidence /workspace/va1-evidence/normalizer-minimum-next. Final core MCP
12.799s, core emit9.631s, client MCP7.468s, affected client emit6.283s, public
8-declaration type/axiom audit9.519s pass. Only existing standard axiom subsets.
The first induction mistakenly fixed rest (11.790sFAIL); generalization was
correct but argument order then failed11.654s. A per-file goal query inspected
the real induction signature, and final repair passes. Both failed sources/
raw outputs and inspected goal remain; none is a passing gate. Final source/client
MCPs report success with no items/failed dependencies.

Original lock, pinned Lean4.24.0/Lake5.0.0-src+797c613, serial threads1/Lean-j1,
actual memory.max12884901888/swap.max0 and12GiB host reserve retained. Measured
aggregate RSS2170740KiB, cgroup peak1312038912bytes, host available minimum
16416120832bytes;9 unsuccessful resource measurements retained. Static strict
automatic/layers/reachability/trust/whitespace pass. Broad docs85/inventory404
findings remain FAIL and earlier fullgate/TypeExamples stops remain failures.
No unchanged stopped full build repeated. No EVM evidence is claimed.

Independent read-only finder/skeptic source reviews report no findings; both
verify actual successful-child accounting and exact shared-budget scope. Neither
uses Lean/server/builds/edits. Final docs/export reviews and immutable committed
package seal remain pending until performed. Original full goal remains partial:
global meaningful Residue/DecisionTheorem-prime/target/hash bridge, keyed/field/
struct/nested arrays, broader memory, halting OR, revised broader program-free M4
boundary, whole-pipeline formula-derived fuel/511 bound, remaining performance/
backfill/final full gates and held VA1-Q2 are open. Prior seals/approvals/failures
preserved; no goal reset/completion, scope takeover or publication.


## Actual typed-prefix storage observations (2026-11-02)

After sealede757deb2, actual array-gap staging in array-key-next distinguishes
concrete blockers before repair. Fixed root/bad controls collect3 reads, pass
Src/lifting/flattening with235/223 nodes. Fixed-below-key, dynamic-below-key and
below-field pass prefix/free-parameter coverage, bounded preparation and cut,
but collect0 reads and fail arithmetic Src/flattening (57/61/47 nodes); lifting
still succeeds. Arrays of structs/arrays stop earlier at leafOf?. Thus the
root-only ElemPath restriction is not evidence that the whole cut returns none.
No source-family gap cause is conflated or expected verdict changed.

Owned DecisionFixedArrayStorage now connects existing SVal fixedFloorAtPath to
actual Storage.set at an arbitrary intrinsically typed root/prefix. Absence
remains none. For all contracts/root types/fixed lengths/continuation types,
success plus the unchanged length-breakpoint premise transports full optional
find, real Storage.obs.word and Storage.obs.has to floored indices, including
undefined/out-of-range observations. Diverging same-root paths retain lookup;
other roots retain complete values. No successful-prefix/save premise is
assumed beyond the actual optional result; existing presence supplies existence.
This is the previously missing real-storage observation layer, not another
vector/path proof or a collector/coverage implementation.

Inhabited clients use actual mapping and nested-fixed storage roots. Selected
row value9 becomes7; non-default sibling key stays9 and another-root sentinel
stays42. Presence distinguishes in-range2 from out-of-range3. An absent nested
outer prefix refuses reconstruction, without installing a default. Omitting
the length breakpoint gives an actual false presence-transport control.
No default/observation/predicate/decision/classifier changes. Two imports/two
module-map rows are narrow additive registrations. Producer files and all five
array unknown pins remain unchanged.

Raw /workspace/va1-evidence/array-key-next. Detailed stage replay4.172s, final
core MCP5.264s, client MCP4.161s, explicit affected emit3.154s and14 public
type/axiom declarations4.197s all pass. Initial stage harness mistakenly used
--run without main: exit1/3.148s retained with source; corrected invocation
adds detailed observations and passes. It is not a failed theorem or a passing
gate. No proof failures or proof-budget increases in this component. Only
existing standard axiom subsets. Original lock, Lean4.24.0/Lake5.0.0-src+797c613,
threads1/Lean-j1, hard memory.max12884901888/swap.max0 plus12GiB host reserve
remain enforced. Sampled aggregate RSS1387204KiB, cgroup peak526958592bytes,
minimum host available17157500928bytes;9 failed measurements retained.

Reachability1113/layers180core/strict automatic491/61budgets/11refuted/trust1128
sources/248sites and whitespace pass. Same broad85 docs/404 inventory findings
remain FAIL against frozen-base analysis; old full/TypeExamples resource failures
remain failures. No EVM or full combined-tree evidence claimed. Independent
read-only finder/skeptic source reviews find no issues; neither uses Lean/server/
builds or edits. Final documentation/export review and committed seal remain
pending until performed.

Global meaningful Residue/DecisionTheorem-prime/target/hash bridge, general
keyed/field/struct/nested array collector/coverage and reconstruction composition,
wider memory, halting OR, broader revised M4 boundary, whole-pipeline fuel/511
bound, remaining performance/backfill/full gates and held VA1-Q2 remain open.
No other lane scope taken; prior seals/goal identity/failures preserved.


## Decidable map-guard reversed-field reason (2026-11-02)

After sealed820d41b5, owned DecisionMappingFieldReason adds a separately named
MappingReversedFreshField source family: all C/Γ, exact fresh-struct binder,
actual primitive-field lookup, direct literal on the left/field on the right,
complete intrinsic source equality, and (Ty.ref(struct s)).mapFree=false.
“Mapping-bearing” names this actual syntactic guard; no separate equivalence
with a semantic contains-mapping predicate is claimed. The one-line reason is
that the existing fresh-struct realization requires a map-free struct whereas
this source fails that structural guard. No new target exclusion is introduced.

Recognition uses actual allocView/eqView/literalTerm, field enumeration and full
Tm.beqR comparisons. Public soundness/completeness/iff and constructive Decidable
prove exact membership without querying target/Covered/decideGoal. Generic
hashFree and schema_refuses prove only actual boundAnswer refusal for every
body of that binder, not all-route/global unknown. Separate high
DecisionMappingFieldBoundary proves target admission for every existing waiver
setting and every closed member. No child-heap realization, countermodel,
coverage or future theorem is assumed; the map-free children premise is
unavailable here and remains a substantive proof obligation.

Actual original mappingReversed0 and new mappingOne1 both inhabit the class,
are hash-free/admitted, and remain globally unknown by kernel computation.
Supported map-free original/five/Bool reversals, map-bearing reflexive, compound
RHS and given-heap shapes are negative controls. Constructive proposition
decisions also have inhabited positive/negative controls. Existing verdicts,
source definitions, frozen predicates/premises/budgets remain unchanged. Three
root imports/three map rows are narrow additive registrations.

Raw /workspace/va1-evidence/mapping-reason-next. Final core MCP5.260s, boundary
MCP4.175s, client MCP4.241s, explicit affected emission3.106s and15 public
type/axiom reports5.244s pass; only existing standard axiom subsets. Initial
client MCP4.218s failed because a Gaps formula was mixed into a StandardExample
list. The same given-heap input is now a separate conjunct, preserving intrinsic
contract typing and every expectation. Failed source/output retained; review
alone was not claimed to establish elaboration. No budget increase or coercion.

Same original writer lock, pinned Lean4.24.0/Lake5.0.0-src+797c613, threads1/
Lean-j1, hard memory.max12884901888/swap.max0 and12GiB host reserve. Sampled
aggregate RSS1533308KiB, cgroup peak612241408bytes, minimum host available
17164214272bytes;9 unsuccessful measurements retained. Required static gates
pass except unchanged broad85 documentation/404 inventory findings, retained
against frozen-base analysis. Earlier full/TypeExamples resource stops remain
failures; VA1-Q2 remains held and its source untouched. Kernel/Lean evidence
only, no EVM claim.

Independent read-only finder/skeptic source reviews report no findings after
the intrinsic-contract control repair. They verify exact family/premises and
specific-schema versus global-verdict distinction; neither uses Lean/server/
builds/edits. Final docs/export review and committed package seal remain pending
until performed. Global Residue union/exhaustive target/hash bridge and
DecisionTheorem-prime remain open, as do general array collector/coverage, wider
memory, halting OR, broader revised M4 boundary, whole-pipeline fuel/511 bound,
remaining performance/backfill and final full gates. Goal/VM/branch and prior
seals/failures preserved; no push/merge/PR/tag or whole-goal completion.
