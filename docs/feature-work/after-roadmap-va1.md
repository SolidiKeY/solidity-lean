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
  countermodel controls are partial progress, not a theorem substitute.
- AU01 performance: hash/main splits and unchanged DecisionArrays replay checks
  pass below 300 s. Further interpreted profiling, requested array split and
  final import/full gates remain open; no milestone eligibility claimed.
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
