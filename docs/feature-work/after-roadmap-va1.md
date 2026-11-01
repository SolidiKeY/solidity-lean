# VA1 decision lane: setup and open work

Status: **partial; VA1-Q1 pending; independent AU01 work active**, 2026-11-01. Base `8bd8742ad987d566f7ba7624372cec1c020be07c`,
branch `codex/solidity-automation-20261031/va1-decision`, checkout
`/workspace/solidity-lean`. Exact AQ1/AQ2 receipt is recorded in
[solidity-scope.md](../solidity-scope.md), checkpoint
`717069361a21755914e78caf13d1df2ca76a0284`. No implementation claim.

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
- AU01 performance: interpreted profiling and coherent sub-300s module splits pending.
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
