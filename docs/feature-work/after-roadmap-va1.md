# VA1 decision lane: setup and open work

Status: **blocked on VA1-Q1**, 2026-10-31. Base `8bd8742ad987d566f7ba7624372cec1c020be07c`,
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

`Decision.lean` already separates non-hash `Covered` completeness from
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
