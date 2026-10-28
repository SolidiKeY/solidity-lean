# Two-anchor KeY-int test point

The original `gapKIntTwoAnchors` statement is now kernel-certified `.proved`
through `decideKEnc`, `decideLeaf` and `decideGoal`. The assignment remains **validation-blocked**: the full library passed, but
the mandatory TestSuite run stopped at the unchanged independent loop module
`Derived17` under the original memory/headroom guard. Closure of this
one witness is not `DecisionTheorem` or general Presburger completeness.

## Scope and proof

For an outer KeY-int local `z` and integer literal `k`,
`∀ y : Int. y > z → y > k` is exactly `z >= k`. If `z < k`, the point
`y = k` refutes the implication; otherwise transitivity proves it.
The new module `Solidity/Calculus/KIntTwoAnchors.lean` proves this equivalence
at every typed state, under either hidden-binder modality. Private intrinsic
formula views use `Fml.casesOn` with generalized context/formula motives;
shallow term inspections and certified `Tm.beqR` truth checks retain the
exact shape witness. No syntax, term, state or witness representation changes.
Existing `gt`/`ge` and integer-literal printers remain applicable.

`Fml.kencBind` tries the existing direct/anchor encoding first, preserving
all previous successful outputs, then uses this exact test point. The
existing `holds_kenc`, coverage, soundness and countermodel lifting apply.
The remaining outer integer is handled by the existing bounded two-word
encoding with its unchanged side conditions and limits. No ledger cut,
`QArith`, target predicate, waiver, exclusion, profile decision or general
`DecisionTheorem` checkpoint changes.

## Baseline and observations

Checkout `/workspace/solidity-lean`, origin
`https://github.com/SolidiKeY/solidity-lean.git`, branch
`codex/next10-kint-two-anchors`, published base and fetched `origin/master`
`f4dee4a29c2e208b36db4a4161a4723c735cd775`; ancestry confirmed. Lean 4.24.0,
Lake 5.0.0-src+797c613. Activation was required for PATH; no project drift.
Setup and user files were preserved.

| Fixture/observation | Before | After, kernel evidence |
|---|---|---|
| Original gap statement and `inTarget` certificate | retained; true | retained; true |
| Original gap coverage | false | `kencCovered` and `Covered` true |
| Original `decideLeaf`/`decideGoal` | exactly unknown, reproduced by `rfl` | exactly proved |
| Original `decideKEnc` | not separately pinned | exactly proved |
| Positive control, threshold -3, both modalities | new control | covered and proved, including `z = k` |
| Negative universal control, threshold -3, both modalities | new control | covered and certified refuted; `z = -4`, `y = -3` |
| Negative-polarity true universal antecedent | new control | in target, encoded and covered; KEnc/Leaf/Goal refuted with the same typed countermodel |
| Deep outer integer behind a bool local | new control | recognized position 1 and threshold -3 |
| Boolean false observation / different lhs local | new controls | view refuses |
| Unbounded symbolic multiplication | existing refusal boundary | outside target, not encoded, exact unknown |
| Earlier example pins | existing kernel coverage/target pins | retained and checked in the same module |

The explicit countermodel works at every typed starting state. For the
original gap it gives `z = -1`, `y = 0`, falsifying its hypothesis. Exact
verdict equalities use existing coverage and semantic theorems; they are
kernel-checked certificates of the computable functions, not a claim about
interpreted automaton timing. No solc/compiler/EVM execution or new native
Solidity coverage is claimed for these pure KeY-int logic fixtures.

## Validation evidence

Raw logs, baseline certificate source, resource measurements and reproducible
bounded-check helpers are in `/workspace/next10-kint-evidence`.

| Command/check | Exit and measurement |
|---|---|
| `lake build Solidity.KeySort` | 0; raw `runtime-gate.log`, 2 jobs, 24,875,008-byte cgroup peak; output retained before `RUNTIME_GATE_PASS` |
| Unchanged `lake build Solidity.Examples.DecisionKInt` | 0; 310 jobs; about 3263s from process start to final artifact; 10,358,276,096-byte cgroup peak; terminal tail and timing metadata in `baseline-build.json` |
| Baseline exact unknown/false coverage certificate | 0; `baseline-pin.log`, 8s, 203,673,600-byte cgroup peak |
| New core per-file MCP, recursor version | 0; `core-g0-final-diagnostics.log`, complete/no warnings, 4s, 596,922,368-byte cgroup peak |
| Binder per-file MCP and unchanged axiom guard | 0; `binder-final-diagnostics.log`, 24s, 1,400,410,112-byte cgroup peak; repaired core subsequently rebuilt in 1.8s, binder in 21s |
| Fixture per-file MCP, full errors/warnings/audits | 0; `fixture-final-diagnostics.log`, 18s; sampled aggregate RSS 3,042,582,528 bytes; cgroup peak 1,752,281,088 bytes |
| Clean dependency confirmation | 0; `fixture-dependencies-confirmed.log`, cached 310 jobs |
| Static/trust/inventory gates | 0; `static-gates-confirmed.log`, 5s, sampled RSS 204,070,912 bytes, cgroup peak 178,487,296 bytes; 701 reachable/0 orphaned, 153 core/0 elaborator paths, 491 automatic + 61 step-budget proofs, 11 refuted, 0 manual/pending; trust 715 sources/0 findings; inventory 212 features/783 symbols, generated contents unchanged |
| `./run-lean.sh` | **75, resource stop**; `full-run.log`, 5833s; library 686 jobs passed, DecisionKInt 16s; sampled aggregate RSS 10,825,768,960 bytes, cgroup peak 12,369,313,792 bytes, minimum working headroom 2,141,204,480 bytes; no OOM/max events |
| Isolated `lake build Solidity.TestSuite.Derived17` | **75, same headroom stop**; `isolated-derived17.log`, 81s, RSS 10,736,132,096 bytes, cgroup peak 10,093,232,128 bytes; no OOM/max events; no further repeat |
| Final `lake build` | 0; `final-library.log`, 686 jobs, 1.61s cached confirmation, RSS 1,597,431,808 bytes, cgroup peak 216,621,056 bytes |
| Strict timing audits of cold/full and final library logs | 0; `final-gates.log`; 18 completed TestSuite modules timed below unchanged 300s limit; cached library log has zero TestSuite timings. **Not complete timing coverage** of the stopped suite |
| Final fixture/root MCP diagnostics | 0; `fixture-negative-final.log`, complete/no warnings, 40.53s; RSS 3,272,507,392 bytes, cgroup peak 1,988,124,672 bytes |
| `lean_verify`, source scan enabled, headline equivalence/original goal/negative control | 0; `headline-verify.log`, 28.62s; each has only the standard three axioms and no warnings; RSS 5,780,475,904 bytes, cgroup peak 3,206,766,592 bytes |
| Final static/trust/inventory and frozen SolKey checks | 0; `final-gates.log`, 5.44s, RSS 210,853,888 bytes, cgroup peak 391,499,776 bytes; counts unchanged; 377 taclets parsed, 131 read-bearing annotations matched |
| Six-gap preservation / changed paths | 0; `preserve-gaps.py` in static gate confirms all six complete definitions and target certificates, original helpers and policy source unchanged; changed paths/links checked |
| Root module MCP | 0; complete and empty diagnostics in `fixture-negative-final.log` |
| Final read-only fixture/control reviews | no confirmed remaining code findings; finder and skeptic used no Lean server or writes; final evidence/replay cleanup independently reviewed by both, no confirmed findings |

All proof audits printed for the arithmetic lemma, state equivalence, shape
transport, positive validity, explicit countermodel, all three exact gap
verdicts and both negative verdict certificates contain only
`[propext, Classical.choice, Quot.sound]`. The pre-existing `holds_kenc`
axiom guard is unchanged and passes. No new axioms, `sorry`, unsafe proof
shortcuts or increased heartbeat/fuel/node/test limits are used.

Heavy checks are serialized by
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`, with
`LEAN_NUM_THREADS=1` and explicit `-j1`. Systemd user scopes were unavailable;
Docker cgroup v2 readings verified `memory.max=12884901888` and
`memory.swap.max=0`, beneath the own VM's 16 GiB parent. Later checks also
sample aggregate RSS every 0.2s and stop only their own group if available
working-memory headroom falls below 2 GiB. Cgroup peaks include charged
cache; sampled aggregate RSS is reported separately. Caches remain on disk.
The alternate Lake file changes threading only and is not part of the patch.
The shared local machine's 12 GiB reserve is not applied to this VM.

Failed proof probes remain in the logs and are not counted as passing.
The first Lake command rejected unsupported `lake build -j1`; this was
repaired with per-target weak Lean arguments. A dependency rebuild was
intentionally cancelled only in its verified own cgroup to fix G0 (exit
137, not an OOM pass). The repaired build completed internally in 1029s,
with a 6,086,103,040-byte cgroup peak, but editing its external wrapper
while active caused a trailing shell error (outer exit 2). The wrapper
was repaired, kept immutable during checks, and the cached confirmation
exited 0. The initial static runner also exposed a missing Node PATH entry inside Docker and the canonical non-executable mode of `check-trust.sh`; the installed Node runtime was added to the runner PATH and the unchanged trust script is invoked through Bash. The repaired complete static gate exits 0. The pinned MCP package emits a known transport cleanup warning
after returning complete diagnostics; diagnostics success, completeness,
exit codes and resource stops are checked explicitly.

## Review and remaining limits

Independent read-only finder and skeptic reviews used no Lean server.
They confirmed exact shape/position/truth checks, total thresholds, both
modalities, old branch priority, nonlinear refusal and local acyclic imports.
The finder identified the missing mirrored core list entry; it was fixed.
The skeptic identified the indexed formula match under G0; both formula
inspections were replaced with generalized `Fml.casesOn` views, and the
skeptic confirmed resolution. Both independently reviewed the final fixture and
negative-polarity control with no confirmed defect. The latter exercises the
new fallback rather than an already supported positive universal path.

The finder investigated the resource stop without running Lean: `Derived17`
has no transitive import of `KIntEncode` or `KIntTwoAnchors`, and its setup
JSON contains neither. Its source is byte-identical to the base and has ten
existing loop obligations. History and `feature-work/integration.md` already
record its high memory cost. A distinct isolated same-limit experiment also
stopped, so the blocker is retained. No loop-proof or checking-cost refactor
was attempted: that belongs to a prohibited previous-batch area. Remaining
mandatory work is a bounded full/TestSuite pass and complete timing coverage;
this patch does **not** claim assignment completion. Existing linter warnings
from unrelated modules remain in the full build log.

Evidence replay uses `prepare-config.py` to recreate the exact threading-only
alternate Lake file under the writer lock; it refuses to overwrite differing
content and can remove only its matching file. The retained config and
`REPLAY.md` keep evidence helpers reproducible after checkout cleanup. Both
reviewers checked the final evidence records and replay helpers with no
confirmed findings; config regeneration and bounded KeySort replay passed.

Other two-anchor linear shapes still require further reduction. All six
original gap definitions and target certificates remain; the other five
original gaps remain open. No Residue policy or D1/D2 decision was taken.
This task does not claim full decision completeness or source/compiler
semantic equivalence.

Shared edits: the narrow `KIntEncode` import/fallback/proof/docstring,
`Examples/DecisionKInt` controls/certificates, root module registration,
core-layer registration and its mirrored prose, module-map entries,
automation status, this handoff and the Lean-only rule-map entry.
The new arithmetic implementation lives in its own additive module.
No changes were pushed or merged.

## Investigated continuation: declaration serialization

Run `b4b6f3b8-ee8a-4ec4-b964-c2cbb819f21a` resumed the same saved executor,
clean checkout, branch and `a030ca2ce909f711986b07f49eba77d51bea855b` commit.
Actual Lean/Lake and local Docker commands verified usability; no replacement
or unrelated task evidence/code was used. The prior invocation had `-j1` but
no `-DElab.async=false`. A distinct runtime-only experiment added that weak
argument to the evidence-local Lake configuration and set artifact-cache
restoration off. Tracked `lakefile.toml` and all source/proof files stayed
unchanged. Derived17's source SHA256 before/after and at published base is
`5ddbd7922a3d418fde5e46ae6ff48951e03c55eb4f6482e5701b9b840e592c54`.

The forcing script moved only the pre-existing Derived17 setup artifact (no
compiled artifact existed), and actual live process evidence records
`lean --tstack=131072 -j1 -DElab.async=false .../Derived17.lean ... --json`.
This was a fresh execution, not cache replay. A 300-second timeout retained the
existing timing budget. The same writer lock, one Lean thread, disk caches,
`memory.max=12884901888`, `memory.swap.max=0` and 2 GiB working-headroom guard
remained in force under the outer VM's 16 GiB cgroup.

**The distinct experiment failed:** exit 75 at 88.743279438 seconds, sampled
aggregate RSS 10,664,943,616 bytes, cgroup peak 9,998,143,488 bytes and minimum
outer-VM working headroom 2,112,159,744 bytes. No max/OOM event occurred.
`continuation-serial-derived17.log` and its memory JSON retain the stop;
`continuation-b4b6f3b8/actual-derived17-process.txt` retains the live invocation.
Both earlier resource stops remain visible. No unchanged retry or subsequent
full run was attempted. Full/TestSuite and complete strict timing coverage
remain mandatory open gates; this is **not assignment completion**.

Unaffected checks were rerun in this executor:

| Check | Actual result |
|---|---|
| Owning core, binder, fixture and root MCP diagnostics; three headline `lean_verify` audits | 0; `continuation-focused-axioms.log`, 72.95s; all complete, no errors; only pre-existing binder unused `Int.add_mul` simp warning; audits standard three/no warnings; RSS 5,776,769,024 bytes, cgroup peak 3,236,925,440 bytes, minimum working headroom 8,873,213,952 bytes |
| `lake build Solidity.KeySort Solidity.Examples.DecisionKInt` | 0; `continuation-fixture-build.log`, 311 jobs cached replay, 0.403s; RSS 73,846,784 bytes, cgroup peak 43,892,736 bytes |
| Orphans/layers/strict automation/trust/inventory and frozen SolKey | 0; `continuation-policy-gates.log`, 5.84s; unchanged counts, six gap/target definitions preserved, 377 taclets/131 annotations; RSS 372,637,696 bytes, cgroup peak 399,704,064 bytes |
| Strict timing audit | existing 18 completed TestSuite timings pass unchanged 300s limit; stopped Derived17 has no successful timing; complete suite coverage remains open |

The positive, negative and nonlinear controls and their exact kernel verdict
certificates are unchanged. No callback/invariant semantics, ordered observation,
expected result, policy, heartbeat/fuel/node/test budget or axiom changed.
Conditional/theorem-based exact decision certificates are not a fresh concrete
native decision run; no Solidity compiler/EVM observation was added.
Evidence-local configuration/replay details are in
`/workspace/next10-kint-evidence/continuation-b4b6f3b8/README.md`.
Independent finder and skeptic read-only continuation reviews found no
confirmed defects. Neither used Lean/server/builds or wrote files; they checked
the actual invocation, source hashes, limits, renewed checks, replay safety and
blocked-gate claims. Their records are retained in the evidence bundle.
