# VA2 AU03/AU04 handoff

Status: runtime recovered; AU03 warning, typed joined walks, notation/chains, bounded multi-base closer and original Boolean mapping-key kernel closure checked. The forced signed sequential fixture still fails; isolated post-anon measurement, AU04 sharing/loop repair and full assignment gates remain incomplete.

Repository: `/workspace/va2-sharing`. Branch:
`codex/solidity-automation-20261031/va2-sharing`. Exact base:
`8bd8742ad987d566f7ba7624372cec1c020be07c`.

## Setup checkpoint

Fetched `origin master` and the exact base from the configured GitHub remote.
`origin/master` equals the base; merge-base ancestry passed. Preserved the
older clean `/workspace/solidity-lean` checkout at `9b24b57311b8daf0d4cd01b52bf420fd024c1d3a`
on `work`, creating this isolated worktree instead. Recorded exact AQ1/AQ2
human answers in `docs/solidity-scope.md` before implementation. No Lean
source edits. `git diff --check` passed.

Independent read-only finder `/root/setup_finder` and skeptic
`/root/setup_skeptic` both found no issues with branch/base/ancestry or exact
approval receipt; neither used the Lean server. Evidence:
`/workspace/va2-sharing-artifacts/evidence/reviews.md`.

## Runtime blocker

Actual tools: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613
(Lean 4.24.0). Cgroup memory.max is 17179869184 (16 GiB), swap.max is
`max`; OS reports no swap. Required 12 GiB/no-swap process-group bound
is not available: cgroupfs is mounted read-only, user systemd has no bus,
system systemd is not PID 1, and sudo is absent. Per-process address-space
limits do not establish an aggregate process-group limit. No heavy job,
LSP session or build was started. No aggregate build RSS measurement exists.
KeySort and RUNTIME_GATE_PASS remain pending. Raw command outcomes:
`/workspace/va2-sharing-artifacts/evidence/setup.json`.

Unblocking requires an executor with a delegated writable cgroup or an
already-enforced 12 GiB/no-swap scope. No theorem, budget or resource
requirement has been weakened. No automatic approval rejection occurred.

## Full queue accounting

All implementation remains pending: baseline PolySize, doubling family,
joined mapping-key failure, loop leaf past anon and speed-history audit;
AU03 located warning and controls; dependent-assignment joins and general
soundness/size proofs; conditional notation/printer roundtrip and restored
chain rows/ifTrace; Boolean-key kernel split; two-base/beyond-splitMax
joined values; AU04 fresh intrinsic call-result locals with freshness,
evaluation and validity transport; loop repeated-leaf repair and controls.

All backfill remains pending: notation/printer/chain controls;
Int.negSucc affine controls; SplitTo Solidity docstrings; proof_size
relocation/pins; certifyLong context discovery; warning/sharing/loop
fixtures. Integrated narrower gap-worker deliveries still need auditing.
Return to dependencies after backfill; do not take VA1 Decision/Residue,
AU05/AU06 or compiler files.

All required proof/validation gates remain pending: per-file diagnostics,
affected closure, full bounded ./run-lean.sh, strict automatic gate,
trust/axiom audits, docs-versus-exact-base comparison, measurements of walk
and leaf growth/time/RSS, and independent finder/skeptic reviews for each
implementation milestone. Setup reviews do not cover those milestones.
No new theorem premises or external-test correctness claims exist.

Artifacts will include a cumulative patch and Git bundle, this handoff,
evidence archive and SHA256 manifest under `/workspace/va2-sharing-artifacts`.
No push, merge, PR or tags were performed. The assignment is incomplete.

## Investigated runtime recovery (2026-10-31)

The earlier cgroupfs/systemd failure evidence remains intact. No unchanged
cgroupfs/systemd probe was retried. Consulted the supported
`cloud-environment-runtime` skill and its `references/docker.md`.
The same attached VM has the platform-managed Docker 28.4.0 daemon at
`unix:///var/run/docker.sock`; no daemon was installed, started or restarted.
Explicit local endpoint selection cleared Docker endpoint/context/TLS
selectors only, as required by the skill. No policy, authentication,
privilege, catalog or VM changes were made. Podman/nerdctl are absent.

A task-owned child container using pinned image
`debian@sha256:f6b08b09a05725f9431502d3b5714f5c4576e82c1a84fa1debe0c24a7e0c3ec4`
mounted the exact existing `/workspace` tree, including the isolated checkout
and existing toolchain. It ran as UID/GID 1000 with `--network=none`,
`--memory=12g --memory-swap=12g`. Actual child cgroup values were
`memory.max=12884901888` and `memory.swap.max=0`. The daemon reports
MemoryLimit=true and SwapLimit=true. This is the aggregate hard limit;
the RSS sampler is measurement only. Containers were removed on exit.

Actual toolchain in that bounded container:
Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake 5.0.0-src+797c613 (Lean 4.24.0).
With `LEAN_NUM_THREADS=1`, the command
`lake env lean -j1 --tstack=131072 Solidity/KeySort.lean` passed.
The evidence script prints RUNTIME_GATE_PASS only after those cap checks,
version outputs and successful KeySort exit. Recorded wall time is 1 second
(coarse whole-second measurement), sampled aggregate process RSS peak
301932 KiB, and cgroup peak accounted memory 114503680 bytes. These are
different measurements; shared resident pages can be accounted outside this
child cgroup. Neither number is a walk/leaf growth benchmark.

An initial Lake build attempt failed with `permission denied` for `//.cache`
and emitted a Lean command without explicit -j1; it is retained as a failed
attempt and does not support the runtime gate. The passing explicit invocation
sets the existing writable `XDG_CACHE_HOME=/workspace/.setup/cache`.

Original checkpoint `29aec17e607a5dfc585a0e4a49990dc8e3f751c3` and every
original artifact were preserved; all original SHA256SUMS entries verified.
New evidence is separately stored under
`/workspace/va2-sharing-artifacts/runtime-recovery/`, with exact command arrays,
exit codes, raw logs and reproducible probe scripts. No implementation files
were edited; all work/backfill/proof/validation obligations listed above remain
open. The same existing blocked goal awaits coordinator reactivation based on
this evidence; no replacement goal or competing continuation was created.

Independent recovery finder `/root/setup_finder` accepted the runtime evidence
and requested a committed handoff with separately checksum-bound recovery
artifacts. This recovery checkpoint addresses that finding. Independent skeptic
`/root/setup_skeptic` accepted the KeySort runtime gate and flagged that RSS
sampling sums visible `/proc` processes without a separately recorded PID
isolation assertion; treat that RSS number as a visible-process sample, not an
independently certified process-group maximum. Both reviews were read-only,
without Lean server or gate reruns. Evidence: `runtime-recovery/reviews.md`.

## Supporting AU03 checkpoint: notation, measurements and controls

This checkpoint does not finish AU03 or AU04. It supplies the conditional
notation needed to state joined leaves, moves the measurement command out of
an example, and preserves regressions for the smaller M8 items. No rule,
strategy, observation, validity/hash premise, verdict pin, proof budget or
exclusion changed. The unconnected `Syntax/LoopWarnings.lean` working file is
not part of this checkpoint; its classification review is still being applied.

### Frozen-base measurements and source audit

Raw commands and exact archived fixtures are in
`/workspace/va2-sharing-artifacts/work/`. All Lean work runs in the same managed
Docker child, hard `memory.max=12884901888`, `memory.swap.max=0`, network none,
`LEAN_NUM_THREADS=1`, explicit `-j1`, writer lock held, no overlapping build/LSP.
The warm runner is `work/bounded.py`; it records command arrays and elapsed time,
visible-process RSS samples and cgroup memory peak. The RSS sample can count
shared pages more than once; it is a measurement, not the hard cap.

`baseline-cold.log` passed the focused cold build (234 jobs, 1552.67 s wall,
3,577,240 KiB sampled RSS, 4,228,907,008 bytes cgroup peak).
`baseline-measure-build.log` passed the archived baseline fixture (41.89 s,
1,264,396 KiB sampled RSS). Its walk and leaf sizes are separate:

| Family | k | Walk nodes | Leaves (term sizes) |
|---|---|---|---|
| F1 joined assignments | 1,2,3 | 8,13,18 | 25,41,57 |
| F2 invariant loop | 1 | 10 | 17,49,32 |
| F2 invariant loop | 2 | 17 | 17,49,44,78,59 |
| F3 loop with branches | 1 | 14 | 20,64,37 |
| Offset doubling calls | 1,2,3 | 5,5,5 | 20,20,20 |
| Non-offset `x*3+1` doubling calls | 1,2,3 | 5,5,5 | 26,34,50 |

F2's largest whole leaf after `sol_leaf` took 1.137 s (raw 14,886,087 heartbeats) at k=1,
3.129 s (raw 44,305,622) at k=2; F3 k=1 took 4.830 s (raw 64,045,537).
Usual displayed heartbeat units divide these raw counts by 1000.
`baseline-fuel.log` retains F3 k=2's default-budget failure. No budget increased.
`baseline-extras-tree.log` confirms literal loop bounds 2/4 still unroll to
proved exact results in the kernel strategy; the named proof-tree builder
stops at those `.auto` loops (5 nodes, 1 open leaf). Kernel step counts were
37/61. That named-tree limit must not be reported as kernel unrolling failure.
The actual retained Boolean-key mapping obligation reaches its joined mapping
leaf and still needs `sol_leaf; sol_close`. Multi-assignment branches split.
Two-base/beyond-limit closure and more baseline controls remain to be measured.

Speed history inspected before representation work: `fe105b52` (joins/closer
expansion), `3dbf353a` (strict-redex sharing), `c98bd4b2` (bounded kernel input),
and `00a88bb9` (factor folding). Preserve their whole-leaf/redex safeguards.
Integrated handoffs for kint anchors, quantified ledger, negative memory,
parameter/struct witnesses and written-memory hash were audited; their existing
deliveries are reused, with no edits to those worker modules or VA1 files.

### Implementation and proof boundaries

- `SurfaceNotation` reads conditional terms in both term equality and program
  expression equality through existing intrinsic `NTerm.ite`/ternary readers.
  Nested terms, printed-body rereading, invalid guard/branch types and lazy
  selected versus failing unselected branches have controls. This is not a new
  calculus rule. Broader signed printer/type-inference coverage remains open.
- `#proof_size` moved unchanged from PolySize to Tools/ProofTree, with positive
  walked and false/open pins in Examples/ProofTree. The existing unsafe
  measurement trust entry moved with it. Measurements are not soundness proofs.
- `CloseJ.affine` recognizes normalized literal `Int.ofNat`/`Int.negSucc` and
  conservatively leaves symbolic `Int.negSucc n` as a base. Direct metatests
  cover negative/zero/positive literals and signed addition/subtraction offsets.
  Signed validity/refutation controls use ordinary `sol_close`/`sol_refute`.
- `closeSide`/`closeArith` no longer dereference premises absent from a sibling
  goal's local context. Bound proof IDs flow to `omegaIn`, which already skips
  IDs absent from its local context. Detailed failed range goals are retained.
  **Forced signed sequential closure still fails** at a range side condition:
  `mcp-context-fix-stub.log`, `mcp-signed-literal-detail.log`, archived
  `JoinControls-with-open-step.lean.txt`. General closure is not evidence for
  sequential closure. Earlier solved-state MCP trials were invalid evidence;
  later open-goal trials and per-file diagnostics exposed the limitation.
- SplitTo congruence documentation now states its Solidity context; theorem
  signatures/proofs are unchanged.
- `certifyLong` already discovers the nonempty peeled context correctly in the
  frozen base. Its closed input context `[]` is required by its initial state;
  it extracts and uses the peeled context consistently. No production change
  was appropriate. LongContext supplies `n=5`, pins the resulting nonempty
  context and builds a real kernel certificate refuting a false length claim.
  It also checks no certificate for a true supplied candidate or an unsupplied
  binder. Candidate refusal is not a universal validity proof.

No new axioms/sorry/admit or external dependencies. `lean_verify` on
`conditionalJoined` and `falseLengthRefuted` reports exactly `propext`,
`Classical.choice`, `Quot.sound` (`mcp-backfill-axioms.log`). Its optional source
scan reports rg unavailable inside the child; the host trust/source checks
cover that separate boundary. Kernel theorem certificates establish validity
or refutation, whereas source parser/metatests, sizes and timings are tooling
controls only.

### Gates and independent reviews

All commands below use the absolute work path above; raw `.log` and command
metadata `.json` are retained, including every failed attempt.

- Per-file MCP full diagnostics passed: ProofTree tool, SurfaceNotation,
  LeafSplit, Steps, PolySize, DlNotation, Examples/ProofTree, JoinControls and
  LongContext. The no-build LSP launcher prevents implicit compilation and
  enforces explicit `-j1` server/workers; stale imports produce a failed check
  then a separate bounded build. The early non-j1 implicit setup-file attempt
  was stopped and retained as failure, not a pass.
- `bounded.py backfill-checkpoint-build build` with targets JoinControls,
  LongContext, DlNotation, PolySize, Examples.ProofTree, Tactics.Join passed
  297 jobs, 171.03 s wall; sampled RSS peak 2,933,692 KiB and cgroup peak
  2,304,315,392 bytes. Existing joined-family examples passed unchanged.
- `node scripts/check-automatic.mjs --strict` passed: 491 automatic, 61 with a
  step budget, 0 manual; 11 refuted; 0 pending. This checkpoint's static gate
  does not replace the final TestSuite timed build gate.
- `bash scripts/check-trust.sh` passed: 1050 sources, 248 inventoried
  implementation/recovery sites, 0 findings. `git diff --check` passed.
- `bash scripts/check-doc-paths.sh` **failed** with 48 missing references.
  Exact frozen-base snapshot plus private Git index reproduces byte-identical
  raw output (`base-doc-paths.log` vs `backfill-doc-paths.log`). No new path
  finding; the repository gate itself remains failed, not relabeled pass.
- Root per-file diagnostics and the full final `./run-lean.sh`, full affected
  TestSuite timing/strict gate, full axiom/trust/import audits remain pending
  for the entire assignment. Runtime KeySort passed as recorded above.

Independent read-only finder `/root/setup_finder` and skeptic
`/root/setup_skeptic` reviewed this checkpoint without Lean/server/build/writes.
They requested branch-type rejection, explicit printer-body rereading and root
registration of LongContext; all were added. Both accepted the remaining
changes without a blocking soundness finding, conditional on reporting the
forced signed sequential limitation. The skeptic's bound-ID question was
checked against `omegaIn`'s `lctx.find?` guard. Reviews exclude the pending
warning implementation. Raw review transcription: `work/reviews-backfill.md`.

Shared integration hunks are exactly two additive imports in Solidity.lean,
two new example module-map rows and the ProofTree command clause in its row.
No Rules.lean change. AQ decision hunk remains the setup checkpoint's only
scope-record change. The cumulative patch records the exact hunks.

### Remaining whole-assignment obligations

AU03: connect/review located warnings for DSL/imported/reachable loop bodies,
retain unrolling and remeasure PolySize; sequential dependent-assignment joins
with freshness/order/typing, soundness and size laws; restore original chain
programs/add ifElseJoin row/finish ifTrace; kernel Boolean-atom split with
substitution on the actual mapping-key pin; two-base/beyond-splitMax joined
closure at existing budgets; resolve the signed sequential range limitation.
AU04: genuine bounded non-offset doubling-call leaf sharing through intrinsic
fresh locals with freshness/evaluation/validity proofs; measured walk AND leaf
growth across k; repair and remeasure actual loop leaf cost past anon, with
positive/negative controls. None of those is completed by constant walk size.
Final bounded full gates, timed automatic gate, independent reviews for each
remaining checkpoint, exact final patch/bundle/evidence/checksums remain due.
The existing persistent goal stays incomplete; no competing goal was created.
No push, merge, PR or tag publication.

## AU03 warning checkpoint: keep unrolling and name the loop

AQ2 is implemented as a diagnostic at elaboration/import boundaries. The
original pure program elaboration, loop lowering, `.auto`/unwind choices,
semantics and theorem verdicts are unchanged. No option or invariant was added.
This is the warning portion of AU03; the multi-assignment walk checkpoint is
still incomplete.

`Syntax/LoopWarnings.lean` classifies literal comparisons (signed literals and
units included), reversed/countdown bounds, member subjects and conjunctions.
It does not infer termination or treat a disjunction as a bound. An invariant,
quantified invariant or explicit unwind suppresses only its own loop's notice;
nested unannotated loops remain visible. Direct loops retain their syntax span.
Called bodies use the callee and stable raw statement/block path at the call's
source location. Only statically reachable bodies are scanned, once each,
including modifier, constructor and initializer callees; unused DSL functions
remain silent. Constructor reachability includes indirect calls too.

Splice emits notices once before program elaboration. Notation emits before
modality retries/dual readings and stops the outer syntax scan at embedded Lean
formula holes. It queries called bodies via the existing elaboration evaluator,
returning a quoted string; there is no new unsafe/trust site. Import emits before
loop lowering for each actual row and separately for constructors, sharing a
body/path deduplication set. Imported rows have synthetic parameter/return
prefixes; only those prefixes are dropped from diagnostic paths. Imported source
locals may already have source-adapter aliases (for example solcLocal153), which
are reported honestly rather than relabeled as original source names.

A canonical-callee-only first implementation missed uncalled imported rows:
those rows need not occur in C.funs. The actual failed control is retained in
`mcp-loop-notices-import-names.log`; direct original-row scanning fixes it.
The constructor review also found that constructor-only imports bypass the
function-row loop; the separate constructor hook fixes that actual omission.
No expected verdict was edited. Diagnostic pins were corrected only to the
actual existing source aliases and correct AST contract namespace suffixes.

`Examples/Tactics/LoopNotices.lean` covers direct while/for/do loops, signed and
reversed guards, units, symbolic/no-condition/disjunction silence, every
annotation form, nesting, repeated/transitive/recursive calls, modifier bodies,
unused callees, constructors, constructor initializer calls, symbolic modality
readings and actual pinned imports. A constructor-only Solidity fixture under
`tests/automation` was generated with the already available pinned solc 0.8.34
and existing generator, under the same hard bound/network-none runner. No
compiler/dependency was installed; no compiler-lane API or source profile was
changed. Its FNV pin is `0xa7ef25dc4cfa9c6d`. This is a diagnostic/import test,
not a compiler correctness proof.

The positive diamond theorem proves the loop returns two (so a divergent box
cannot pass vacuously); the negative theorem kernel-refutes return three.
`lean_verify` on exactResult and wrongResult reports precisely propext,
Classical.choice, Quot.sound (`mcp-warning-axioms.log`). Optional MCP source
scanning was disabled for this axiom-only check; the separate trust/source gate
covers that boundary. Pure classifiers/metatests and imported AST generation
are tooling controls, not soundness certificates for a compiler.

### Warning gates, measurements and reviews

- Full per-file MCP diagnostics passed for helper, Splice, Notation, Import and
  LoopNotices; final controls are in `mcp-warning-controls-and-positions.log`.
  The archived direct-source probe emits distinct warning positions 6:3 and 7:3
  (`VA2LoopWarningLocations.lean.txt`); it was removed after capture.
- `bounded.py warning-checkpoint-build build` targeting PolySize, LoopNotices
  and LoopsImport passed 238 jobs in 48.61 s wall. Sampled visible-process RSS
  peak: 1,517,824 KiB; cgroup memory peak: 623,562,752 bytes. Hard memory/swap
  values were asserted before execution. LoopNotices checked in 3.3 s;
  existing LoopsImport checked in 20 s with its original theorem verdicts.
- PolySize's existing complete size pins pass unchanged. Its file check was
  20 s versus the frozen-base cold run's rounded 21 s: no slowdown observed
  in this single comparison, not a statistical performance claim. Walk and
  leaf sizes remain separately measured as in the earlier baseline table.
- A focused paired source-import probe used the exact frozen-base importer
  source and the current importer on the same pinned Loops AST, with shared
  current dependencies. File checks were 1.0 s before and 1.1 s after; the
  combined bounded build passed 39 jobs in 3.16 s wall, sampled RSS peak
  745,520 KiB, cgroup peak 180,883,456 bytes. This isolates importer overhead;
  it is not a second full frozen-base package build. The temporary source
  copies/probes are archived as .lean.txt, then removed from the checkout.
- Exact commands/results, including failed intermediate fixtures, are in work
  `.log`/`.json` files. The generator command/result is
  `warning-ctor-fixture-generate.log`: existing compiler version
  0.8.34+commit.80d5c536.Emscripten.clang, 3948-byte AST, correct FNV pin.

Independent read-only finder and skeptic, neither using Lean/server/builds,
reviewed this checkpoint. Their countdown/compound guard, constructor/import,
initializer, hygiene, source-path and missing-uncalled-row findings were fixed
and exercised by actual controls. Both final source reviews report no confirmed
remaining blocking defect; performance/affected gates above subsequently passed.
Evidence transcription: `work/reviews-warning.md`. Scope is still the warning
portion only. Root/helper/example registrations and module-map rows are narrow
additions; Rules.lean and VA1 files are untouched.

Remaining AU03/AU04 obligations in the previous whole-assignment list still
apply, except the warning implementation/control/PolySize remeasure portion is
now checked. Full final run-lean, complete import/TestSuite timing/strict gates,
final trust/axiom audits and remaining independent proof reviews are still due.
The full persistent goal remains incomplete. No push/merge/PR/tag.

Warning checkpoint static gates: `node scripts/check-automatic.mjs --strict`
passed (491 automatic, 61 budgeted, 0 manual; 11 refuted; 0 pending).
`bash scripts/check-trust.sh` passed (1051 sources, 248 inventoried sites,
0 findings); no temporary benchmark sources remain. `git diff --check` passed.
`bash scripts/check-doc-paths.sh` remains failed with 48 references; its raw
output is byte-identical to the exact frozen-base result. The comparison
passed; the underlying checker was not relabeled pass. Full final gates and
unimplemented AU03/AU04 items remain pending.


## AU03 joined-assignment foundation checkpoint (2026-11-01)

This supporting checkpoint proves the straight-write builder before changing
strategy dispatch. It does not claim multi-assignment walker integration or
completion of AU03/AU04. The singleton join path is unchanged in this checkpoint.

`Calculus/JoinSequence.lean` decodes only intrinsic value-local assignments,
with an explicit indexed motive and a delayed tail on rejected heads. The
Gate G0 open-context/two-write reduction pin is by reflexivity. Successful
decoding proves output-context equality and reconstructs the entire original
program by heterogeneous equality. It neither substitutes RHS terms nor drops
failing assignments whose results are later overwritten.

The builder captures the original simple Boolean condition once in a fresh
intrinsic head local. Every original target is shifted to `.there`; each RHS
is shifted once. Guarded singleton assignments retain source order, and an
untaken RHS is never evaluated. Names are supplied from the existing freshness
budget; positional freshness supplies the semantic independence. No new core
term/state/formula constructor, semantic premise or exclusion is introduced.

`Calculus/Sound/JoinSequence.lean` proves exact ordered execution, preservation
of the snapshot, guarded-list execution with an arbitrary continuation, the
complete joined result, and exact state-and-halt equality after popping the
snapshot. `LocalWrites.joined_sound` gives `Premise.Runs` for every typed state
and either modality without arithmetic/validity hypotheses. These are kernel
proofs of the standalone builder, not proof that a dispatcher already uses it.

`Calculus/JoinSequenceSize.lean` counts emitted program syntax explicitly:
joined size = original if-statement size + three nodes per original write;
the generated size is at most four times original statement size. Both branches,
the snapshot and all guards are counted. The pop is the existing Ext frame,
not emitted program syntax. The first guessed two-node overhead failed because
`Val.simple` adds its own wrapper node; raw failed attempts are retained and
no budget was raised. Program linearity is not asserted to imply leaf linearity.

`Examples/Tactics/JoinSequence.lean` has inhabited kernel controls: one branch
changes its source guard, repeats a uint target and reads the predecessor's
value, while the unselected branch divides by zero. The observed result is
exactly `(false, 2)`. Selecting the zero-divisor branch fails; nested blocks
and requirements are refused; the emitted syntax is pinned to 33 nodes.
The concrete failure projection uses `toOption`; exact halt preservation is
proved generally by the execution equality, not inferred from that projection.

### Foundation gates and independent review

All evidence below is under `/workspace/va2-sharing-artifacts/work/`.

- Per-file MCP diagnostics passed for core (`mcp-join-reconstruct-checked.log`),
  soundness (`mcp-join-sound-final.log`), size (`mcp-join-size-final.log`) and
  controls (`mcp-join-examples-final.log`), with no errors/warnings, partial
  results or timeouts. Intermediate proof failures remain in the raw logs.
- `lean_verify` for `LocalWrites.joined_sound` and
  `JoinSequence.changedGuardDependent` reports only `propext`,
  `Classical.choice`, `Quot.sound`, with no warnings. Source scanning is the
  separate trust gate; MCP scan_source was false.
- `bounded.py join-foundation-build build Solidity.Calculus.JoinSequence
  Solidity.Calculus.JoinSequenceSize Solidity.Calculus.Sound.JoinSequence
  Solidity.Examples.Tactics.JoinSequence Solidity.Examples.Tactics.PolySize`
  passed 224 jobs: 5.94 seconds inside / 6.94 seconds runner wall, sampled
  visible-process RSS peak 1,913,812 KiB, cgroup memory peak 1,337,454,592 bytes.
  Every run asserted memory.max=12,884,901,888 and memory.swap.max=0, serial
  LEAN_NUM_THREADS=1 and explicit Lean -j1. Existing PolySize pins pass unchanged.
- `node scripts/check-automatic.mjs --strict` passed: 491 automatic,
  61 budgeted, zero manual, 11 refuted, zero pending.
- `bash scripts/check-trust.sh` passed: 1055 sources, 248 inventoried sites,
  zero findings. `git diff --check` passed.
- `bash scripts/check-doc-paths.sh` failed with the same 48 references as the
  exact frozen base; raw output compares byte-identical to base-doc-paths.log.
  Only the comparison passes; the underlying checker remains failed.

Independent finder and skeptic re-reviewed the four source modules read-only,
neither using Lean/server/builds. Neither found a blocking source defect.
Both require dispatcher correspondence/shape/fragment integration and actual
walk-versus-leaf measurements before calling this a walker delivery. Finder's
optional exact-concrete-halt strengthening is covered generally by the exact
state/halt theorem; the concrete toOption boundary is explicit above.
Their transcribed results are in `work/reviews-join-foundation.md`.

Root imports and four module-map rows are narrow additive registrations;
Rules.lean and all VA1-owned files remain untouched. The exact registration
hunks are available in the cumulative patch. Final run-lean/TestSuite timing
gates, query/rule/walker integration, chain restoration,
Boolean mapping-key closure, broader joined values, signed sequential closer
repair, AU04 call sharing and loop-leaf repair all remain outstanding as
previously recorded. Full persistent goal remains incomplete. No push/merge/PR/tag.


### Root closure and diagnostic compatibility follow-up

`bounded.py join-foundation-root-build build Solidity` failed after 8077.07
seconds inside the cap: sampled visible-process RSS peak 9,251,844 KiB,
cgroup memory peak 12,573,798,400 bytes. This first cold root closure found
13 message-pin mismatches in seven files caused by the approved loop warnings.
The original failure is retained in `join-foundation-root-build.log` and
`join-root-failure-summary.json`; it is not labeled a passing gate.

Only message docstrings changed in `Evm/Examples`, `Examples/ProofTree`,
`Examples/Tactics/{Branch,CheckedBlock,Loops,StorageSuite}` and `Examples/Verify`.
All original printed programs, outcomes, step budgets, the rejected
break-in-try error and the exact certified counterexample remain unchanged.
Independent finder and skeptic reviewed the complete seven-file/thirteen-pin
patch read-only without Lean/server/builds. Neither found a semantic or
expectation weakening. See `work/reviews-warning-pins.md` and
`work/warning-pins-fix-7files.diff` for exact hunks.

All seven edited files then passed individual bounded MCP diagnostics,
without partial results or timeouts (`mcp-warning-pin-final-1.log` through
`mcp-warning-pin-final-7.log`, aggregate `warning-pin-checks.json`). Expected
warnings outside guarded messages are retained. No budgets were raised.

`bounded.py join-foundation-root-warm build Solidity` passed all 1015 jobs,
216.24 seconds inside / 217.41 runner seconds; sampled visible-process RSS
peak 2,699,500 KiB, cgroup memory peak 1,790,754,816 bytes. The actual enforced
aggregate cap remained 12,884,901,888 bytes with zero swap, threads=1 and
explicit Lean -j1. `mcp-join-root-final.log` reports successful root diagnostics,
no messages, no failed dependencies, no partial results and no timeout.
The client emits an asyncio shutdown traceback after its successful structured
result; exit remains zero. This is not a Lean proof failure.

The remaining axiom checks passed in `mcp-join-foundation-audits-final.log`:
`Prog.localWrites?_reconstruct` uses only `propext`; `LocalWrites.joined_size_le`
uses `propext` and `Quot.sound`. MCP lean_verify's identifier validator rejects
legal names containing `?`; that raw failed tool call is retained separately.
The reconstruction check therefore used MCP lean_run_code with an imported
module and explicit `#print axioms`, not a renamed or weakened theorem.

Static final checkpoint gates (`join-final-*.log`) pass strict automatic
coverage (491 automatic, 61 budgeted, 0 manual, 11 refuted, 0 pending), trust
(1055 sources, 248 inventoried sites, 0 findings), layers (181 core modules,
0 elaborator dependencies), orphans (1040 reachable, 0 orphans) and diff
whitespace. The doc-path failure remains byte-identical to the frozen base's
48 failures. Canonical frozen SolKey snapshot hash verification passes at
commit `473da8944ca7329e6b76819863591407db26e7ec`.
`bash scripts/check-testsuite.sh --complete --solkey tests/migration/solkey/keyext.solidity.examples`
passes: 552 derived + 11 refuted + 1 existing excluded, 0 pending/divergent,
2 skipped. The earlier default invocation failed because `../solkey` is absent;
its raw failure remains. This static certificate/parity check is not a timed
TestSuite Lean build or final `./run-lean.sh` pass. Those full final gates and
all unfinished AU03/AU04 items above remain required. No new exclusion or
validity/hash premise was introduced. The persistent goal remains incomplete.


## AU03 captured-block prerequisite checkpoint (2026-11-01)

Before dispatcher integration, independent finder and skeptic required the
exact premise wrapper to be covered: Premise.capture declares one snapshot,
then runs a block containing only the guarded lists. It must not snapshot twice.
`LocalWrites.captured_drop_runSt` now proves complete state-and-halt equality
with the original conditional after the outer pop. The inner block drops no
locals. `captured_sound` covers either modality without validity/arithmetic/
totality assumptions. `captured_size` counts exactly one additional block node
beyond the raw joined builder. This is still a standalone prerequisite; the
walker does not yet dispatch to it and no new rule is registered here.

Concrete controls execute this actual block with a changed source guard and
subsequent dependent writes, observing original locals `(false, 2)` after
explicitly popping the snapshot. Selecting the bad branch still yields none;
the concrete toOption projection merges halt kinds, while the generic theorem
preserves every halt exactly. Actual emitted program size is 34 versus raw 33.

The first direct rfl success proof hit the unchanged 200000-heartbeat limit;
raw `mcp-join-capture-examples.log` remains failed. An experiment asking rw to
infer the list arguments crashed the MCP scratch worker at the hard 12 GiB cap
(`mcp-join-capture-control-attempt.log`, cgroup peak 12884901888). This is a
retained failed resource experiment, not a pass or performance result. The
finished proof unfolds only the observation/wrapper, invokes the exact
transport theorem with every argument supplied, then computes the original
conditional. `mcp-join-capture-control-explicit.log` records the successful
candidate; final `mcp-join-capture-examples-final.log` passes with no errors,
partial results or timeout. No budget or resource limit was raised.

Both proof files passed per-file MCP (`mcp-join-capture-final.log`); the three
new generic theorems passed lean_verify (`mcp-join-capture-audits.log`). Exact
transport and soundness use only propext/Classical.choice/Quot.sound; size uses
only propext/Quot.sound. All raw tactic/tool failures are retained, including
unavailable child-container rg for lean_local_search and an audit launch
refused by writer.lock before starting any concurrent job.

`bounded.py join-capture-prebuild build Solidity.Calculus.Sound.JoinSequence
Solidity.Calculus.JoinSequenceSize` passed. After stopping MCP,
`bounded.py join-capture-root-build build Solidity` passed 1015 jobs in 9.15s
inside / 10.21s runner wall; sampled visible-process RSS 1916972 KiB,
cgroup peak 1358422016 bytes. Actual aggregate cap remained 12884901888 bytes,
zero swap, LEAN_NUM_THREADS=1 and explicit Lean -j1. This warm closure is not
an uncached throughput measurement. Static checks (`join-capture-*.log`)
pass: strict automatic 491 / 61 budgeted / 0 manual / 11 refuted / 0 pending;
trust 1055 sources / 248 sites / 0 findings; layers 181 / 0 elaborator; orphans 1040 / 0;
diff whitespace. The final doc-path check is still compared to the exact base;
the unchanged 48 failures remain failures. No final run-lean / timed TestSuite claim.

Finder and skeptic independently reviewed the final exact wrapper proofs,
size law and revised concrete proof read-only without Lean/server/builds.
Neither found a defect, added premise, exclusion, observation change or budget
increase. See `work/reviews-join-capture.md`. Dispatcher/query/rule/fragment
integration, actual walk/leaf measurements and all remaining AU03/AU04 work
listed above remain unfinished. Full persistent goal remains incomplete.


## AU03 weakening prerequisite checkpoint (2026-11-01)

`Prog.localWrites?_wk_isSome` proves exact equality of acceptance/refusal
before and after any intrinsic Thin. It does not claim decoded lists are
literally unchanged or substitute for semantic transport. The proof uses the
intrinsic mutual program recursor with a trivial statement motive, rejecting
nonassignment heads by reduction and propagating the assignment-tail result
through Option.map. The earlier direct recursive attempt failed termination;
raw `mcp-join-wk-attempt.log` remains failed. No budget was raised.

Per-file MCP diagnostics pass with no messages, partial result or timeout
(`mcp-join-wk-final.log`). MCP lean_run_code checks the source with explicit
`#print axioms`; the legal question-mark name is unsupported by lean_verify's
validator. The axiom set is only propext. `bounded.py join-wk-prebuild build
Solidity.Calculus.JoinSequence` passes 40 jobs, 4.23 seconds inside / 5.44
runner seconds; sampled visible-process RSS peak 827920 KiB, cgroup peak
293044224 bytes. Memory cap 12884901888 bytes and swap 0 remain enforced,
with LEAN_NUM_THREADS=1 and explicit Lean -j1. This focused prebuild is not
a new full-root or final run-lean pass.

Independent read-only finder and skeptic found no defect or added premise,
exclusion or budget change; neither used Lean/server/builds/writes. Evidence:
`work/reviews-join-weakening.md`. Trust and diff checks pass; the doc-path
checker still has the same 48 byte-identical frozen-base failures. All actual
dispatcher, rule correspondence/fragment integration, walk/leaf measurements,
closer, chain and AU04 work listed above remains required. Full persistent
goal remains incomplete.


## AU03 complete write-data weakening prerequisite (2026-11-01)

`LocalWrites.wk` shifts each intrinsic target and RHS through the same Thin,
preserving list order without composing or substituting terms.
`Prog.localWrites?_wk` proves equality of the complete decoded write data,
including refusal (`none`), before and after weakening. This strengthens the
previous success/refusal-only theorem without changing its statement.
The intrinsic mutual recursor uses a trivial statement motive; rejected
heads reduce without traversing their continuations. No import, semantic
premise, observation, proof budget or exclusion changes.

Per-file MCP errors are zero (`work/mcp-join-write-data-wk-final.log`).
The legal question-mark theorem name is unsupported by lean_verify's name
validator, so MCP lean_run_code checked the source and explicit `#print axioms`:
only propext. `bounded.py join-write-data-wk-prebuild build
Solidity.Calculus.JoinSequence` passed 40 jobs in 4.83s inside / 5.33s runner,
sampled visible-process RSS peak 837276 KiB, cgroup peak 314159104 bytes.
Actual memory.max=12884901888, memory.swap.max=0, LEAN_NUM_THREADS=1 and
explicit Lean -j1 remained enforced. This is a focused prerequisite gate,
not the final run-lean or timed TestSuite gate.

Independent read-only finder and skeptic found no correctness, typing,
ordering, refusal, premise or budget issue; neither used Lean/server/builds
or writes. Evidence: `work/reviews-join-write-data-weakening.md`.
The static prerequisite checks are saved as `work/join-write-data-*.log`.
The doc-path checker remains a failure with the same 48 byte-identical
frozen-base findings; the comparison passes, not the checker itself.

Production dispatcher/rule/fragment integration and concrete control work
is in progress separately and is not certified by this prerequisite commit.
Although the Stmt.inSolkey definition is textually unchanged there, its
joinShape dependency classifies newly joined programs through a Lean-only
rule; do not claim extensional fragment membership is unchanged. Canonical
short-circuit programs retain their existing SolKey split path. Full walk
and leaf measurements, chain restoration, broader closer work, AU04 sharing,
final gates and checkpoint review/handoff remain required. The persistent
full-assignment goal remains incomplete.


## AU03 joined-walk checkpoint — production integration

This checkpoint integrates typed multi-assignment joins and their closer support. It does not complete AU03's Boolean mapping-key kernel pipeline, AU04, the isolated post-`anon` measurement/repair, or final whole-assignment gates.

The old singleton algorithm remains `Upd.ifJoinSingle?`; the public `Upd.ifJoin?` now returns a `JoinPlan` (old update or captured straight-write sequence). Its singleton premise expands to `some (.inl u)`. Decoder success reconstructs the original typed programs. The new Lean-only `ifElseJoinSequence` row captures the Boolean guard once, then executes ordered guarded assignments without substituting RHS terms into one another. Exact canonical generated short-circuit AND/OR shapes retain their existing split path; source semantics are not excluded. `Stmt.inSolkey` is textually unchanged, but its dependence on the generalized join eligibility changes membership for newly joined programs. Those programs use the Lean-only row.

`LocalWrites.joinPlan_sound` preserves evaluation order, selected failures, unselected non-evaluation, state/frame transport and both modalities. `LocalWrites.joinPlan_size_le` counts the actual emitted snapshot/block/guarded program: at most `4 * originalStmt.size + 1`. The existing immediate-update/formula bound is not a program or leaf bound. No generic leaf-linearity or call-family bound follows from either theorem.

The closer retains its already-proved normalized defining facts instead of normalizing the same equations again at the final post. Multi-base hulls use only current certified bounds, and inferred endpoints still require arithmetic proof from actual facts. Bounded Boolean cases retain `joinMaxCases = 64`; `splitMax = 6`, `wholeMax = 5`, `shareNodes = 20000`, the 100k step budget, 20k finish allowance and declaration budgets are unchanged. Lazy side-case normalization proves decision equivalences before arithmetic, filters stale certificate IDs and restores failed side-check state. A local Int-comparison negation may refuse a tactic goal inside the same 20k allowance; it never supplies a global refuted verdict. Actual negative results below have independent inhabited kernel countermodels.

`NTerm.ite` now checks both arms at an enclosing primitive value sort. Its synthesis and non-value widening paths remain the old ones. Signed positive-literal, mixed/nested, both-branch mismatch, unsigned synthesis, KeY widening and exact AST roundtrips through both formula printers pass. The original singleton programs in StorageCoverage are restored, with actual join links and a separate genuine reverting-arm split control. Their final parallel conditional RHSs are exact state functions, retain captures and arbitrary postconditions, and pass `#last_line`; they are not weakened observations. ChainNotation.ifTrace now reaches the joined update and merged storage-read conditional.

The new rule printer now handles the captured schema program through the existing program-piece path. Unsupported program-variable stems retain the raw typed fallback, with ten positive/negative name controls. The complete typed rule conclusion roundtrips through the scoped Schema reader with `isDefEq`; exact `#taclet` output and all 181/28/4 rule-printing coverage pins pass. This is the actual new Lean-only row, not a new SolKey rule.

Precision correction to the earlier baseline section: its phrase “largest leaf past anon” meant the largest whole leaf after `sol_leaf`; those timings do not isolate repeated work after an anonymising frame. The exact post-`anon` measurement and repair remain pending. The older raw runs remain useful whole-leaf baseline data only.

### Production walk/leaf pins

| Family | Walk nodes | Leaves | Open | Largest leaf term nodes |
|---|---:|---:|---:|---:|
| Two dependent assignments per arm | 17 | 1 | 0 | 57 |
| Four per arm | 21 | 1 | 0 | 89 |
| Eight per arm | 29 | 1 | 0 | 153 |
| Two sequential multi-assignment conditionals | 29 | 1 | 0 | 101 |
| Three sequential conditionals | 41 | 1 | 0 | 145 |
| Seven independent guards / two bases | 40 | 1 | 0 | 139 |
| Twelve guards / two bases | 65 | 1 | 0 | 229 |

These are pinned actual production `#proof_size` outputs. All corresponding complete source theorems use existing `sol_auto`, not a research closer override. The frozen-base two-write-per-arm source had 15 nodes, two leaves and largest leaf 36; joining need not reduce the largest single leaf. The frozen-base coupled seven-guard source remained open beyond the existing split limit. Existing reset-seven baseline already closed and is not claimed as a new delivery.

### Cost and proof boundaries

On identical pre-retention leaves, original/candidate step closers both kernel-closed under the same 100k budget. Raw heartbeats (millions): one join 4.462/4.464; two 8.045/8.038; six 25.559/25.510; sixteen unrelated local declarations plus two joins 24.876/24.805. Per-case elapsed times and suite RSS are in `join-retain-performance-results.json` and `mcp-join-retain-perf.log`; RSS was not isolated per case. The one-join wall sample increased from 0.357s to 0.467s, so this is not a blanket zero-regression claim. Retained-fact instrumentation measured 16/12 facts and 1524/1002 summed per-fact nodes for eight-write/three-sequential captured leaves. Their successful closure used the existing fast arithmetic path; an experimental sliced fallback was unnecessary and is not in production.

The first strict false-correlation control really timed out at the existing 20k finish allowance. That run remains FAIL in `mcp-join-retain-negative-strict.log`. After the local comparison-negation repair, strict controls pass with ordinary refusal at 12.574m raw heartbeats instead of roughly 32m; global falsity is separately kernel-certified. Earlier recovery-generated success lines, incomplete proofs, stale imports and timeout attempts remain raw failures, never completion evidence. Thirteen owned research sources were archive/hash verified before removal from the production tree: `joined-research-probes-20261101.tar.gz` and its SHA256 JSON.

Runtime remains the existing same-VM Docker runner: pinned Debian image, UID/GID 1000, network disabled, enforced `memory.max = 12884901888`, `memory.swap.max = 0`, `LEAN_NUM_THREADS=1`, explicit Lean `-j1`/bounded stack, at most two configured LSP files and no overlapping build/LSP. Sampled aggregate process RSS and actual cgroup peaks are distinct metrics. Lean 4.24.0 commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Lake 5.0.0-src+797c613; passing KeySort and RUNTIME_GATE_PASS remain in the runtime-recovery evidence. No RSS watchdog or per-process address-space limit is claimed as the aggregate cap.

### Gates and independent reviews

Per-file production diagnostics passed for CloseScoped/Steps, NamedTerm, JoinSequence, JoinWalk, JoinIntervals, JoinControls and both chain files. Exact bounded commands, outcomes, RSS and raw diagnostics are under `/workspace/va2-sharing-artifacts/work`; final focused-build/axiom records are appended below after they finish. Static strict automation, trust, layers, orphans and diff checks pass. The documentation-path checker itself fails with byte-identical raw output against frozen base `8bd8742ad987d566f7ba7624372cec1c020be07c`; its exact-base comparison passes, not the checker.

Independent read-only finder and skeptic reviewed the dispatcher/proofs, row registration, inhabited controls, closer, notation and chain endpoints without Lean/server/builds/writes. Confirmed findings fixed include a non-decisive false-guard observation, uninstantiated generated theorem type, stale bound IDs, incorrect case context, catch-all resource refusal reporting, missing metric pins/docstrings and the literal-condition documentation claim. Full reviews and retained findings are in the `reviews-join-*` and `reviews-hull-bool-prototype.md` evidence, with this checkpoint's final review record appended below. No reviewer approval substitutes for pending full gates.

### Shared integration and remaining queue

Shared registration hunks are narrow additive changes relative to the frozen base: the new Rules.lean Lean-only constructor; Solidity.lean module imports; the owned module-map entries. The exported shared-registration patch records exact hunks. The matching AQ1/AQ2 scope receipt remains the approved setup hunk; no additional approval is claimed.

The earlier forced signed sequential range-closure failure (`mcp-context-fix-stub.log`, `mcp-signed-literal-detail.log`) was retested exactly with `sol_close_join_steps` after these changes and still FAILS (`sol_close_join_steps: the leaf did not close`, no timeout). Its repair remains pending; passing conditional expected-type and signed-offset controls do not settle that failure.

Outstanding: resolve that exact still-failing signed sequential range fixture; the actual boolKeyMappingSymbolicKey split/substitution kernel pipeline and controls; exact frozen post-`anon` leaf timing; full AU04 fresh-result/call-family sharing, freshness/evaluation/validity laws, full payload sizes, unchanged observables and actual loop repeated-cost repair; final affected/full bounded run, timed strict automatic gate and final audits/reviews/package. Non-offset doubling-call leaves still have the earlier measured `18 + 4 * 2^k` growth until AU04 changes them. Existing SolKey rule shapes and intrinsic syntax constructors remain unchanged. No AU05/AU06, compiler/PC lane, options work, new axioms, weakened semantic premises or new exclusions are authorized or delivered here. The full goal remains incomplete.

### Checkpoint gate commands and outcomes

All Lean commands below use `python3 /workspace/va2-sharing-artifacts/work/bounded.py LABEL ...`, the same task-owned Docker runner, hard memory/no-swap cap, serial thread settings and repository writer lock described above. Wrapper JSON records the complete Docker command and mounted exact checkout; log footer records sampled aggregate RSS and cgroup peak. No raw bare Lean/Lake invocation is used.

- `... bounded.py join-checkpoint-affected-build-final build Solidity.Examples.Tactics.PolySize Solidity.Examples.Tactics.JoinControls Solidity.Examples.Tactics.JoinSequence Solidity.Examples.Tactics.JoinWalk Solidity.Examples.Tactics.JoinIntervals Solidity.Examples.Tactics.CallSummary Solidity.Examples.Chains.StorageCoverage Solidity.Examples.ChainNotation Solidity.Examples.Tools`: PASS, `Build completed successfully (269 jobs)`, wrapper 308.64s, sampled aggregate RSS 1,984,492 KiB, cgroup peak 1,190,064,128 bytes. Exact log/JSON: `work/join-checkpoint-affected-build-final.{log,json}` in the evidence archive.
- `... bounded.py mcp-join-rule-printer-safe-file2 /workspace/solidity-lean/.venv/bin/python .../mcp_probe.py .../requests/join-rule-printer-file.json`: PASS per-file diagnostics, 34.82s. The earlier String API correction failure remains retained.
- `... bounded.py mcp-join-tools-printer-safe-roundtrip2 /workspace/solidity-lean/.venv/bin/python .../mcp_probe.py .../requests/join-tools-printer.json`: PASS per-file diagnostics, 8.62s, with exact output/typed roundtrip/name controls/complete census pins. Earlier stale imports, absent scoped reader and monadic list API failures remain retained.
- `node scripts/check-automatic.mjs --strict`: PASS, 491 automatic plus 61 step-budget declarations, zero manual, 11 refuted, zero pending. This static gate is not the final timed build-log gate.
- `bash scripts/check-trust.sh`, `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`, `git diff --check`: PASS. Layers: 181 core modules, zero reach elaborator; orphans: 1042 reachable, zero orphaned, zero not allowed. The mistaken direct trust-script invocation rejected missing stdin and is separately retained, not a passing audit.
- `bash scripts/check-doc-paths.sh`: FAIL, inherited 48 findings; byte-identical exact-frozen-base comparison PASS, SHA256 `01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a`. Raw candidate and exact-base logs retained; no path checker PASS claimed.

Independent final source reviews: finder confirmed and guided the unsupported program-name fallback repair; skeptic required explicit signed sequential accounting and precise unchanged SolKey/intrinsic-constructor wording. Both fixes are included. Neither reviewer used Lean, a server, a build or writes. Evidence: `work/reviews-join-checkpoint-printer.md`, together with the earlier per-area review records.

- `... bounded.py mcp-join-checkpoint-production-audits /workspace/solidity-lean/.venv/bin/python .../mcp_probe.py .../requests/join-checkpoint-production-audits.json`: headline `lean_verify` PASS for rootW8 (propext/Classical.choice/Quot.sound) and staleDecisionClosed (propext/Quot.sound); compiled-import audit PASS for all 27 production fixture theorems, each using only a subset of the standard three axioms. Exact extracted results: `work/join-checkpoint-production-audit-results.json`. Runtime wrapper 115.12s, sampled aggregate RSS 5,128,548 KiB, cgroup peak 3,147,763,712 bytes.
- The same serial job's separate exact signed sequential retest is FAIL, not a timeout: `sol_close_join_steps: the leaf did not close`. The probe wrapper exit 0 does not turn this structured `success=false` into PASS. This known unfinished backfill remains in the queue and is not replaced by the passing signed-offset ordinary-closer controls.

The committed handoff records this checkpoint's parent `2a437a434eeb084a4e4e68d06a11008b093f3d35`; its own resolved full committed head is bound in the exported `revision.json` and handoff. Whole-assignment status remains partial.


## AU03 Boolean mapping-key kernel checkpoint

The exact original `Solkey.TestSuite.boolKeyMappingSymbolicKey.problem` now closes through `sol_prove` alone. Its assigned `Derived5.lean` pin removes only the manual `sol_leaf; sol_close` replay. The theorem has been checked independently in a self-contained MCP snippet and in the actual Derived5 file; the snippet's axiom set is the standard propext/Classical.choice/Quot.sound.

The missing operation was not negative-target splitting. The original final leaf has a positive Boolean equality, under an earlier symbolic mapping result being unequal to one. Existing `Facts.proveEqN` already splits the Boolean atom and substitutes through `addEqn`/`addNeq`/`rebuild`. One branch thereby retains contradictory normalized disequalities. New `Facts.clashRaw_false` derives False only from the unchanged `Facts.Ok.nes` certificate (both sides return unequal values) and typed structural term equality. `directOrClash` tries the old direct equality path first, then scans those retained facts without new normalization. Its soundness feeds the existing proveEqN recursion. `closeFuel=3`, all returns guards, observation/validity/hash premises, syntax constructors and the one-rule strategy remain unchanged. Existing `LFml.verdict_eq_M`/`close_eq_closeM` still check; kernel and executable paths use the same helper. This reuses existing certified atom splitting/substitution, not a new calculus row.

Finished controls are consolidated in the existing registered JoinControls file, without bringing TestSuite imports into the default example target. They include an explicit intrinsic witness for every consistent-list size, a generic semantic proof of the false target for any such size, raw clash plus impossibility of a sound certificate, halting operands not stored as returning disequalities, a partial negative-equality premise that cannot prove false (with an actual semantic countermodel), same numeric ID at bool/uint, shadow removal plus a decisive nested source-binder positive/refuted pair, an ordinary direct equality, the symbolic Boolean-key source assertion and its changed-assertion kernel refutation. Actual per-file diagnostics and headline axiom checks pass. Trial syntax/API errors and recovered empty goals are retained as failures, not proof evidence; the finished source checks decide success.

### Cost boundaries, including failures

Identical benchmark code runs on exact frozen base 8bd8742ad987d566f7ba7624372cec1c020be07c and the candidate, in the same VM/runner/cap. Each logs whether the new helper is present (false on base, true on candidate), guarding against stale cache reuse. Benchmark source hashes and extracted outcomes are retained in `work/bool-facts-performance-results.json` and the raw logs.

Reflective kernel equality checks PASS for direct targets at 0/8/32/128 consistent facts; raw heartbeats base/candidate are 25,699/26,131; 25,582/25,997; 25,563/26,002; 25,565/25,992. This measured constant extra cost is consistent with retaining the fast path. False targets PASS at 0 and 8 facts, with 404,747/436,286 and 504,764/627,977 raw heartbeats. The latter is about 24.4% extra raw heartbeats; no zero-regression claim is made.

Reflective false targets at 32 and 128 facts FAIL at the unchanged default recursion limit in BOTH frozen base and candidate. Both full reflective benchmark runs therefore have structured success=false, despite the orchestration wrapper returning zero. No maxRecDepth/heartbeat increase, expected-verdict edit or deletion hides those failures. The generic semantic control proves the false outcome without forcing those large reflective normal forms; it is not a claim that reflection at those sizes passed.

Separate compiled-execution samples PASS all direct/false 0/8/32/128 rows in both checkouts. At 128 facts, the false-target single sample is 1.929115ms base / 2.461432ms candidate. These are external execution measurements; first rows include warm-up effects, and suite RSS is not per-row RSS. They are not kernel-normalization timings or a new leaf/call-family size law. Exact commands, cgroup/RSS footer and raw results are retained. The initial plain Lake-env CLI attempt failed to resolve a private cached artifact and is retained; the existing MCP setup-file mechanism resolved the cache in each worktree without a new runtime or installation.

### Remaining assignment

AU03's original mapping-key gap is repaired. The exact forced signed sequential range fixture still fails and remains assigned backfill. Isolated post-anon measurement and actual repeated-cost repair, AU04 fresh intrinsic call-result sharing and full payload-size/freshness/evaluation/validity laws and measurements, final full bounded run/timed automatic gate/audits/reviews/package remain incomplete. Non-offset doubling-call leaves still have the original measured exponential growth; no call-sharing completion follows from this Boolean repair.

### Checkpoint gates and resources

All Lean commands use the existing task-owned bounded.py Docker wrapper (same VM, pinned image, network disabled, `memory.max = 12884901888`, `memory.swap.max = 0`, thread 1, Lean `-j1`, at most two configured LSP files, no simultaneous build/server). Actual Lean 4.24.0 / Lake 5.0.0-src+797c613 and prior passing KeySort remain in the combined runtime evidence.

- `... bounded.py bool-checkpoint-affected-build build Solidity.TestSuite.Derived5 Solidity.Examples.Tactics.JoinControls Solidity.Examples.Tactics.JoinSequence Solidity.Examples.Tactics.JoinWalk Solidity.Examples.Tactics.JoinIntervals Solidity.Examples.Chains.StorageCoverage Solidity.Examples.ChainNotation Solidity.Examples.Tactics.PolySize Solidity.Examples.Tactics.CallSummary Solidity.Examples.Tools`: PASS, 283 jobs, wrapper 234.23s, sampled aggregate RSS 2,871,756 KiB, cgroup peak 2,032,439,296 bytes. Old metric/printer/chain/control expectations unchanged and passing.
- Actual per-file MCP: Closer/Leaf PASS after code and final docstrings; Derived5 PASS; JoinControls PASS after all final source-shadowing controls. New law and positive/refuted/partial/shadow headline `lean_verify` results use only standard axioms. Exact raw/extracted output under `work/mcp-bool-*` and `work/bool-production-evidence-results.json`; latest final records are appended below.
- Reflective/native benchmark commands use the same MCP probe on current and exact-base worktrees; full commands/caps/RSS are in their matching JSON/logs. Reflective full scripts FAIL as described above; native full scripts PASS. `work/bool-facts-performance-results.json` binds identical source-code hashes and actual outcomes. Suite RSS is separate from each timed row.
- `node scripts/check-automatic.mjs --strict`, `bash scripts/check-trust.sh`, `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`, `git diff --check`: PASS; automation 491 automatic + 61 budgeted / 0 manual / 11 refuted / 0 pending, layers 181 core / 0 elaborator, orphans 1042 reachable / 0 orphan / 0 not allowed.
- `bash scripts/check-doc-paths.sh`: inherited FAIL, 48 findings; exact frozen-base raw comparison PASS, identical SHA256 01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a. The checker itself is not called PASS.

Independent finder and skeptic read-only reviews found no correctness defect. Confirmed test/docstring/evidence findings fixed; measured cost retained. Neither reviewer used Lean/server/build/writes. Evidence `work/reviews-bool-kernel.md`. The exported package will bind this checkpoint's full resolved head; parent is `665e66d3a6cc7822acdea7b5e0a554583b315f3e`. Full goal remains incomplete.

- Final `... bounded.py bool-checkpoint-controls-final-build build Solidity.Examples.Tactics.JoinControls Solidity.TestSuite.Derived5`: PASS, 242 jobs, wrapper 14.24s, sampled aggregate RSS 1,538,668 KiB, cgroup peak 430,653,440 bytes. This checks the exact final source-shadowing additions after the broader 283-job gate.
- Final `... bounded.py mcp-bool-controls-shadow-final .../mcp_probe.py .../requests/bool-controls-shadow-final.json`: per-file diagnostics PASS and both actual source-shadowing `lean_verify` audits PASS, wrapper 34.24s. Final `... bounded.py mcp-bool-checkpoint-all-axioms .../mcp_probe.py .../requests/bool-all-axioms.json`: PASS, all 25 compiled actual theorem audits use only subsets of propext/Classical.choice/Quot.sound, wrapper 14.65s; extracted `work/bool-final-axiom-results.json`.


## Parallel producer interface (2026-11-01)

The ready concrete declarations and client obligations are indexed in [PARALLEL-INTERFACE](after-roadmap-va2-interface.md). This incremental export preserves source checkpoint `04da7063854f2bb719e2bed9ab52c306279da4ee`; it makes no AU04 leaf-linearity or full-assignment completion claim. Independent read-only finder and skeptic reviewed the interface against the concrete modules and witnessed clients, without Lean/server/builds; neither found a semantic or completion mismatch. The skeptic wording refinement separates kernel semantic proofs from diagnostic/measurement evidence. Packaging and checksum verification are required separately. Full AU04 and final gates remain open.
