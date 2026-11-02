# VA2 AU03/AU04 handoff

Status: the assigned AU03/AU04 implementation/proofs and backfill are complete. Full bounded default/TestSuite/sort and affected Corpus builds passed, as did complete timed automation and compiled-value axiom audits. Final static/review/package records below bind the delivered tree; inherited documentation-path failures and intrinsic/runtime boundaries remain explicit.

Repository: VM location `va2-sharing`. Branch:
`codex/solidity-automation-20261031/va2-sharing`. Exact base:
`8bd8742ad987d566f7ba7624372cec1c020be07c`.

## Current queue status

- Baseline measurements/source audits, AU03 warning/unrolling, typed joined walks, conditional notation/chains, Boolean mapping-key kernel closure, multi-base/beyond-split controls and signed sequential/conjunctive repair: checked.
- Original backfill (printer roundtrip/chain rows, Int.negSucc, SplitTo docs, proof_size relocation/pins, certifyLong audit/context controls, warning fixtures): completed or reused as documented below.
- AU04: whole-result capture, operational base/graph definitions, complete intrinsic UInt family leaves, full formula-size/context bounds, multi-k semantic clients and one measured post-anon loop repair checked. Actual expanded-assignment, typed source-call transport and explicit parsed-source f6/f7 proofs/metrics and default closer integration checked; full bounded gates now passed.
- Full bounded `./run-lean.sh`, affected Corpus, complete timed automation and assignment-wide source reviews passed. Final static/review/package bookkeeping is recorded below. Earlier sections retain historical pending states and raw failures; later checkpoints supersede them without deleting evidence.

## Setup checkpoint

Fetched `origin master` and the exact base from the configured GitHub remote.
`origin/master` equals the base; merge-base ancestry passed. Preserved the
older clean `.` checkout at `9b24b57311b8daf0d4cd01b52bf420fd024c1d3a`
on `work`, creating this isolated worktree instead. Recorded exact AQ1/AQ2
human answers in `docs/solidity-scope.md` before implementation. No Lean
source edits. `git diff --check` passed.

Independent read-only finder `/root/setup_finder` and skeptic
`/root/setup_skeptic` both found no issues with branch/base/ancestry or exact
approval receipt; neither used the Lean server. Evidence:
VM location `va2-sharing-artifacts/evidence/reviews.md`.

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
VM location `va2-sharing-artifacts/evidence/setup.json`.

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
evidence archive and SHA256 manifest under VM location `va2-sharing-artifacts`.
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
sets the existing writable `XDG_CACHE_HOME=VM setup: cache`.

Original checkpoint `29aec17e607a5dfc585a0e4a49990dc8e3f751c3` and every
original artifact were preserved; all original SHA256SUMS entries verified.
New evidence is separately stored under
VM location `va2-sharing-artifacts/runtime-recovery/`, with exact command arrays,
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
VM location `va2-sharing-artifacts/work/`. All Lean work runs in the same managed
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

All evidence below is under VM location `va2-sharing-artifacts/work/`.

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

Per-file production diagnostics passed for CloseScoped/Steps, NamedTerm, JoinSequence, JoinWalk, JoinIntervals, JoinControls and both chain files. Exact bounded commands, outcomes, RSS and raw diagnostics are under VM location `va2-sharing-artifacts/work`; final focused-build/axiom records are appended below after they finish. Static strict automation, trust, layers, orphans and diff checks pass. The documentation-path checker itself fails with byte-identical raw output against frozen base `8bd8742ad987d566f7ba7624372cec1c020be07c`; its exact-base comparison passes, not the checker.

Independent read-only finder and skeptic reviewed the dispatcher/proofs, row registration, inhabited controls, closer, notation and chain endpoints without Lean/server/builds/writes. Confirmed findings fixed include a non-decisive false-guard observation, uninstantiated generated theorem type, stale bound IDs, incorrect case context, catch-all resource refusal reporting, missing metric pins/docstrings and the literal-condition documentation claim. Full reviews and retained findings are in the `reviews-join-*` and `reviews-hull-bool-prototype.md` evidence, with this checkpoint's final review record appended below. No reviewer approval substitutes for pending full gates.

### Shared integration and remaining queue

Shared registration hunks are narrow additive changes relative to the frozen base: the new Rules.lean Lean-only constructor; Solidity.lean module imports; the owned module-map entries. The exported shared-registration patch records exact hunks. The matching AQ1/AQ2 scope receipt remains the approved setup hunk; no additional approval is claimed.

The earlier forced signed sequential range-closure failure (`mcp-context-fix-stub.log`, `mcp-signed-literal-detail.log`) was retested exactly with `sol_close_join_steps` after these changes and still FAILS (`sol_close_join_steps: the leaf did not close`, no timeout). Its repair remains pending; passing conditional expected-type and signed-offset controls do not settle that failure.

Outstanding: resolve that exact still-failing signed sequential range fixture; the actual boolKeyMappingSymbolicKey split/substitution kernel pipeline and controls; exact frozen post-`anon` leaf timing; full AU04 fresh-result/call-family sharing, freshness/evaluation/validity laws, full payload sizes, unchanged observables and actual loop repeated-cost repair; final affected/full bounded run, timed strict automatic gate and final audits/reviews/package. Non-offset doubling-call leaves still have the earlier measured `18 + 4 * 2^k` growth until AU04 changes them. Existing SolKey rule shapes and intrinsic syntax constructors remain unchanged. No AU05/AU06, compiler/PC lane, options work, new axioms, weakened semantic premises or new exclusions are authorized or delivered here. The full goal remains incomplete.

### Checkpoint gate commands and outcomes

All Lean commands below use `python3 VM location: va2-sharing-artifacts/work/bounded.py LABEL ...`, the same task-owned Docker runner, hard memory/no-swap cap, serial thread settings and repository writer lock described above. Wrapper JSON records the complete Docker command and mounted exact checkout; log footer records sampled aggregate RSS and cgroup peak. No raw bare Lean/Lake invocation is used.

- `... bounded.py join-checkpoint-affected-build-final build Solidity.Examples.Tactics.PolySize Solidity.Examples.Tactics.JoinControls Solidity.Examples.Tactics.JoinSequence Solidity.Examples.Tactics.JoinWalk Solidity.Examples.Tactics.JoinIntervals Solidity.Examples.Tactics.CallSummary Solidity.Examples.Chains.StorageCoverage Solidity.Examples.ChainNotation Solidity.Examples.Tools`: PASS, `Build completed successfully (269 jobs)`, wrapper 308.64s, sampled aggregate RSS 1,984,492 KiB, cgroup peak 1,190,064,128 bytes. Exact log/JSON: `work/join-checkpoint-affected-build-final.{log,json}` in the evidence archive.
- `... bounded.py mcp-join-rule-printer-safe-file2 .venv/bin/python .../mcp_probe.py .../requests/join-rule-printer-file.json`: PASS per-file diagnostics, 34.82s. The earlier String API correction failure remains retained.
- `... bounded.py mcp-join-tools-printer-safe-roundtrip2 .venv/bin/python .../mcp_probe.py .../requests/join-tools-printer.json`: PASS per-file diagnostics, 8.62s, with exact output/typed roundtrip/name controls/complete census pins. Earlier stale imports, absent scoped reader and monadic list API failures remain retained.
- `node scripts/check-automatic.mjs --strict`: PASS, 491 automatic plus 61 step-budget declarations, zero manual, 11 refuted, zero pending. This static gate is not the final timed build-log gate.
- `bash scripts/check-trust.sh`, `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`, `git diff --check`: PASS. Layers: 181 core modules, zero reach elaborator; orphans: 1042 reachable, zero orphaned, zero not allowed. The mistaken direct trust-script invocation rejected missing stdin and is separately retained, not a passing audit.
- `bash scripts/check-doc-paths.sh`: FAIL, inherited 48 findings; byte-identical exact-frozen-base comparison PASS, SHA256 `01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a`. Raw candidate and exact-base logs retained; no path checker PASS claimed.

Independent final source reviews: finder confirmed and guided the unsupported program-name fallback repair; skeptic required explicit signed sequential accounting and precise unchanged SolKey/intrinsic-constructor wording. Both fixes are included. Neither reviewer used Lean, a server, a build or writes. Evidence: `work/reviews-join-checkpoint-printer.md`, together with the earlier per-area review records.

- `... bounded.py mcp-join-checkpoint-production-audits .venv/bin/python .../mcp_probe.py .../requests/join-checkpoint-production-audits.json`: headline `lean_verify` PASS for rootW8 (propext/Classical.choice/Quot.sound) and staleDecisionClosed (propext/Quot.sound); compiled-import audit PASS for all 27 production fixture theorems, each using only a subset of the standard three axioms. Exact extracted results: `work/join-checkpoint-production-audit-results.json`. Runtime wrapper 115.12s, sampled aggregate RSS 5,128,548 KiB, cgroup peak 3,147,763,712 bytes.
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


## AU04 incremental whole-result capture (2026-11-01)

`Calculus/CallResultCapture.lean` provides `capture`, `restore`, and `leaf`, all intrinsically indexed over the original context and a fresh primitive head. `capture_applyV` evaluates the complete result once. `restore_locals` and `restore_state` preserve the old context, exact state, globals and heap after copying into a shifted old target and popping. `target_fresh` excludes aliasing the head. `capture_exh` retains the exact exhaustion predicate. `sound`, `complete`, and `holds_iff` prove exact equivalence for every typed state, primitive result, postcondition and both modalities, without totality or push-free assumptions. `leaf_size` counts `t.size + φ.tmSize + 5`; it does not bound an already-expanded result term.

The inhabited client checks old-target dependence at a non-head target, preserved neighbor, distinct argument, wrong-result rejection, selected division-by-zero under box and diamond, overflow, two identical display names holding distinct values 13 and 7, preserved balance 5, and actual complete syntax size 11. Generic exhaustion transport is proved algebraically; these concrete failure controls have exhaustion false and do not independently witness exhaustion true. No external EVM result is claimed.

Gates and raw evidence under VM location `va2-sharing-artifacts/work`:

* `python3 .../bounded.py mcp-call-result-capture-audit .venv/bin/python .../mcp_probe.py .../requests/call-result-capture-audit.json`: PASS, both actual files diagnostics and 20 theorem audits; axiom sets are subsets of `propext`, `Classical.choice`, `Quot.sound`. 11.596 seconds inside; sampled aggregate visible RSS 3,040,652 KiB, cgroup peak 1,368,399,872 bytes. Final client diagnostics after review wording correction also PASS (`mcp-call-result-capture-final.log`). Earlier failed iterations remain raw evidence, not passes.
* `python3 .../bounded.py call-result-capture-affected build Solidity.Calculus.CallResultCapture Solidity.Examples.Tactics.CallResultCapture`: PASS, 64 jobs, 1.610 seconds inside, sampled visible aggregate RSS 771,220 KiB, cgroup peak 180,305,920 bytes. Hard aggregate `memory.max=12884901888`, `memory.swap.max=0`; Lean `-j1`, `LEAN_NUM_THREADS=1`. No simultaneous LSP/build. Toolchain and initial KeySort/runtime evidence remain as previously recorded; no budget increases.
* `node scripts/check-automatic.mjs --strict`: PASS, 491 automatic, 61 with step budget, 0 manual, 11 refuted, 0 pending. `bash scripts/check-trust.sh`, `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`, `git diff --check`: PASS. Commands/results are in `capture-static.json` and individual raw logs.
* `bash scripts/check-doc-paths.sh`: FAIL with the same 48 existing missing references. Output SHA256 `01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a` is byte-identical to the exact frozen-base comparison retained earlier. This is not a passing documentation gate.

Independent read-only finder and skeptic reviewed core, controls and narrow registrations without Lean/server/builds. Neither found a soundness defect. Finder requested correction of a restoration-identity docstring that implied it tested names; corrected, and the separate actual duplicate-name control remains. Both explicitly distinguish this prerequisite from call-family compression. No new calculus rule, source representation, dependency or semantic premise was introduced.

This checkpoint is independently usable without VA1 Residue. AU04 actual call-family sharing, bounded complete leaf growth, repeated post-anon repair, forced signed sequential closure, and final full combined-tree gates remain unfinished. The original goal stays incomplete. Shared edits are exactly two additive imports in `Solidity.lean` and two additive module-map rows; the cumulative shared-registration patch is exported separately.


## AU03 signed sequential and target-only intervals (2026-11-01)

Closed the exact previously failing forced `sol_close_join_steps` fixture with `x := -5` and two Boolean-dependent decrements. The current normalized first fact contained endpoints `[-6,-7]` but no interval certificate. The common literal/same-base relative endpoint proof now uses existing `omegaCasesIn`, which first tries the old `omegaIn`, then the existing bounded Boolean cases. A second checked-result probe confirmed the same gap for `[a.val-1,a.val-2]`; the resulting stored certificate is `[-9,-7]`. No numeric budget, case cap, arithmetic premise or semantic observation changed.

A conjunct still failed despite the existing certified `hintA : -9 ≤ a.val ∧ a.val ≤ -7`: `closeArith` selected bounds only for newly introduced hypotheses. It now also selects live existing certificates for variables read by the target, preserving prior hypothesis selection and rejecting stale proof IDs. This constructs ordinary arithmetic proofs; it invents no interval or premise.

`Examples/Tactics/JoinSigned.lean` uses actual producer-stored proofs for first and composed intervals, checks unsigned literals, the exact original forced sequential formula, a parenthesized two-sided forced postcondition, a false tighter bound and a false mis-scoped conjunction through inhabited kernel countermodels, and actual signed underflow. The initially unparenthesized draft incorrectly put the upper bound outside the updates; its exact formula is retained as the refuted scoping control and its raw failure is preserved. A separate new unsigned `uintOfNat 6/7` producer probe refused normalization; the delivered unsigned control uses the actual closer's `CloseS.uintOf` literal form. The earlier refusal remains raw evidence and is not claimed repaired.

The newly routed literal path has direct six-used-Boolean certificates, seven-used-Boolean refusal at the unchanged 64-case cap, and a certificate with twenty irrelevant Booleans. The refusal is optimization metadata, not global refutation. A stale target interval is refused and paired with an inhabited countermodel. Generated cap declarations explicitly resolve type metavariables; the initial harness failed kernel declaration checks and is retained as a failure, regardless of its premature self-reported message.

Validation (actual commands and full invocations in VM location `va2-sharing-artifacts/work` request/runner JSON and raw logs):

* `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-join-signed-audit .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/join-signed-audit.json VM location: va2-sharing-artifacts/work/join-signed-audit-records.json`: PASS, actual file diagnostics and all eleven theorem axiom audits, standard-three subset. 25.407 seconds inside; sampled aggregate visible process RSS 3,083,468 KiB; cgroup peak 1,374,441,472 bytes. MCP's local-instance pattern notice is not a new axiom or Lean diagnostic error.
* `python3 VM location: va2-sharing-artifacts/work/bounded.py signed-interval-affected build Solidity.Examples.Tactics.JoinSigned Solidity.Examples.Tactics.JoinIntervals Solidity.Examples.Tactics.JoinControls Solidity.Examples.Tactics.JoinWalk Solidity.Examples.Tactics.PolySize Solidity.Examples.Tactics.CallSummary Solidity.Examples.ChainNotation Solidity.Examples.Chains.StorageCoverage Solidity.TestSuite.Derived5 Solidity.Calculus.CloseTests Solidity.Examples.Tactics.CallResultCapture`: PASS, 275 jobs, 218.625 seconds inside; sampled aggregate visible process RSS 2,901,956 KiB; cgroup peak 2,139,451,392 bytes. This is affected closure validation, not the final full gate.
* Identical `requests/interval-performance.json` executed through `bounded.py` and `bounded-frozen-base.py`, labels `mcp-interval-performance-current` and `mcp-interval-performance-base`: both structured success, three actual same-base `[2,5]` certificates with standard-three axioms. Base raw heartbeats 779584/759352/758950; current 779827/759961/758856. Base times 69.970/62.485/63.135 ms; current 68.384/57.453/59.974 ms. These small timing samples support only this ordinary fast path, not a general speed theorem. Raw code/hash, records and suite RSS/cgroup peaks are saved; RSS is not measured per row.
* `node scripts/check-automatic.mjs --strict`: PASS, 491 automatic, 61 budgeted, 0 manual, 11 refuted, 0 pending. `bash scripts/check-trust.sh`, `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`, `git diff --check`: PASS; raw `signed-static-*` logs and `signed-static.json`.
* `bash scripts/check-doc-paths.sh`: FAIL, the same 48 references as the exact frozen base; raw SHA256 `01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a`. The byte-identical baseline comparison passes; the checker itself does not.

All Lean jobs were serial `LEAN_NUM_THREADS=1`, explicit `-j1`, with asserted cgroup `memory.max=12884901888`, `memory.swap.max=0`, no simultaneous LSP/build. Existing verified toolchain and passing KeySort evidence remain recorded above. Speed history `cd16cd0d3db5462b68a2c10df5cf575436cc2e4d` and `c98bd4b2fef531e7d2df1733e64983ae14e6f605` was inspected; ordinary-first fallback, shared term traversal and kernel redex cap remain intact.

Independent read-only finder and skeptic reviewed the producer change, target lookup, final source controls and narrow registrations without Lean/server/builds. Neither found a defect; both required measured fast-path/cap coverage and the affected gate, now provided. Evidence: `reviews-signed-interval.md`. Shared edits are one additive root import and one module-map row, exported in the cumulative shared-registration patch.

The exact failed post-anon prototype was archived verbatim with SHA256 as `PostAnonFresh-failed-prototype.lean.txt` before removing its owned scratch file. It generalized Lean proof values, not intrinsic leaf locals, and did not repair the loop. Full AU04 call-family sharing, actual loop repair, complete leaf/walk/time/RSS measurements for that design, and final full combined-tree gates remain open. No whole-assignment completion or runtime speed claim follows from this checkpoint.


## AU04 primitive-anon leaf sharing checkpoint (2026-11-01)

`Calculus/AnonLocalCapture.lean` reuses the exact fresh-head/copy/pop mechanism from `CallResultCapture`. `Positions Γ` is a dependent list of primitive positions, `keys` preserves the original list including repetitions, and `plan m names k xs φ` introduces one fresh intrinsic head per list entry, copies it into the shifted old position, pops it, and continues in the original context. No RHS or postcondition is substituted into another term. `sound` is one-way: the plan establishes the original anon leaf at every typed state and for both modalities. It chooses actual anonymous values in the plan's universal binders. No equivalence, call-family compression, totality or push-free premise is asserted. `plan_size` counts the entire emitted bind/copy/pop syntax: `φ.tmSize + 4 * xs.length`.

The closer recognizes only a reachable literal nonempty primitive anon list through its normal positive prefix. Recognition and emitted accepted goals retain the existing `shareNodes` cap; the emitted-goal check occurs after construction and is not claimed to bound all intermediate construction. Modal/unknown formula shapes refuse the optional leaf entry. Existing numerical proof budgets and split/share limits are unchanged. The new automatic `sol_close_joined_anon_steps` first rejects zero-join leaves cheaply, then invokes the general proved transformation; explicit `sol_close_anon_steps` also supports zero joins. Sequential peeling retains only newly appended proved propositions so a normalized defining relation survives even when no absolute interval was certified. All subsequent arithmetic consumes checked, live proof IDs. SolKey names/shapes and its one-rule-per-statement strategy are unchanged; the new sound transformation is recorded as Lean-only.

### Actual loop measurement and proof boundary

The baseline used the exact original `s <= 1 * i` loop invariant, not the different simplified `s <= i` draft. At frozen base 8bd, its walk is 14 nodes/3 leaves and the largest original whole leaf has 64 term nodes. At the first anon boundary the remainder is 55 nodes, with three positions `(s,s,i)`; the new plan is 66 nodes. That is a larger emitted remainder, not leaf compression. The complete source walk and its original whole-leaf size remain unchanged.

Frozen-base original-whole closure passed (4.7526 seconds / 64.586m raw heartbeats); trying the old closer just past the anon failed (6.6225 seconds / 90.349m raw heartbeats). Raw failures are retained. A failed Lean-proof-local generalization prototype was archived separately and is not an intrinsic-local result.

The paired concrete experiment, before default integration, kernel-checked the original leaf through both routes: old whole closure 4.551744 seconds / 64,651,064 raw heartbeats; intrinsic full reconstruction 1.181506 seconds / 14,340,862 raw heartbeats; transformed remainder closure 0.795622 seconds / 10,395,922 raw heartbeats. The paired source snapshots and SHA256 live in `work/paired-anon-experiment`; they are uncommitted intermediate research inputs, not checked dependency exports.

On the final default-dispatch source, `anon-final-routing-records.json` reconstructs all three original leaves with zero open goals: initial 0.171252 seconds / 1,764,434 raw heartbeats; preservation 1.093330 seconds / 12,794,461; exit 1.093616 seconds / 15,990,984. Explicit intrinsic sharing also kernel-checks preservation and exit, at 1.492348 seconds / 12,785,371 and 0.957329 seconds / 9,507,609. These are individual VM timing samples, not a universal speed theorem. The original source proof uses `sol_prove` followed by ordinary `all_goals (sol_leaf; sol_close)` replay. `sol_prove` alone still leaves two scoped goals; its raw failure remains and no VA1 pipeline claim is made.

The client includes mixed primitive types, duplicate positions and duplicate display names, both modalities, untouched neighbor 13 and balance 5, wrong 14 through a kernel countermodel, empty/no-anon/nonprimitive nested-anon fallbacks, source-loop false tighter postcondition via `sol_refute`, explicit zero-join sharing and identical default closure, and an actually entered impossible profile whose refusal restores the active goal. The refusal is paired with an inhabited kernel countermodel. All sixteen core/client theorem audits use subsets of propext/Classical.choice/Quot.sound. No EVM test or external execution correctness claim is made.

### Confirmed regression, repair and remaining scheduling cost

The first broad integration gate failed the unchanged Derived15 variant/break proof and Derived17 array-length invariant at their existing heartbeat budgets. The owned run was stopped after those failures (exit 137); no final RSS exists because its monitor was stopped. `anon-closure-regressions.*` and `anon-regression-stop.json` remain failures, never PASS.

An actual zero-join variant leaf passes old-order closure (~20.81m raw heartbeats) while the forced intrinsic attempt fails (~11.97m) on a checked subtraction-return side goal. Restoring tactic state does not refund spent heartbeats. The repaired automatic eligibility therefore rejects zero joins. Focused unchanged proofs pass: Derived17 184 seconds, Derived15 98 seconds; the 241-job run takes 300.683 seconds inside, sampled aggregate visible RSS 10,088,304 KiB, cgroup peak 9,868,349,440 bytes. This is within the unchanged 300-second per-module gate; the gate is not a 300-second whole-run limit.

A separate discriminating control uses a walk-only captured current variant leaf (its final assertion has an extra explicit update, unlike the earlier ProofTree-captured leaf) and adds one unused conditional declaration immediately popped before the original formula. It has exactly one joined update outside the anon remainder. The forced attempt still fails normally on checked return: 12,623,389 raw heartbeats. Old-order closure kernel-passes in 22,001,381; default closure kernel-passes via fallback in 33,624,904, about 53% extra. Thus automatic eligibility is not universally beneficial or regression-free. Both actual wrapped proof axiom audits use only the standard three. Source/hash/records: `wrapped-variant-probe.lean.txt`, `wrapped-variant-audit.lean.txt`, `wrapped-variant-source-sha256.json`, `wrapped-variant-records4.json`, `wrapped-variant-audit-records.json`. Earlier stale-import, namespace, mutability, arity and collector heartbeat failures remain raw evidence.

Walk-only collection uses the existing `Walk.walk (close := false)` and exports actual closed leaf propositions, not proof certificates. Four owned research source files were archived with their hashes in `anon-research-sources.tar.gz` / `anon-research-sources-sha256.json` before removal from the checkout. They are not published checked dependencies.

### Checkpoint validation

The exact final affected/import closure PASS: `python3 VM location: va2-sharing-artifacts/work/bounded.py anon-final-affected-closure build SolkeyTestSuite Solidity.Examples.Tactics.AnonLocalCapture Solidity.Examples.Tactics.CallResultCapture Solidity.Examples.Tactics.JoinSigned Solidity.Examples.Tactics.JoinIntervals Solidity.Examples.Tactics.JoinControls Solidity.Examples.Tactics.JoinWalk Solidity.Examples.Tactics.PolySize Solidity.Examples.Tactics.CallSummary Solidity.Examples.ChainNotation Solidity.Examples.Chains.StorageCoverage Solidity.Calculus.CloseTests Solidity.Calculus.PrintedRules Solidity.Examples.Tools`. Decisive output: `Build completed successfully (312 jobs)`, exit 0, 1495.965 seconds inside (1497.34 wrapper), sampled aggregate visible process RSS 10,150,976 KiB, cgroup peak 9,959,985,152 bytes. Exact logs/command/resource footer: `work/anon-final-affected-closure.{log,json}`. Unchanged final Derived15 PASS94s and Derived17 PASS180s; PolySize/CallSummary and original chain/control pins pass.

`node scripts/check-automatic.mjs --strict --build-log VM location: va2-sharing-artifacts/work/anon-final-affected-closure.log`: PASS, 24 TestSuite modules timed, unchanged 300 seconds each; 491 automatic, 61 step-budget, zero manual, 11 refuted, zero pending. Raw evidence `anon-timed-automatic.{log,json}`. This is the completed affected gate, not the remaining final full default-target run.

Final per-file source diagnostics for Steps, Close and the new core/client files PASS. `python3 .../bounded.py mcp-anon-capture-final-audit .venv/bin/python .../mcp_probe_records.py .../requests/anon-capture-final-audit.json .../anon-capture-final-audit-records.json`: PASS, actual diagnostics plus all sixteen theorem audits, 33.385 seconds inside, sampled aggregate visible RSS 4,055,368 KiB, cgroup peak 1,572,220,928 bytes. The local-instance pattern notice is not a Lean error or new axiom. `mcp-anon-unused-join-axioms` PASS verifies the two actual wrapped controls; the forced closure failure remains explicit in the same raw records, not a successful intrinsic proof. Earlier mistaken nonexistent Counterexample target, stale dependency and proof-iteration failures remain failures.

Independent read-only finder and skeptic reviewed core, client controls, eligibility, retained facts and raw regression measurements, without Lean/server/builds or writes. Neither found a soundness defect. Both required the unchanged regression gates and explicit fallback-cost/leaf-shape boundaries, now recorded. Raw reviews: `work/reviews-anon-joined-dispatch.md`. Their source reviews do not replace the passing kernel/build gates. The parent checkpoint is `59d20112a44abe9bd2042b783df4e1f8a66af81d`; the exported revision/manifest bind the resolved committed head.

 Static automation passes 491 automatic + 61 step-budget, zero manual, 11 refuted, zero pending; trust, layers (181 core / zero elaborator), orphans (1047 reachable / zero orphan or not allowed), and diff whitespace checks pass. Documentation paths remain FAIL with the same 48 findings and exact-base SHA256 `01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a`. The baseline comparison passes; the checker does not.

All Lean work uses the same VM's existing Docker runner, asserted `memory.max=12884901888`, `memory.swap.max=0`, `LEAN_NUM_THREADS=1`, explicit Lean `-j1`, at most two configured LSP files, no simultaneous LSP/build. Actual toolchain remains Lean 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b), Lake 5.0.0-src+797c613, with the prior passing KeySort runtime record. Sampled aggregate RSS and cgroup peak are different measurements.

The non-offset doubling-call family still has exponential complete result terms. This loop checkpoint does not implement that call-family sharing. A separate unchecked function-table draft outside the checkout is research only; no simulation oracle, future theorem or new premise is assumed. Full AU04 call-result graph capture, complete size bounds and multi-k walk/leaf/time/RSS measurements, followed by the final full `./run-lean.sh`, timed automatic gate and final audits remain open.


## AU04 partial-function graph prerequisite (2026-11-01)

The independent next component uses existing typed UInt keys and finite ledgers. `Calculus/CallFunctionTable.lean` proves full-domain `realize` and `exists_represents`, injectivity of the encoding `none ↦ -1`, exact `returns_iff`/`failure_iff`, and `composes_iff`/`squares_iff`. `Composes first second next` propagates a first failure and reads the second function at the first returned argument. The transport theorem requires proved `Represents` certificates for both input tables. These are mathematical interfaces to be discharged internally from actual source definitions; they are not new user validity premises. The full-domain witness constructor is private/noncomputable; no tool enumerates, evaluates or materializes the 2^256-entry logical witness.

`Calculus/CallFunctionGraph.lean` encodes that invariant as an actual `Fml C Γ` using existing oldNet positions, two fresh universal UInt positions, and existing KeY-int Boolean comparisons. `holds_compose` proves its exact pointwise semantics in every typed state. `compose_size` counts every quantifier, connective, lookup and argument term: 31 nodes. That is one definition clause only. Base definitions, table binders, terminal application constraints, actual result capture and restoration remain outside this law. It is not a complete call-family leaf bound. The initially unchecked direct-kint-equality draft used a nonexistent Fml signature and guessed 23 nodes; its raw type/size failure is retained. The finished existing Boolean comparison encoding adds eight nodes and proves 31 by kernel reflexivity. No equality constructor, SolKey shape or strategy changed.

The client evaluates actual intrinsic checked terms (`x*3+1`, `x/2`, `1/(x-1)`) and proves distinct returning inputs, first overflow, second-call division failure, successful zero, and noncommuting order (2→7→3 versus 2→1→4). It constructs inhabited represented partial/composed functions, rejects a wrong output, and builds an actual intrinsic graph model with a false-observation countermodel. Caller values 2/99, balance 5 and ledger entry 19 survive the logical table locals. Both quantifier display names intentionally coincide. A separate inhabited malformed-first-table model demonstrates why `Composes` alone cannot justify a representation conclusion. Intrinsic oldNet typing supplies a ledger; it does not supply the partial-function invariant. All fourteen clients and nine public core theorem audits use only subsets of propext/Classical.choice/Quot.sound.

These controls are kernel results on checked terms and typed formula/state models. Option absence is not yet source-call halt correspondence. The fixed initial-state term controls and concrete caller frame do not establish arbitrary-state source simulation, generic fresh-result transport, satisfiable base-definition clauses or a complete universally bound graph leaf under both modalities. The actual source-call bridge, full doubling-call family emission, complete leaf size bounds and multiple-k walk/leaf/time/RSS measurements remain open. No EVM correctness result or full AU04 completion is claimed.

### Gates and resources

- `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-call-function-core-audits .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/call-function-core-audits.json VM location: va2-sharing-artifacts/work/call-function-core-audit-records.json`: PASS, both actual core files' diagnostics plus nine public axiom audits. 11.695 seconds inside; sampled visible aggregate RSS 3,559,444 KiB; cgroup peak 1,354,407,936 bytes.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-call-function-client-audits .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/call-function-client-audits.json VM location: va2-sharing-artifacts/work/call-function-client-audit-records.json`: PASS, final actual client diagnostics and fourteen axiom audits. 8.178 seconds inside; sampled visible aggregate RSS 2,731,008 KiB; cgroup peak 1,243,754,496 bytes.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py call-function-prerequisite-affected build Solidity.Calculus.CallFunctionTable Solidity.Calculus.CallFunctionGraph Solidity.Examples.Tactics.CallFunctionTable`: PASS, `Build completed successfully (171 jobs)`, exit 0, 1.914 seconds inside; sampled visible aggregate RSS 979,660 KiB; cgroup peak 206,516,224 bytes.
- `node scripts/check-automatic.mjs --strict`, `bash scripts/check-trust.sh`, `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`, `git diff --check`: PASS; 491 automatic + 61 budgeted, zero manual, 11 refuted, zero pending; trust 1065 sources / zero findings; layers 181 core / zero elaborator; orphans 1050 reachable / zero orphan or not allowed. Exact commands/output/hashes in `call-function-static.json` and raw logs.
- `bash scripts/check-doc-paths.sh`: inherited FAIL, exact same 48 findings/output SHA256 `01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a`. The baseline comparison passes; the checker does not.

The 265 local modules in the TestSuite import closure are byte-identical to passing checkpoint 90c4499c65eceaeb1c9a341fcb9ab8de73f01ceb (`call-function-testsuite-closure-unchanged.json`). This is dependency bookkeeping, not a fresh TestSuite kernel run. No unchanged 25-minute gate was repeated. The earlier timed affected gate remains recorded at its exact checkpoint; the final full default-target run is still pending. New modules are registered by three narrow additive root imports and three module-map rows; the graph definition clause has a Lean-only correspondence row.

All jobs retain actual memory.max=12884901888 / memory.swap.max=0, LEAN_NUM_THREADS=1 and explicit Lean -j1, no simultaneous LSP/build, at most two configured LSP files (core and client audits use separate serial jobs). Existing Lean 4.24.0 / Lake 5.0.0-src+797c613 and passing KeySort runtime evidence remain applicable. Earlier stale-import, beta-rewrite, reserved-keyword and record-layout failures remain raw failures. Speed-motivated history 00a88bb99a82b93fa6cf4c42b3f317134e440f4a and 3dbf353adecb7a52543f33a7700430a48a7e0b93 was inspected; existing literal folding and strict redex sharing are unchanged.

Independent read-only finder and skeptic reviewed the actual mathematical and intrinsic modules, controls and boundaries without Lean/server/builds/writes. Neither found a logical defect. Finder requested the malformed-predecessor control; it is included and kernel-checked. Both require the source invariant to be proved internally and the 31-node clause to remain distinct from a whole leaf bound. Final handoff/source review evidence is bound in the checkpoint package. Parent: 90c4499c65eceaeb1c9a341fcb9ab8de73f01ceb; the exported revision/manifest bind the resolved full head. Full assignment remains incomplete.


## AU04 arbitrary-prefix result restoration prerequisite (2026-11-01)

`Calculus/CallResultRestore.lean` restores the caller's original intrinsic context after any typed fresh prefix. `copyDrop h j r : Upd C Δ Γ` reads the primitive result at `r : Idx Δ (.val p)`, writes only the old `j.ext h`, and uses the existing typed bulk pop. `env_drop_set`, `state_drop_set` and `locals_drop_set` preserve exact environments, global/heap state and virtual reads; `copyDrop_applyV` gives its actual evaluation. `holds_copyDrop` proves exact equivalence for both modalities and every old-context continuation, including modal continuations, without a validity, totality or heap premise. `target_fresh` excludes aliasing an additionally pushed result head; `copyDrop_exh` is false.

`leaf` connects actual result capture directly to that restoration. `holds_leaf_of_eval` transports the checked returning value into the exact caller; its evaluation premise is a branch fact to prove internally. `holds_leaf_of_none` retains the exact old disjunction `m.onHalt ∨ capture.exh = true`, including diamond exhaustion. No halt observation or source validity premise was weakened. These are update/leaf laws; source-call halt correspondence remains open.

The structural update size is 2; the complete capture/copy/drop formula counts the result term and post once, `t.size + φ.tmSize + 5`. Context/Ext metadata is outside that existing metric. The concrete mixed prefix has depth 5, accounted for separately, and the complete actual term/post fixture has 32 nodes. These laws do not compress an already-expanded term or establish complete graph-family growth.

Actual clients evaluate two checked non-offset applications to 22 at a non-head old target, with neighbor 99, balance 5 and global ledger value 19 preserved while a distinct ghost ledger contains -77. They test a mixed int/oldNet/kint/bool/result prefix, changed result, false result, wrong target, positional freshness, actual prefix depth, signed -7 and Boolean true under both modalities. The final `endToEnd` client feeds the checked capture directly into restoration; it does not construct a separate literal-valued restored input state. Selected division-by-zero establishes false under box and is refuted even for true under diamond. Generic exhaustion-true transport is proved; no concrete exhaustion-positive fixture is claimed. All 27 core/client theorem audits use subsets of propext/Classical.choice/Quot.sound. No EVM result is asserted.

### Gates and review

- `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-call-result-restore-audits .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/call-result-restore-audits.json VM location: va2-sharing-artifacts/work/call-result-restore-audit-records.json`: PASS, both actual files' diagnostics and all 27 theorem audits. 13.102 seconds inside; sampled visible aggregate RSS 3,462,848 KiB; cgroup peak 1,450,221,568 bytes.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py call-result-restore-affected build Solidity.Calculus.CallResultRestore Solidity.Examples.Tactics.CallResultRestore`: PASS, `Build completed successfully (172 jobs)`, exit 0, 1.912 seconds inside; sampled visible aggregate RSS 978,776 KiB; cgroup peak 207,486,976 bytes.
- `node scripts/check-automatic.mjs --strict`, `bash scripts/check-trust.sh`, `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`, `git diff --check`: PASS, automation 491+61 / zero manual / 11 refuted / zero pending; trust 1067 sources / zero findings; layers 181 core / zero elaborator; orphans 1052 reachable / zero orphan or not allowed. Exact commands/output/hashes: `restore-static.json` and raw logs.
- `bash scripts/check-doc-paths.sh`: inherited FAIL, same 48 findings and frozen-base SHA256 `01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a`. Checker remains FAIL; baseline comparison passes.

The TestSuite's 265 local import-closure files are byte-identical to ce55ee6e9cdbbefe5a333fcdbf3b2540774d6beb (`restore-testsuite-closure-unchanged.json`), dependency bookkeeping rather than a fresh kernel run. No unchanged heavy full gate was repeated. All actual Lean jobs keep memory.max=12884901888 / memory.swap.max=0, LEAN_NUM_THREADS=1, explicit -j1, at most two LSP files and no simultaneous LSP/build. Toolchain and passing KeySort evidence remain as previously recorded. Raw failed induction syntax, virtual-value/projection proof, Ext-versus-Thin and private-definition rewrite attempts are retained; only final actual diagnostics/builds establish PASS.

Independent read-only finder and skeptic reviewed the generic and composed transport laws and controls without Lean/server/builds/writes. Neither found a defect. Finder requested direct capture-to-restoration coverage; the end-to-end and paired failure controls now pass. Both require the structural-size/context distinction and exact nonreturn/exhaustion condition to stay explicit. The checkpoint adds two root imports, two module-map rows and one Lean-only logical transport row; no calculus datatype or SolKey strategy changes. The parent is ce55ee6e9cdbbefe5a333fcdbf3b2540774d6beb; exported revision/checksums bind the actual committed head.

Next: satisfiable intrinsic base definitions with internally proved representation invariants, actual source-call transport and call-family leaf construction, full payload/context accounting and multi-k walk/leaf/time/RSS measurements, then final full bounded ./run-lean.sh and full-assignment reviews/gates. Those obligations remain unfinished; these independently checked prerequisites do not complete AU04.


## AU04 satisfiable denotation base definitions (2026-11-01)

`Calculus/CallFunctionBase.lean` supplies an actual intrinsic definition for a UInt base term. The term is typed before the fresh oldNet local exists; `Thin.keep/drop` inserts the table below its input and a further result binder above it. `result_reads` proves that neither inserted slot changes the original term's reads at any typed state. This rules out self-referential table definitions structurally, including reads of original caller locals.

The clause constrains every returning observation and explicitly forces -1 when no primitive result is denoted. `represents_iff_observations` and `holds_clause` establish exact representation of the actual term denotation. `satisfiable` constructs an inhabited definition at every original state without any agreement or validity premise. Logical full-domain witnesses remain opaque/private and are never enumerated. `holds_clause_eval` separately uses the existing checked `agreeB` certificate to connect operational evaluation; the producer must discharge that certificate internally. Denotation and evaluation are not assumed equal universally, and no new user validity/hash premise is granted.

`term_size_wk` preserves actual term structure under typed thinning. `clause_size = 2*t.size+24` includes both explicit term occurrences and every quantifier/connective/Boolean comparison. The complete actual five-node base term yields 34 nodes. These are base-definition sizes only; function-table binders, composition stages, terminal call-result use and context metadata/full-family bounds remain separate.

The client reads original caller factor 3/offset 1 under input/result/table slots, checks results 7/10 and genuine overflow, constructs an inhabited actual definition, rejects individual corrupted returning and overflowing entries, rejects an empty ledger for that nonconstant function, and preserves caller/global frame observations. A total constant-zero term has the concrete empty-ledger model; replacing a successful-zero entry by failure is rejected. Both binder names deliberately coincide. All eleven client and seven core theorem audits use standard-three subsets; the explicit agreement certificate for the actual arithmetic term is checked by reflexivity. These are kernel term/formula/state results, with no EVM or source-call-family completion claim.

### Gates and boundaries

- `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-call-function-base-audits .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/call-function-base-audits.json VM location: va2-sharing-artifacts/work/call-function-base-audit-records.json`: PASS, both actual files' diagnostics and all eighteen axiom audits. 12.306 seconds inside; sampled visible aggregate RSS 3,620,960 KiB; cgroup peak 1,411,936,256 bytes.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py call-function-base-affected build Solidity.Calculus.CallFunctionBase Solidity.Examples.Tactics.CallFunctionBase`: PASS, `Build completed successfully (170 jobs)`, exit 0, 1.712 seconds inside; sampled visible aggregate RSS 966,516 KiB; cgroup peak 192,577,536 bytes.
- `node scripts/check-automatic.mjs --strict`, `bash scripts/check-trust.sh`, `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`, `git diff --check`: PASS, automation 491+61/zero manual/11 refuted/zero pending; trust 1069 sources/zero findings; layers 181 core/zero elaborator; orphans 1054 reachable/zero orphan or not allowed. Exact commands/output/hashes: `base-static.json` and raw logs.
- `bash scripts/check-doc-paths.sh`: inherited FAIL with 48 findings, frozen-base output SHA256 `01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a` unchanged. Baseline comparison passes; checker remains FAIL.

The TestSuite’s 265 local import-closure files remain byte-identical to parent 1efce54463471e55ad33e57029a0c164a7adaa6b (`base-testsuite-closure-unchanged.json`); this is bookkeeping, not a fresh kernel run. No unchanged heavy gate was repeated. Every Lean job retains hard memory.max=12884901888 / memory.swap.max=0, single-thread/-j1, at most two LSP files and no simultaneous build/server. Actual Lean 4.24.0/Lake 5.0.0-src+797c613 and passing KeySort remain in runtime evidence. The failed broad simplification and list-alias field-notation attempts remain raw failures; final exact typed proof/qualified accessors and actual diagnostics establish the passes.

Independent read-only finder and skeptic reviewed the actual clause/model/weakening/size proofs and controls without Lean/server/builds/writes. Neither found a defect. Finder requested total-constant and successful-zero controls; both are included and kernel-checked. Both require operational agreement to be a producer fact or ordinary fallback, never a new user validity premise. Narrow registrations add two root imports, two module-map rows and one Lean-only definition row; no calculus datatype, SolKey shape/strategy or expected source verdict changed. Exported revision/checksums bind this checkpoint's resolved head; parent 1efce54463471e55ad33e57029a0c164a7adaa6b.

Remaining: an operational definition route for eligible terms not covered by the denotation-agreement certificate, internally proved source-call halt/evaluation transport, complete family emission and multi-k full leaf/context/time/RSS measurements, final full bounded run and assignment-wide reviews/gates. Those obligations stay open; the original goal is incomplete.


## AU04 operational base definitions (2026-11-01)

`Calculus/CallFunctionOperationalBase.lean` defines tables by actual operational capture, without a theory/evaluation agreement premise. At every quantified UInt input the box capture constrains returning results, while failure of the diamond capture selects code -1. `capture_of_eval` uses actual typed landing; `capture_of_none` retains `m.onHalt ∨ capture.exh = true` exactly. `capture_noExh` derives non-exhaustion from the existing checked no-push certificate. `summary_term_pushFree` obtains that certificate from a concrete successful existing `CallRet.summary?` equation and `summary_agrees`; clients must establish that producer equation internally, never assume a new user validity premise. No-push is essential to distinguish ordinary nonreturn from exhaustion.

`input_eval` and `pushFree_wk` establish operational independence of the fresh oldNet slot. The term is typed before that slot exists. `holds_clause` proves exact representation of `fun x => t.eval (σ.push x)` and `satisfiable` constructs a real table model for every original state with a no-push certificate. No future theorem, simulation oracle or VA1 premise is used. Full-domain witnesses stay logical and are not enumerated. `clause_size = 2*t.size+22` counts both captures, both term occurrences and all wrappers; it is one base clause, not a whole family bound.

Fourteen client theorems check actual caller factor 3/offset 1, distinct 7/10 returns and checked overflow, an inhabited model, separate returning/failing entry corruption, successful zero versus failure, caller/global frames and the complete 32-node arithmetic clause. An actual partial array read has `agreeB=false`, `pushFree=true` and evaluation None; its operational definition is inhabited and rejects a false successful-zero entry. This demonstrates absence of an agreement certificate, not a proved discrepancy of theory and evaluation at that state. The earlier guessed theory value failed kernel reflexivity and remains a raw failure. No source or EVM equivalence is asserted.

### Checkpoint gates and reviews

- `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-operational-base-audits .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/operational-base-audits.json VM location: va2-sharing-artifacts/work/operational-base-audit-records.json`: PASS, both actual file diagnostics and all 25 public theorem audits, standard-three subsets only. 17.845579 seconds inside, sampled visible aggregate RSS 3,668,060 KiB, cgroup peak 1,413,931,008 bytes. The client docstring word opaque triggers a text-pattern notice, not an axiom or declaration. MCP cleanup event-loop warning followed actual successful results/exit 0.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py operational-base-affected build Solidity.Calculus.CallFunctionOperationalBase Solidity.Examples.Tactics.CallFunctionOperationalBase`: PASS, Build completed successfully (175 jobs), 1.709617 seconds inside, sampled visible aggregate RSS 983,252 KiB, cgroup peak 196,460,544 bytes.
- `python3 VM location: va2-sharing-artifacts/work/checkpoint-static.py operational-base`: strict automation/trust/layers/orphans/whitespace PASS: 491 automatic +61 budgeted/zero manual/11 refuted/zero pending; 1071 sources/zero trust findings; 181 core/zero elaborator; 1056 reachable/zero orphan or not allowed. Documentation paths retain inherited FAIL48, exact frozen-base output SHA256 01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a. Comparison passes, checker fails. Raw commands/output retained in operational-base-static.json.

Both independent read-only reviewers found no defect; no Lean/server/build/write used. Their suggested concrete summary-certificate and exhaustion-boundary clients remain optional unclaimed coverage. Review evidence is work/reviews-operational-base.md. Stale-dependency and initial probe failures remain raw failures. The existing TestSuite local import closure is byte-identical to parent 2efa5d31ab9b633180b2c216572d090ed0316c90 (dependency bookkeeping, not a new kernel run). All actual Lean jobs assert hard memory.max=12884901888 / memory.swap.max=0, LEAN_NUM_THREADS=1 and -j1, at most two files, no simultaneous build/LSP. Actual Lean 4.24.0/Lake 5.0.0-src+797c613 and prior passing KeySort remain unchanged runtime evidence.

Narrow registrations add the two root imports, adjacent module-map rows and one Lean-only correspondence row; no SolKey calculus constructor/shape/strategy or expected verdict changed. Exported immutable bundle/source/module hashes bind the actual committed head; parent is 2efa5d31ab9b633180b2c216572d090ed0316c90.

Full source-call evaluation/halt transport, complete call-family leaf construction and bounds, multi-k walk/leaf/context/time/RSS measurements and the final full bounded run/reviews remain open. This is an independently proved producer component, not full AU04 completion; the original full goal remains incomplete.


## AU04 complete intrinsic function-family leaves (2026-11-01)

`Calculus/CallFunctionLeaf.lean` constructs a complete intrinsic leaf, not just a graph clause. The base table is constrained by the checked operational clause; each doubling level binds one fresh oldNet local and guards the remaining continuation by the actual 31-node composition clause. The terminal binds one fresh UInt result, selects its exact represented code, copies it into the old target and bulk-drops all new locals before the unchanged old-context post. No new Fml/Proves/SolKey constructor, strategy change or external dependency is introduced.

`holds_terminal`, `holds_stages` and `holds_leaf` give exact both-modality semantics for every typed original state and arbitrary old-context post, including program modalities. The forward proofs explicitly choose actual represented tables for the base and every composition; universally guarded definitions cannot be vacuous. Reverse proofs derive each representation invariant from actual clauses. `power_succ` proves the ordered equation `power f (k+1) x = (power f k x).bind (power f k)`, retaining first/later failure. Each base application reads the same original captured caller. The existing base no-push certificate excludes exhaustion internally; it is not a new user validity/hash premise. Actual source transport must establish its summary/evaluation facts and captured-state invariance internally.

The complete emitted formula-size law is `2*t.size + φ.tmSize + 33*k + 44 + (haltPost m).tmSize` (haltPost size 1 box / 2 diamond). Every base occurrence, table binder, composition, result binder, terminal guard, restoration update and post is counted. `Calculus/CallFunctionLeafMetrics.lean` separately proves actual maximum formula-context length at most `max (Γ.length+k+3) (contextPeak φ)`. This metric measures Fml/update boundaries and excludes program interiors, internal intermediate update contexts, total context/index annotation volume and kernel-expression bytes. It is not a claim of linear total annotation volume or checking time.

Clients check actual checked arithmetic x*3+1 whose factor/offset are old caller locals, at k=0…5 with results 7,22,202,16402,107616802,4632550472129602. Both modalities certify the complete emitted leaf. Wrong output203vs202 is refuted. Target=input and target=coefficient controls keep intermediate reads in the original caller, assigning only at the end. First/later checked division failures, successful zero, box/diamond contrast, same display names and preserved neighboring inputs/coefficients are covered. `modalPost` is an update continuation; `programModalPost` additionally uses actual Fml.modal with typed empty program/frames. Actual full client leaf node pins are 70,103,136,169,202,235; corresponding maximum formula-context lengths 7,8,9,10,11,12.

### Measurements and gates

The external actual-construction probe uses a smaller fixed two-local caller and a three-node post, hence sizes differ from the richer client. At k=0,1,2,3,4,5,6,7,8,16,32 it emits 58,91,124,157,190,223,256,289,322,586,1114 nodes, with context peaks 5,6,7,8,9,10,11,12,13,21,37. An IO-ref supplies the level after timing starts, and an effectful sink commits both measured results before timing stops. For 1000 constructions/measurements, nanoseconds were 41071754,54282696,55726402,81156858,110611920,120031549,118677394,165186568,171366873,289816090,586338895. These are one VM samples including IO/ref overhead, not universal speed laws. The earlier pure-let microtimings were rejected as uninformative and remain raw evidence.

These emitted leaves are semantic-family construction/control results. The existing source non-offset call walk still has its previously measured five nodes and exponentially expanded old leaf (26,34,50 at k=1,2,3); no new source dispatch or walk measurement is claimed. Comparing different caller/post fixtures is not evidence of source equivalence. Actual source/summary correspondence and automatic selection remain open.

- `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-call-function-leaf-audits .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/call-function-leaf-audits.json VM location: va2-sharing-artifacts/work/call-function-leaf-audit-records.json`: PASS, all three file diagnostics plus 29 public theorem audits, standard-three subsets. 31.063941 seconds inside, sampled visible aggregate RSS 4326996 KiB, cgroup peak 2150547456 bytes.
- `python3 .../bounded.py mcp-call-function-leaf-program-modal .venv/bin/python .../mcp_probe_records.py .../requests/call-function-leaf-program-modal.json .../call-function-leaf-program-modal-records.json`: PASS, final client diagnostics plus new program-modal axiom audit (30 total theorems), standard-three. 11.181571 seconds inside, RSS3366428 KiB, cgroup1899945984 bytes. Paths abbreviated only here; actual expanded command is in the matching JSON/log.
- `python3 .../bounded.py mcp-call-function-leaf-runtime-measurement .venv/bin/python .../mcp_probe_records.py .../requests/call-function-leaf-runtime-measurement.json .../call-function-leaf-runtime-measurement-records.json`: PASS, actual structured success true and output above. 6.045600 seconds inside, RSS1719548 KiB, cgroup921104384 bytes. This #eval is an external runtime measurement, not a kernel theorem; separate kernel pins cover k=0…5.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py call-function-leaf-affected build Solidity.Calculus.CallFunctionLeaf Solidity.Calculus.CallFunctionLeafMetrics Solidity.Examples.Tactics.CallFunctionLeaf`: PASS, Build completed successfully (178 jobs), 4.933607 seconds inside, RSS1124272 KiB, cgroup367828992 bytes.
- `python3 VM location: va2-sharing-artifacts/work/checkpoint-static.py call-function-leaf`: strict automation/trust/layers/orphans/whitespace PASS: 491 automatic+61 budgeted/zero manual/11 refuted/zero pending; 1074 sources/zero trust findings; 181 core/zero elaborator;1059 reachable/zero orphan or not allowed. Doc paths inherited FAIL48 with exact-base SHA256 01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a. Comparison passes; checker fails. Expanded commands/output/hashes are retained in call-function-leaf-static.json.

The Corpus/TestSuite local import closure is byte-identical to parent 97fbbd6cf56dce94c208194b248da63cb1ffaef3 (dependency bookkeeping, not a new kernel/full run). Per-file diagnostics/axiom audits and all affected builds use hard memory.max12884901888/swap.max0, LEAN_NUM_THREADS1/-j1, at most two LSP files, no simultaneous build/LSP. Actual Lean4.24.0/Lake5.0.0-src+797c613 and passing KeySort remain in runtime records. Failed direct rfl six-level evaluation at unchanged200k heartbeats, initial modality/forall proof repairs and the BaseIO probe failure are retained; final exact proofs/structured successes establish the passes.

Both independent read-only finder/skeptic reviews found no defect, no Lean/server/build/writes; their requested alias/failure/zero/context and program-modal controls are included. Review evidence work/reviews-call-function-leaf.md. Narrow registrations add three root imports, three module-map rows and one Lean-only logical-construction row. The exported immutable patch/bundle/source/manifest bind this committed checkpoint; parent97fbbd6cf56dce94c208194b248da63cb1ffaef3.

Remaining full assignment work: actual old-summary/source-call correspondence, internal eligibility/capture invariants and automatic concrete family selection, matching multi-k source walk/old-and-new leaf/context/time/RSS measurements, then final full bounded ./run-lean.sh, timed automatic gates and final assignment-wide reviews. The new complete-leaf laws do not assume a future bridge or complete AU04. An external term-transport draft is unchecked research only until separately checked/committed. The original full goal remains incomplete.


## AU04 actual expanded-summary and typed source-call transport (2026-11-01)

`Calculus/CallFunctionTermPower.lean` connects the complete shared leaf to actual old intrinsic terms and actual typed calls. `inst?` is existing `Tm.substE` with an intrinsic `Thin` and `SEnv.idAt`, keeping original captured caller locals/globals. `eval_inst` preserves success and proves that a failed argument still fails where the base's checked `strictReads 0` certificate is true. `pushFree_inst` and `pushFree_expanded` reuse existing value-only/no-push certificates. All producer flags/equations must be checked internally, not granted as new user validity/hash premises.

`expanded?` constructs an actual old term for certificate comparison; it is not the emitted leaf. `iterate_add`/`power_iterate` prove exactly 2^k ordered Option applications, and `eval_expanded_power` transports actual old-term evaluation at every typed caller state. `holds_assignment` proves exact equivalence between the full emitted shared leaf and the actual old assignment for either modality and any old-context post. Failure/exhaustion is preserved via internally proved no-push evidence; strictness is not silently assumed.

`summary_ends` derives actual call termination and non-exhaustion from the concrete successful existing `CallRet.summary?` construction, using existing `CallRet.sym_call`/`Prog.sym_sound`. It does not infer termination from update agreement alone. `run_of_summary_eval` reconstructs the exact whole returned caller (globals, heap, every indexed local) from actual checked summary evaluation, excluding every error case explicitly. `holds_call` gives exact both-direction source observation; `sound_call` uses the actual summary/expansion equations to transport arbitrary remaining program/frames through existing `Premise.sound_callSummary`. Its continuation is the existing rule's exact `modalK` representation. No new calculus/Proves/SolKey constructor or one-rule strategy change.

The client constructs real intrinsic typed call bodies: body0 assigns checked x*3+1, body(k+1) calls the preceding body first at its input and then at the returned result. Actual existing summary certificates pass at k1/2/3, and expansion certificates at k0…3. Both-modality source proofs at k1/2/3 use the complete shared leaf plus these concrete certificates. `assignmentTwo` covers all caller states/posts. Actual whole returned state, balance5, ledger19, input2, wrong source result203vs202 and genuine source overflow/revert with box/diamond contrast pass. A nonstrict constant really drops a failed argument under substitution, and its strict-read flag is false; a same-named different body really returns0 and is rejected against the expected22 summary. These are typed source-body witnesses, not yet frontend-parsed original contracts or automatic matcher integration. No EVM test/result is claimed.

### Matching typed-family measurements

The external runtime-input probe constructs actual typed bodies, existing old summaries, actual expanded terms and the full new leaf for the same two-local caller/fixed seven-node post. It does not perform kernel proof checking or an automatic walk. Ten constructions per k include an effectful runtime level read and output sink; measured nanoseconds are aggregate batch costs, not single-call latency.

| k | Typed body nodes | Actual old summary leaf nodes | Actual expanded term nodes | Emitted whole shared leaf nodes | Formula context peak | Ten combined constructions ns |
|---|---:|---:|---:|---:|---:|---:|
|0|9|none (existing no-call fallback)|5|62|5|2113498|
|1|26|18|9|95|6|1834375|
|2|60|26|17|128|7|2754097|
|3|128|42|33|161|8|5634491|
|4|264|74|65|194|9|12287890|
|5|536|138|129|227|10|25519347|
|6|1080|266|257|260|11|52569220|
|7|2168|522|513|293|12|114873714|
|8|4344|1034|1025|326|13|247946899|

The new leaf is larger throughk5 and smaller fromk6 in this fixture. Emitted formula syntax grows by33 per level; original summary/expansion construction still grows roughly exponentially at largerk. That cost is not repaired by compact leaf emission and remains a producer/selection concern. The full-domain tables remain logical witnesses, never enumerated. Context peaks are separate from kernel bytes/total annotation volume. Actual source walk measurements are still the earlier five-node parsed-call controls; no new default/shared walk measurement is claimed here. Large-k rows are external runtime samples, while concrete kernel source certificates cover k1…3 and earlier semantic leaf clients coverk0…5.

### Gates, resources and review

- `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-call-function-term-power-audits .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/call-function-term-power-audits.json VM location: va2-sharing-artifacts/work/call-function-term-power-audit-records.json`: PASS, both actual files and all27 public source/transport theorem audits, standard-three subsets.20.566623 seconds inside, sampled visible aggregate RSS3870744KiB, cgroup1644253184bytes.
- `python3 .../bounded.py mcp-call-function-transport-final-types .venv/bin/python .../mcp_probe_records.py .../requests/call-function-transport-final-types.json .../call-function-transport-final-types-records.json`: PASS, final actual core/client/metrics diagnostics and four changed-proof audits after explicit have annotations (two source proofs repeated, two affected context laws), standard-three subsets.19.175143seconds inside, RSS3901228KiB, cgroup1722814464bytes. Expanded commands retained in the matching JSON/log; no proof budget changed.
- `python3 .../bounded.py mcp-call-function-certificate-measurement .venv/bin/python .../mcp_probe_records.py .../requests/call-function-certificate-measurement.json .../call-function-certificate-measurement-records.json`: PASS, actual structured success true and rows above.5.038175seconds inside, RSS1729636KiB, cgroup935178240bytes. This is an external #eval measurement, not a kernel theorem or EVM run.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py call-function-transport-affected build Solidity.Calculus.CallFunctionTermPower Solidity.Calculus.CallFunctionLeafMetrics Solidity.Examples.Tactics.CallFunctionTermPower Solidity.Examples.Tactics.CallFunctionLeaf`: PASS, Build completed successfully (180 jobs),7.951906seconds inside,RSS1118120KiB,cgroup355524608bytes.
- `python3 VM location: va2-sharing-artifacts/work/checkpoint-static.py call-function-transport`: strict automation/trust/layers/orphans/whitespace PASS,491automatic+61budgeted/zero manual/11refuted/zero pending;1076sources/zero trust findings;181core/zero elaborator;1061reachable/zero orphan or notallowed. Docpaths inherited FAIL48, exact-base outputSHA256 01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a; comparisonpasses/checkerfails. Expanded commands/rawoutput/hashes in call-function-transport-static.json.

The Corpus/TestSuite import closure is byte-identical to parentd5a6e85e9242b42c37c226aa2dc96e88da7f908a (bookkeeping, not a new full/kernel run). Every Lean job asserts memory.max12884901888/swap.max0, LEAN_NUM_THREADS1/-j1, at most two LSP files, no simultaneous build/LSP. ActualLean4.24.0/Lake5.0.0-src+797c613 and passingKeySort remain in runtime evidence. Sampled aggregate visible RSS differs from actual cgroup peak. Raw type/elaboration/proof failures, the exact-modalK correction and unchanged200k direct-whole-run reduction timeout are retained. The latter is a failed proof attempt, not a source runtime failure.

Independent read-only finder/skeptic source reviews and follow-ups found no defect, no Lean/server/build/writes. Required strictness, changed-body, exact source run/frame/wrong-post/failure controls are included. Review evidence work/reviews-call-function-transport.md. Narrow registrations add two root imports, two module-map rows and one Lean-only correspondence row; two existing metric proofs gain explicit have types only. The immutable checkpoint patch/bundle/source/manifest bind its resolved committed head, parentd5a6e85e9242b42c37c226aa2dc96e88da7f908a.

Remaining: checked plan production and automatic matching/selection against actual frontend-generated/normalized call terms, bounded producer/certificate costs or precise ordinary fallback, matching multi-k parsed source walk/old/new leaf/context/time/RSS controls, and final full bounded ./run-lean.sh/timed automatic/assignment-wide audits and reviews. An external checked-plan draft is not yet proved/exported code. The full original goal remains incomplete; no VA1 Decision/Residue theorem, AU05/6/compiler/ABI/function-ref work or new semantic exclusion is assumed or taken.


## AU04 checked intrinsic plan production (2026-11-01)

`Calculus/CallFunctionPlan.lean` produces an actual checked plan indexed by the exact old intrinsic result term. `checked? base level input out` checks existing pushFree/valueOnly/strictReads facts, computes an actual typed expansion and compares it with `out` using existing proved `Tm.beqR` equality. A successful `Plan out` stores the real expansion equation. `Plan.holds` gives exact old-assignment semantics for every typed state/post and both modalities; `Plan.size` counts the complete emitted formula. No callee name, future interface or simulated oracle is trusted, and no new user validity/hash premise is introduced.

The producer adds input-derived resource guards, not an option: base.size≤out.size and level≤log2(out.size) before exponentiation, then2^level≤out.size. `boundedExpansion?` refuses any retained intermediate exceeding out.size. `boundedExpansion_eq` proves each accepted result has the exact original expansion equation; `boundedExpansion_size` proves its retained-term limit. `checked_bounds` ties actual returned-plan base/level/step limits to a successful checker equation. Arbitrary manually constructed Plans need not satisfy those resource guards, and unrestricted public boundedExpansion? accepts an explicit n. The checker resource facts do not bound pending recursive stack, transient substitution allocation before size checking, preliminary eligibility traversals, aggregate memory, total proof payload, kernel bytes or checking time. Hard process-group memory/swap limits remain enforced separately.

Clients prove actual checker acceptance atk0…4, a nonempty accepted Plan result, both-modality returning observations through actual capture/restoration and a wrong-observable rejection. Actual metadata matches base size5/input index1/level2. Wrong level/input, changed arithmetic and reversed operations refuse. A syntactically matching nonstrict constant refuses; push-bearing reads refuse; a snapshot read with passing pushFree/strict flags but valueOnlyfalse independently refuses. Intermediate limit8 rejects the actual9-node term while9 accepts it. Proposed level1000 refuses before computing its power or expansion. Returning Option.none is optimization refusal only; consumer/default fallback integration remains unfinished.

### Actual producer measurements and gates

The external IO-input/effectful-sink probe builds old terms, invokes the real guarded checker and measures actual returned-plan leaf/context sizes. It accepts runtime samplesk0…8 with old term sizes5,9,17,33,65,129,257,513,1025; full plan leaf nodes58,91,124,157,190,223,256,289,322; formula-context peaks5…13. Ten old-term/checked-plan/leaf constructions cost respectively3282640,1082943,1789760,2577897,4825485,10975551,31172796,82812298,310135885ns. These are aggregate VM samples including runtime IO and measurements, not per-source-call latency or kernel checking. They show substantial producer cost growth with expanded input; retained-step bounds are not a cheap-certificate claim. Earlier source walk counts remain unchanged and are not rebranded as this producer's leaf measurements.

- `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-call-function-plan-audits .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/call-function-plan-audits.json VM location: va2-sharing-artifacts/work/call-function-plan-audit-records.json`: PASS, final actual core/client diagnostics and all18 theorem audits, standard-three subsets.17.674017seconds inside, sampled visible aggregateRSS3740012KiB, cgroup1485418496bytes.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py call-function-plan-affected build Solidity.Calculus.CallFunctionPlan Solidity.Examples.Tactics.CallFunctionPlan`: PASS, Build completed successfully (179 jobs),2.415086seconds inside,RSS996396KiB,cgroup219578368bytes.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-call-function-plan-measurement .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/call-function-plan-measurement.json VM location: va2-sharing-artifacts/work/call-function-plan-measurement-records.json`: PASS, structuredsuccess true and actual values above.4.037231seconds inside,RSS1651104KiB,cgroup840085504bytes. This #eval is an external runtime sample; separate kernel client pins establish actual accepted/refused cases and semantic controls.
- `python3 VM location: va2-sharing-artifacts/work/checkpoint-static.py call-function-plan`: strict automation/trust/layers/orphans/whitespace PASS491automatic+61budgeted/zero manual/11refuted/zero pending;1078sources/zero trust findings;181core/zero elaborator;1063reachable/zero orphan/notallowed. Docpaths inherited FAIL48, frozen-base outputSHA256 01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a unchanged; comparisonpasses/checkerfails. Exact commands/output/hashes retained in call-function-plan-static.json.

Corpus/TestSuite import closure remains byte-identical to parente9ff191446abba7dc633860bae13db3206698fe5; this is dependency bookkeeping, not a fresh full/kernel gate. All actual Lean jobs assert memory.max12884901888/swap.max0, LEAN_NUM_THREADS1 and-j1, max2LSPfiles/no simultaneous build/LSP. ActualLean4.24.0/Lake5.0.0-src+797c613 and prior passingKeySort remain in runtime evidence. Raw initial update-post parenthesis error remains a failure; only final actual diagnostics/audits/builds establishPASS. Sampled aggregate RSS and cgroup peak are separate measures.

Independent read-only finder/skeptic reviews/follow-ups found no defect and used no Lean/server/build/writes. They requested distinct value-only refusal and precise guard/allocation/stack boundaries; these are included. Review evidence work/reviews-call-function-plan.md. Narrow registrations add two root imports, two module-map rows and one Lean-only producer row. Immutable checkpoint patch/bundle/source/module manifest binds its resolved committed head, parente9ff191446abba7dc633860bae13db3206698fe5.

Remaining original work: automatic typed candidate selection and actual frontend/default leaf integration with conservative ordinary fallback, unchanged semantic profiles/budgets and matching parsed-source multi-k walk/old/new leaf/context/time/RSS controls, then final full bounded ./run-lean.sh/timedautomatic/audits/assignment-wide reviews. This checked explicit-candidate producer alone is not an automatic sharing implementation or full AU04 completion. Full original goal stays incomplete; no other lane prerequisite, semantic choice or compiler/ABI/function-ref task is assumed or taken.


## AU04 automatic intrinsic candidate selection (2026-11-01)

`Calculus/CallFunctionSearch.lean` automatically proposes actual base/input/level data, rather than receiving those three values from a client. UInt subterms are collected inside first by the intrinsic Tm recursor with an executable twin; `subterms_eq` proves equality of the two. `subterms_length` proves retained proposals≤32. Original positions come from existing `Tm.litVarsS` and certified `Idx.valAt?` reused from AllLeft. Existing `SEnv.set/idAt/substE` abstracts only the proposed old input into a fresh intrinsic head; other captured locals are weakened without substitution into one another. Descending positive-level candidates are accepted exclusively by the exact guarded `checked?` producer. Every returned Plan is indexed by the actual old term, so no name match, future theorem, untyped substitute or user validity/hash premise is trusted.

This is automatic candidate selection, not yet default closer/frontend integration. The literal/value collector refuses other expressions, and a refusal is an optional optimization result; no existing source verdict/profile/one-rule strategy changed. The width cap bounds retained proposals, not whole-tree traversal, full preliminary variable collection/deduplication, proposal sizes, repeated attempts, allocation or kernel checking. Up to32inputs×32proposals×logarithmically many levels can invoke existing expansion checks. No cheap-search claim follows.

Clients prove automatic selection atk1…4, actual selected level3/base5/inputIdx1 metadata, an actual nonempty returned Plan with both-modality returning semantics and fixed proposal-width pins. Literal/no-input, conditional collector and same-size changed-final-offset near-matches refuse. A multiple-local expression selects the true input separately from an old coefficient; actual Planreturn19702 keeps coefficient99 for every intermediate call even when that coefficient is the final target. A retained32/refusal control is paired with an actual accepted explicit35-nodebase beyond every retained proposal's size. This proves real search incompleteness; it does not assert the cap is the sole cause of refusal. No cap was deleted or raised to hide that control.

### Actual automatic-search samples and gates

The external IO-input/effectful-sink probe invokes real search from actual old terms, with no supplied base/level/input. Atk0 it returnsnone (onlypositivelevelsareproposed). Atk1…8 it selects exactly(levelk,inputIdx1), with oldterm nodes9,17,33,65,129,257,513,1025; actual full selected leaf nodes91,124,157,190,223,256,289,322 and formula-context peaks6…13. Three old-term/search/leaf constructions cost respectively1531557,1436055,3051796,7761177,16716601,50156162,198993044,616248070ns; k0's three refusals cost1762829ns. These are aggregate VM runtime samples including IO/measurements, not single-source-call latency, kernel proof closure or walk counts. Producer cost still grows substantially with expanded input.

- `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-call-function-search-audits .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/call-function-search-audits.json VM location: va2-sharing-artifacts/work/call-function-search-audit-records.json`: PASS, actual core/client diagnostics and13public theorem audits, standard-three subsets.13.619364secondsinside,RSS4281576KiB,cgroup1941221376bytes.
- `python3 .../bounded.py mcp-call-function-search-beyond-prefix .venv/bin/python .../mcp_probe_records.py .../requests/call-function-search-beyond-prefix.json .../call-function-search-beyond-prefix-records.json`: PASS, final actual client diagnostics plus new explicitBeyondPrefix axiom audit (14unique theorems), standard-three.9.688678secondsinside,RSS3392248KiB,cgroup1846738944bytes. Expanded actual commands in matching JSON/log.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py call-function-search-affected build Solidity.Calculus.CallFunctionSearch Solidity.Examples.Tactics.CallFunctionSearch`: PASS, Build completed successfully (211 jobs),3.221076secondsinside,RSS1303928KiB,cgroup479473664bytes.
- `python3 .../bounded.py mcp-call-function-search-measurement .venv/bin/python .../mcp_probe_records.py .../requests/call-function-search-measurement.json .../call-function-search-measurement-records.json`: PASS actual structuredsuccess true and rows above.4.730123secondsinside,RSS1794904KiB,cgroup947871744bytes. External #eval samples; separate kernel clients pin actual small-level selections and semantic/refusal controls.
- `python3 VM location: va2-sharing-artifacts/work/checkpoint-static.py call-function-search`: initial FAIL, trust inventory expected0/found1 for the new exact executable override; helper stopped, later gates were pending. Raw failure and command preserved in call-function-search-static-initial-failure.json/rawtrustlog. The verified override is now registered by one exact additive tests/trust-inventory.json row. No checker, previous entry or semantic limit changed.
- `python3 VM location: va2-sharing-artifacts/work/checkpoint-static.py call-function-search-inventoried`: PASS strictautomation/trust/layers/orphans/whitespace,491automatic+61budgeted/zero manual/11refuted/zero pending;1080sources/249inventoriedimplementation/recoverysites/zero findings;181core/zero elaborator;1065reachable/zero orphan/notallowed. Docpaths inherited FAIL48, frozen-base outputSHA256 01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a unchanged; comparisonpasses/checkerfails. Exactcommands/output/hashes in call-function-search-inventoried-static.json.
- `node --test scripts/check-trust.test.mjs`: PASS2tests/0fail, unchanged checker positive/negative counted-inventory and proof-escape controls. Raw call-function-search-trust-checker-tests.log.

Corpus/TestSuite local import closure remains byte-identical to parentdb17ae4b07aceb2ac45c629f85e7495ec43b263a; bookkeeping, not a fresh full/kernel run. All Lean jobs retain asserted memory.max12884901888/swap.max0, LEAN_NUM_THREADS1/-j1, max2LSPfiles/no simultaneousbuild-LSP. ActualLean4.24.0/Lake5.0.0-src+797c613 and prior passingKeySort remain runtime evidence. Raw missing-owning-import, open-term decision/Nat transitivity proof attempts and initial trust failure remain failures. Only final actual diagnostics/audits/builds and separate repaired static gate establishPASS.

Both independent read-only finder/skeptic reviews/follow-ups found no defect; noLean/server/build/writes. Their requested input/coefficient/cap controls, precise causality and traversal/cost boundaries are included. Both reviewed the exact additive inventory hunk and kernel twin theorem. Evidence work/reviews-call-function-search.md. Narrow registrations add two root imports, two module-map rows, one Lean-only producer row and the required single trust-inventory site; exported shared-registration.patch includes that exact inventory hunk. The immutable committed patch/bundle/source/modulemanifest binds the resolved checkpoint head, parentdb17ae4b07aceb2ac45c629f85e7495ec43b263a.

Remaining original work: actual complete-leaf emission/selection in frontend-generated symbolic leaves with ordinary fallback and preserved budgets/caps, matching parsed-source multi-k walk/old/new leaf/context/closure/time/RSS controls, then final full bounded ./run-lean.sh/timedautomatic/audits/assignment-wide reviews. Actual default integration may affect checking cost and requires warning/history inspection before refactoring. This automatic proposal API alone does not complete AU04 or the full goal; no VA1/Decision/Residue/AU05/6/compiler/ABI/function-ref scope is assumed or taken.


## AU04 actual smaller/capped complete-leaf emission (2026-11-01)

`Calculus/CallFunctionEmit.lean` turns actual automatic selection into a complete emitted formula, only when that formula is strictly smaller than the actual old assignment leaf and at most512nodes. `Emission m target out φ` is indexed by exact modality, old target, result term and unchanged original post, and carries the real Plan plus checked full-size evidence. `Emission.holds` proves exact semantics at every typed state, both modalities, any old-context post including program modalities. `Emission.size_lt`/`size_cap` count the actual whole emitted formula, not a walk or isolated composition clause. `replace` returns the literal original formula on refusal, is exactly equivalent on success and never enlarges it (`holds_replace`/`replace_size`). No user option, semantic premise/exclusion or calculus/strategy constructor changed.

The512outputcap is an optional producer eligibility guard, not a new proof budget. Search and candidate construction precede that guard; it does not bound transient memory, stack, proof bytes or checking time. The first valid search plan may fail emission size/cap checks without searching other plans. Structural shrinkage does not establish faster closure. Beyond a refusal, replacement may retain the old exponential leaf, so nonincrease is not a universal linear-family bound. The unconditional complete-family size laws remain in CallFunctionLeaf; this optional emitter has narrower resource eligibility. Default/frontend consumers remain unfinished.

Actual k6 old-term evaluation returns `uintOfNat ((5*3^64-1)/2)` at input2. Kernel controls prove real emissions under both modalities, actualbox256/diamond257nodes versusold262, with formula-context peak11. Real returned formulas establish the correct post. Review found the original wrong-post theorem lacked an emission existence witness; now `emitsWrongSix`/`emittedWrongWitness` prove actual wrong-post emission success and pair its returned formula with the original inhabited state's countermodel under both modalities. Smallk1/k5refusals avoid table overhead. A654nodecandidate wouldshrinkold660butrefusescap. Exact512accepts/513refuses evenwhenitwouldshrink. Refused replacement is definitionally the actual original formula.

Two initial positive/negative proof steps hit unchanged recursion-depth limits. An abstract returnedassignment law was proved without deep terms, but naive client matching stillfailed. Actual lean_goal/lean_multi_attempt established localgeneralization of the deep old term, transporting its already kernel-checked valueSix fact; applying that proof method fixes both statements without changing their claims or any heartbeat/recursion limit. All raw failures and focused proof evidence are retained. These are proof-attempt failures, not source runtime failures.

### Actual replacement samples and gates

The external IO-input/effectful-sink probe constructs the actual old leaf, runs the real emitter, and measures the effective returned formula (emission or exact fallback). Atk0…8 oldleafnodes10,14,22,38,70,134,262,518,1030 become10,14,22,38,70,134,256,289,322. Emissionrefusesk0…5andacceptsk6…8; replacementformula-contextpeaks2,2,2,2,2,2,11,12,13. Three old-term/emission/leafconstructions take2090866,1441445,1177082,2948325,5783994,16267997,64229275,220671508,791319433ns. These are aggregate VM runtime samples, not per-source-call latency, kernelclosurecost or sourcewalknodes. Actual default parsed-source walk/closure measurements stillremain.

- `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-call-function-emit-audits .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/call-function-emit-audits.json VM location: va2-sharing-artifacts/work/call-function-emit-audit-records.json`: PASS, final actual core/client diagnostics and all17 theorem audits, standard-three subsets.31.593853secondsinside,RSS5760804KiB,cgroup3523829760bytes.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py call-function-emit-affected build Solidity.Calculus.CallFunctionEmit Solidity.Examples.Tactics.CallFunctionEmit`: PASS, Build completed successfully (212jobs),11.283853secondsinside,RSS1877044KiB,cgroup1084592128bytes.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py mcp-call-function-emit-measurement .venv/bin/python VM location: va2-sharing-artifacts/work/mcp_probe_records.py VM location: va2-sharing-artifacts/work/requests/call-function-emit-measurement.json VM location: va2-sharing-artifacts/work/call-function-emit-measurement-records.json`: PASS actualstructuredsuccess true, replacement/emission/refusal values above.5.245116secondsinside,RSS1709400KiB,cgroup863784960bytes. External#evalsample; kernelclientsseparatelypin semantic and capcontrols.
- `python3 VM location: va2-sharing-artifacts/work/checkpoint-static.py call-function-emit`: strictautomation/trust/layers/orphans/whitespacePASS491automatic+61budgeted/zero manual/11refuted/zero pending;1082sources/249sites/zero trust findings;181core/zeroelaborator;1067reachable/zeroorphan/notallowed. Docpaths inheritedFAIL48, exactfrozen-base outputSHA256 01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a unchanged; comparisonpasses/checkerfails. Rawcommands/output/hashes retainedin call-function-emit-static.json.

Corpus/TestSuite local import closure remains byte-identical to parent16e6e364588b790774fb76a0dbf13e19c36c630c; bookkeeping, not a new full/kernel gate. Every actual Lean job asserts memory.max12884901888/swap.max0, LEAN_NUM_THREADS1/-j1,max2LSPfiles/no simultaneousbuild-LSP. ActualLean4.24.0/Lake5.0.0-src+797c613 and prior passingKeySort remain runtime evidence. Sampled visible aggregate RSS differs from actual cgroup peak. No resource/proof cap was raised.

Both independent read-only finder/skeptic reviews found no soundness defect and confirmed the negative nonvacuity finding resolved; noLean/server/build/writes. Evidence work/reviews-call-function-emit.md. Narrow registrations add two rootimports, two module-map rows and one Lean-only derived row. Immutable committed patch/bundle/source/modulemanifest binds the actual resolved checkpoint head, parent16e6e364588b790774fb76a0dbf13e19c36c630c.

Next original obligations: consume actual smaller/capped replacements in frontend-generated symbolic leaves with ordinary fallback, unchanged profiles/budgets/SolKeystrategy, matching parsed-source multi-k walk/old/new leaf/context/closure/time/RSS controls, then final full bounded ./run-lean.sh/timedautomatic/audits/assignment-wide reviews. Before a default-dispatch refactor that may slowchecking, warn and inspect speedhistory. This standalone emitter does not complete AU04 or the original full goal; no otherlane/VA1/Decision/Residue/AU05/6/compiler/ABI/function-ref scope is taken.

## AU04 complete intrinsic formula-context transform

`Calculus/CallFunctionTransform.lean` recognizes precisely an existing single UInt local assignment through an indexed `Single` witness, retaining the actual output context without casts. Other update shapes refuse. `update` uses the checked emitter; `holds_update` is exact for every typed state, both modalities and arbitrary actual continuation. `transform` traverses all formula constructors bottom-up, with no traversal into program bodies. `holds_transform` proves equivalence (including negative/antecedent positions); `valid_iff` transports closed validity; `transform_size` proves whole-formula nonincrease. The executable twin `transformM` is kernel-linked by `transform_eq`; one exact additive trust-inventory override entry registers that site. No calculus/rule change.

Witnesses include positive and negative conjunctions, implication antecedents, arbitrary ledger binder with an inhabited false instance, declaration/parallel/signed refusal, and an empty-program modal constructor. The modal fixture does not claim nontrivial execution. Actual complete sizes: old contextual pair 523; transformed box 511, diamond 513. The existing 512 cap applies per emitted replacement, not the whole result. No default consumer has been installed yet.

Commands/evidence under VM location `va2-sharing-artifacts/work/`:
- `bounded.py mcp-call-function-transform-audits ... requests/call-function-transform-audits.json ... call-function-transform-audit-records.json`: PASS, 22 structured records (two clean per-file diagnostics and 20 axiom audits using only standard propext/Classical.choice/Quot.sound). Container process 21.372823 s, sampled aggregate RSS 4,396,896 KiB, enforced cgroup peak 2,071,711,744 bytes.
- `bounded.py build-call-function-transform build Solidity.Calculus.CallFunctionTransform Solidity.Examples.Tactics.CallFunctionTransform`: PASS, 213 jobs; inner 3.926950 s, aggregate RSS 1,301,684 KiB, cgroup peak 473,620,480 bytes. Hard memory.max=12884901888 and swap.max=0, serial -j1 remain enforced.
- `bounded.py mcp-call-function-transform-measurement ...`: PASS actual structured runtime IO controls. Whole old pair k=0..8: 19,27,43,75,139,267,523,1035,2059; effective transformed: 19,27,43,75,139,267,511,577,643; formula context peak 2 through k5 then 11,12,13. Three effectful-input constructions/metrics at k8 took 1,168,550,313 ns. This is emitted intrinsic syntax and construction cost, not parsed-source walk or kernel closure, and not a cheap-traversal claim.
- `checkpoint-static.py call-function-transform`: strict automatic PASS (491 automatic, 61 budget, 0 manual, 11 refuted, 0 pending), trust PASS (1084 sources, 250 inventoried sites, zero findings), layers/orphans/diff PASS. Documentation path checker FAIL with exact same 48 inherited findings/hash as frozen base; comparison PASS, checker remains FAIL. `node --test scripts/check-trust.test.mjs`: 2 PASS.
- Corpus/TestSuite import closure unchanged from committed parent 252a26ae335059c2af80d8451a7196924620252b (266 files): bookkeeping only, not a fresh full gate.

Independent finder and skeptic reviews: no remaining defects; exact evidence `reviews-call-function-transform.md`. Initial reserved-constructor parser and deeply expanded proof failures remain in raw records; no heartbeat/recursion budget increase. Explicit helper term arguments and local generalization preserve the same claims under existing budgets.

Frontend/default dispatch, matching original parsed-call measurements/closure, final affected/full bounded run and full-assignment reviews remain OPEN. Intrinsic kernel proofs make no EVM/compiler adequacy claim and assume no future VA1 theorem.

## AU04 actual parsed-source consumer and compact evaluation certificates

`Calculus/CallFunctionAffine.lean` proves exact checked affine composition, including early multiplication/addition overflow, and doubling-family coefficient evaluation. `eval_term` connects the actual intrinsic two-operation base; `holds_shared_affine`/`holds_shared_affine_cases` consume the complete existing function-table leaf for every typed state/post and both modalities. The nondecreasing profile is an internally certified optimization fact, not a new caller validity premise. The generic shared-leaf API remains available outside this closer's profile; ordinary handling can remain unknown under existing guards.

`Tools/CallFunctionShare.lean` provides explicit `sol_share_calls`, `sol_call_affine`, `sol_close_call_shared`, and `#proof_share_size`. Typed quotation retains the actual semantic leaf head and is checked definitionally against `CallFunctionTransform.transform`. Progress requires actual full-formula node decrease. Every failing step restores the original goal; the complete consumer disables recovery and uses the existing `CloseJ.budget = 100000` within the declaration's budget. Default dispatch has NOT yet been changed. Three exact additive unsafe inventory sites cover untrusted quotation and node measurements; prior entries and the checker are unchanged.

Actual `contract!` parsed functions f0(x)=3*x+1 and f(k+1)(x)=f(k)(f(k)(x)) now have kernel-checked f6/f7 diamond proofs with the original a<1000/y>=a observations, and an unbounded-input f6 box proof. Source countermodels refute y==a at input zero in both modalities. Intrinsic controls cover multiple successful levels, ordered composition, false result, identity, successful deep zero, multiplication failure, addition-only overflow, later failure, word edge and depth-seven-return/depth-eight-failure. These are intrinsic-model/kernel results, not EVM/compiler adequacy tests.

Important confirmed test finding: `mkDecideProof` constructs an expected-proposition hint without validating a false proposition. Before repair, the zero-profile experiment appeared closed at meta level but the kernel rejected its false 1<=0 proof. No false theorem passed. The consumer now calls `Derive.kernelLemma` synchronously on that profile certificate before using it. Raw failing records, including `call-function-share-fallback-concrete-fixed-records.json`, are retained. The final control checks actual entered zero-profile rejection and exact goal identity/type/unassigned-state restoration. Its kernel-error substring is a broad category, contextualized by the logged actual base/level; it is not itself a unique logical certificate. A small no-shrink case then closes through ordinary handling with a checked theorem. Deep zero equality/box-range and exact-input squaring ordinary attempts still fail their existing operation/recursion guards; those raw failures remain failures, not passing tests or new exclusions.

Measured actual source costs (single warm dependency context per row; old walk/initial-leaf time includes its old closure attempt; final kernel time is synchronous):

| Source | Walk nodes/branches | Old whole leaf | Shared whole leaf | Formula context peak | Old walk + initial leaf (s) | Sharing + closure (s) | Final kernel (s) | Sampled aggregate RSS (KiB) | Cgroup peak bytes |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| f6 diamond | 5/1 | 274 | 269 | 11 | 6.131160118 | 0.252632623 | 0.780180580 | 2830584 | 1921802240 |
| f7 diamond | 5/1 | 530 | 302 | 12 | 12.244807940 | 0.424449560 | 1.613477356 | 3653708 | 2769494016 |
| f6 box | 4/1 | 268 | 262 | 11 | 16.270034227 | 0.245354058 | 0.902641322 | 3964144 | 3109023744 |

Walk count is separate from leaf size. These samples demonstrate reduced emitted-leaf growth, not polynomial end-to-end construction/checking time. Existing expanded-summary production/certification still grows substantially; coefficient bit sizes also grow: a/b bits at k0..8 are 2/1,4/3,7/6,13/12,26/25,51/50,102/101,203/202,406/405. Effectful-input 1000 coefficient constructions at k8 took 7851249 ns. `tmSize` excludes integer bit lengths, context annotation volume and proof bytes. The 512 cap is per emitted leaf; refusals may retain an exponentially growing old leaf. No universal runtime or whole-context-512 claim is made.

Commands and decisive evidence under VM location `va2-sharing-artifacts/work/`:

- Per-file MCP errors: all five new modules clean; source controls have informational actual-base/refusal messages only. `mcp-call-function-share-client-doc` PASS and the post-profile-repair bounded rebuild `build-call-function-share-kernel-client` PASS (270 jobs, inner56.263538s, RSS3214980KiB, cgroup2932043776 bytes). `build-call-function-share-controls` PASS. Actual sources and all controls remain under unchanged heartbeat/recursion budgets.
- `bounded.py mcp-call-function-compiled-axioms ... mcp_probe_one_file.py ... requests/call-function-compiled-axioms.json ...`: PASS, 28 actual built theorem values, only standard propext/Classical.choice/Quot.sound (some none), inner11.588901s, RSS2105416KiB, cgroup1040793600 bytes. Four imports, one scratch document; actual source hashes/builds bind this audit. This supersedes the mixed-source audit below.
- **Failed resource-policy attempt retained:** `mcp-call-function-share-audits` stopped at exit137/386.61s after source-main, verification-scratch and source-controls workers were observed together. Its partial records are not a passing final audit. Installed `lean_verify` copies whole source into a scratch. Future sessions enforce one real source path plus one scratch, max-open-files=1; source checks remain per file and compiled-value axiom queries use a single scratch. No build/LSP overlap occurred. A prematurely attempted dependent profile was refused by the writer lock and launched no Lean job. `source-audit-file-budget-stop.json` and `source-audit-repair.md` retain this evidence. Hard 12GiB/no-swap remained enforced; this was a file-count stop, not successful validation.
- `mcp-call-function-share-profile-six-serial`, `...seven-serial`, `...six-box-serial`: PASS structured results and synchronous kernel checking; requests/source/logs/footers retain the table's measured costs.
- `checkpoint-static.py call-function-share`: strict automatic PASS (491 automatic,61 budget,0 manual,11 refuted,0 pending), trust PASS (1089 sources,253 inventoried sites,0 findings), layers/orphans/diff PASS. `node --test scripts/check-trust.test.mjs`:2 PASS. Doc-path checker still FAIL with the exact same48 findings/hash as frozen base; comparison PASS, checker remains FAIL.
- Corpus/TestSuite import closure unchanged from committed parent5c7074300c2e5cf51764560a6adb7bc300772ae2 (266 files): dependency bookkeeping only, not a fresh full kernel gate.

Independent finder and skeptic reviews found no remaining soundness defect after repairs. Exact findings/limits: `reviews-call-function-share.md`; final audit results: `call-function-share-final-evidence-summary.json`. No future VA1 declaration/premise is assumed. Default consumer integration, affected/default closure regressions, final bounded `./run-lean.sh`, final full-assignment reviews and final package remain OPEN.

## AU04 default closer integration (2026-11-02)

The actual checked consumer now lives in `Calculus/CloseCallSharing.lean`, imported by `Closers.lean`; Tools retains typed aliases for the committed explicit API and the measurement command. The existing SolKey calculus, `Stmt.step`, single-rule walk, observation and validity/hash premises remain unchanged. Disjoint plain/joined guards retain earlier anon/small-split/alias paths and consider only an already named leaf or a single update above the existing shareWholeMax=8 guard. Recursive splits can start another invocation; failed-attempt cost is not refunded. No proof/size/split limit was raised.

Five actual closer-only source clients cover f6/f7 diamonds, all-input f6 box, already-named input and a conditional checked-increment prefix. The new prefix consumer stops only at the exact generalized formula variable; each actual remainder stays opaque and is restored by equality. Side-return facts are existing integer/Boolean observations, normalized through intrinsic type aliases and `of_decide_eq_true`. No interval or profile is assumed. Unsupported heads/profiles restore all tactic state. Generated local names are fresh. The existing general CloseJ peeler is unchanged.

The actual current default walk now closes f6/f7, so only their original-open measurement pins improve 1→0. Walk nodes/branches stay5/1 and old/shared complete leaf sizes stay274/269 and530/302. The legacy `original open` label refers to the current default walk before the explicit consumer; it is not the historical pre-default baseline. The prior source profile table belongs to committed60479dcddcbf1e6137f6f837cbf2ba4db66979dc, not a fresh measurement of this default route. Current end-to-end build/file costs are recorded separately; no runtime/bit-size linearity claim follows.

G0 adds exactly five new pure intrinsic foundations to the protected core list (186core/zero elaborator edges), with matching narrow parallelism documentation. The function-table family remains above the existing M7 KIntBinder→LedgerCut→QuotientCut→FlattenReads→PathGuards→DeclarationFacts→SurfaceSpec→Syntax.Elab dependency chain; it is not misclassified as core. No core module reaches it. The quotation unsafe-site registration moves to the new consumer; prior entries/checker stay unchanged.

Concrete commands/evidence under VM location `va2-sharing-artifacts/work`:

- `bounded.py default-call-sharing-regressions build Solidity.TestSuite.Derived15 Solidity.TestSuite.Derived17 Solidity.Examples.Tactics.PolySize Solidity.Examples.Tactics.CallSummary Solidity.Examples.Tactics.JoinSigned Solidity.Examples.Tactics.JoinWalk Solidity.Examples.Tactics.JoinControls Solidity.Examples.Tactics.JoinIntervals Solidity.Examples.Tactics.JoinSequence Solidity.Examples.Tactics.Join Solidity.Examples.Tactics.CallSharingDefault Solidity.Examples.Tactics.CallFunctionShare Solidity.Examples.Tactics.CallFunctionShareControls Solidity.Examples.Tactics.CallFunctionAffine`: PASS311jobs, inner549.501041s, sampled aggregateRSS10169940KiB, cgrouppeak9955971072bytes. Derived15=95s,Derived17=176s, below unchanged300s module budget. Original split/hull limits and false-result controls remain.
- `bounded.py mcp-default-source-set-rebuilt ... serial-file-probes.py close-call-sharing call-share-tool-moved close-default-syntax closers-default-import call-share-main-default call-share-controls-default`: PASS all six per-file sessions; inner77.483688s,RSS4163212KiB,cgroup3527966720bytes. One real file/session, scratchslots1, configuredmaxopen1; no build/LSP overlap.
- `bounded.py mcp-default-call-sharing-compiled-axioms-rebuilt ... mcp_probe_one_file.py ... requests/default-call-sharing-compiled-axioms.json ...`: PASS structuredsuccess/33 actual built theorem values; only standard propext/Classical.choice/Quot.sound subsets (some none). Single scratch. Exact commands/versions/cgroup assertions and measured resources are in rawJSON/logs and `default-checkpoint-resource-summary.json`.
- Failed initial peeler/prefix/Boolean-alias experiments, stale-import attempts and source-pin mismatch remain raw failures. `build-default-call-sharing-final` is FAIL overall for mistakenly named Solidity.Solkey.TestSuite.Derived15/17 targets, even though its three actual client jobs passed; corrected target validation is the311-job gate above. No timeout/resource stop is counted as completion.

Independent read-only finder/skeptic final reviews found no soundness defect after fixes and used no Lean/server/build/writes. Review evidence `reviews-default-call-sharing.md`; both also reviewed the exact additive CORE registration. They confirmed opaque equality transport, conservative arithmetic selection, transactional refusal and inventory relocation. Limits: one selected named leaf through supported positive prefixes; other heads/multiple/negative contexts can refuse. Arithmetic selection can miss conjunctions and scans context per side; no bounded-overhead claim. Already-named inputs are not new capped emissions. Small ordinary fallback and entered unsupported exact rollback are certified; deep-zero/square ordinary stress failures remain failures, not exclusions or general-completeness claims.

Final full bounded wrapper, timed automatic gate, assignment-wide final reviews and final committed package remain OPEN at this checkpoint. No VA1 future theorem or compiler/EVM adequacy premise is assumed.

Final default-source per-file diagnostic `mcp-default-client-final-fresh`: PASS all five theorems/no diagnostics, inner80.168373s,RSS6228292KiB,cgroup6205689856bytes. Earlier event-loop cleanup trace occurs after completed records/normal exit and is not a Lean diagnostic.

Checkpoint static gates: `checkpoint-static.py default-call-sharing` PASS strict automation(491automatic/61budget/0manual/11refuted/0pending), trust(1091sources/253sites/0findings), layers(186core/0elaborator), orphans and whitespace. `node --test scripts/check-trust.test.mjs`:2PASS/0FAIL. Doc-path checker remains FAIL48, with frozen-base-identical outputSHA256 `01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a`; comparisonPASS/checkerFAIL. Commands/raw output/resources reside in the checkpoint staticJSON/logs. Both independent reviewers confirmed that the exact five-module G0 registration strengthens protection and removes no restriction.

## Final-gate rule census and correspondence repair (2026-11-02)

The full wrapper attempt with repaired Node PATH passed its runtime/version/layer preflight but found one stale global printer census: `Examples/LexRuleSyntax.lean` expected27 LeanTaclet rules while the actual complete printer checked28, including the new `ifElseJoinSequence`. Its181 SolKey Taclet and4 CallbackTaclet counts stay unchanged. This is a diagnostic census pin, not a program/verdict expectation. The exact raw failure stays in `work/final-run-lean-node-path.log`; this full attempt is FAIL, not completion evidence.

The required correspondence table also lacked the exact new rule row. Added its precise `.inr body` eligibility, fresh condition capture/block/pop, ordered writes, preserved failures and concrete soundness chain (`captured_drop_runSt`, `joinPlan_sound`, `iteStep_sound`, exact `toStep`). The existing singleton row now names its actual unchanged `ifJoinSingle?`/`.inl` path. This is a narrow registration repair; no kernel definition, theorem, premise, source verdict or budget changes.

Independent read-only finder/skeptic confirmed both repairs and the exact soundness references; neither used Lean/server/build/writes. They specifically required the captured-block theorem rather than only the raw joined-program equality. Focused per-file/build/static gates, final corrected full wrapper and final package remain pending at this draft.

Repair gates now PASS: per-file MCP `mcp-rule-census-repair` clean; bounded `build-rule-census-repair build Solidity.Examples.LexRuleSyntax`107jobs/inner2.517154s/RSS880304KiB/cgroup197754880bytes; `checkpoint-static.py rule-census-repair` strictautomatic/trust/layers/orphans/diff PASS, baseline-identical docpath checker FAIL48 as before. Both reviewers confirmed the exact applied hunks.

Full-wrapper failures retained: `final-run-lean` exit127 before Lean builds (mounted Node omitted from PATH, repaired only in task-owned wrapper); `final-run-lean-node-path` stopped by owner after the concrete census failure, exit137/1519.034300s. This stopped run has no sampler peak footer, so no aggregate peak is inferred. It is not PASS or resource-completion evidence. Completed cache outputs were preserved. The corrected full wrapper, timed gate and final committed package remain open.

## Final assignment validation and delivery (2026-11-02)

The complete original Work queue AU03→AU04 and assigned Backfill queue are implemented/proved or explicitly reused as already integrated. No future VA1 theorem is assumed. Decision/Residue, AU05/AU06, compiler PC/ABI/function-reference/options work and unanswered TypeExamples choices remain untouched. Human AQ1/AQ2 receipts, frozen base and setup29aec17e607a5dfc585a0e4a49990dc8e3f751c3 remain ancestors of this delivery. No push/merge/PR/tag occurred.

Validated source checkpoint: `856cd19640a52d1a21a7c3aaa7cb5ef94e08b362`; semantic/default checkpoint `3591d15b8075a32f3f2ac8623e9ae2fc778e8100`. The final handoff-only commit changes no Lean/build source. Its resolved full committed head is appended to exported handoff.md and recorded in revision.json. Repository VM location `va2-sharing`, branch `codex/solidity-automation-20261031/va2-sharing`, exact frozen base `8bd8742ad987d566f7ba7624372cec1c020be07c`.

### Commands and decisive outcomes

- `python3 VM location: va2-sharing-artifacts/work/bounded.py final-run-lean-rule-census /bin/bash VM location: va2-sharing-artifacts/work/final-run.sh`: PASS. The task-owned PATH shim delegates to pinned Lake with the sanctioned temporary -j1 config and invokes the **actual** `./run-lean.sh`. Default1061jobs PASS; complete SolkeyTestSuite311jobs PASS; native `solkeycheck: parsed377taclets,131read-bearing,tablecovers131` and `OK — annotations match` the exact frozen snapshot rules. Source pin473da8944ca7329e6b76819863591407db26e7ec (not an absent sibling checkout/skip). Actual Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake5.0.0-src+797c613.
- Full run inner5560.872232s (outer5562.21s), sampled aggregateRSS9071300KiB, cgrouppeak10135433216bytes. Every child starts by asserting memory.max12884901888/memory.swap.max0; LEAN_NUM_THREADS1 and explicitLean-j1, no simultaneous LSP/build. The RSS sampler measures; Docker's actual enforced cgroup is the hard bound. Existing non-TestSuite examples legitimately took Recursion380s/OpenLoops506s/Decision574s; no universal300s claim. The repository automatic module budget below applies to TestSuite.
- `python3 VM location: va2-sharing-artifacts/work/verify-final-timings.py`: PASS. It first requires the real full-wrapper exit0, a clean committed tree and no changed TestSuite import dependency between semantic checkpoint3591d15b… and census checkpoint856cd196…. It combines the actual311-job affected-regression and final-wrapper logs; **all22 proof-bearing Derived1…21/Refuted modules covered, zero missing, zero over300s**. Actual `node scripts/check-automatic.mjs --strict --build-log VM location: va2-sharing-artifacts/work/final-combined-timings.log --budget-s 300` reports26TestSuite timing rows,491automatic,61budgeted,0manual,11refuted,0pending. Maximum proof module176s (Derived17); Derived15=95s. No budgets/options/expected source verdicts changed.
- `python3 VM location: va2-sharing-artifacts/work/bounded.py final-affected-corpus build SolidityCorpus`: PASS332jobs, inner73.276899s,RSS1413764KiB,cgroup324263936bytes. Default closer integration **does** change Corpus/TestSuite closures. Standard import-fanout omits their library roots; the initial ad hoc1-module result was invalid, corrected by explicitly reading root imports: Corpus330modules/TestSuite309modules. `default-final-import-closure-corrected.json` supersedes the erroneous ad hoc audit, not the historical immutable pre-default bookkeeping. No changing checkout was exported as a checked dependency.
- Final compiled-value MCP audit: `mcp-default-call-sharing-compiled-axioms-rebuilt` checks33actual built theorem values, including all5default clients, with only standard propext/Classical.choice/Quot.sound subsets (some none). Final dependency audit confirms its277-module import closure unchanged by the census-only follow-up (`final-axiom-import-closure.json`). Earlier per-checkpoint audits cover the other rule/transport/size laws. Final full kernel builds verify the concrete combined local source, not an assumed future interface.
- Passing runtime prerequisite remains `runtime-recovery/command-1.log`: actual enforced limits and versions, passing boundedKeySort, then `KEYSORT_PASS` **before** `RUNTIME_GATE_PASS`; RSS301932KiB/cgroup114503680bytes. That marker attests runtime setup, not assignment completion.

### Queue, proof and measurement boundaries

Baseline raw joined-key failure, M8 leftovers, PolySize/doubling growth, one post-anon leaf and speed history remain archived. AU03 warning names unannotated literal-bounded loops and keeps unrolling; ordered joined writes use fresh condition snapshots/typed updates with soundness and size laws. Conditional notation/printer/chain rows, original ifElse programs, bool-key kernel split/substitution, two-base/beyond-limit and signed/scoping controls are complete. The new Lean-only ifElseJoinSequence row and printer census28 are now explicit, while181SolKey/4callback constructors and one-rule split strategy stay unchanged.

AU04 proves fresh-local restoration, inhabited operational definitions, complete function-family leaf semantics/size/context laws, actual old-term/source-call transport, checked candidate/size-capped emission and all-context equivalence. Actual parsed/default f6/f7 diamonds and f6box, joined prefix and already-named leaves are kernel checked; wrong same-source observations are refuted in both modalities. Small no-shrink ordinary fallback and entered unsupported exact rollback are checked. Original backfill is complete/reused: conditional printer/chain rows, Int.negSucc, Solidity-context SplitTo docs, proof_size relocation/pins, already-correct certifyLong context discovery audit/controls, warning/sharing/loop fixtures.

Walk and leaf growth remain distinct: parsed f6/f7 walk5nodes/1branch; whole old leaves274/530→shared269/302, context peaks11/12. Exact emitted-family tmSize is2*base.size+post.tmSize+33*k+44+haltPost.tmSize. This excludes program interiors, cumulative annotations/proof bytes and integer bits. Optional cap512 is per emitted replacement; refusal may retain exponential originals. Old summary production/kernel checking and coefficient bit growth are not polynomial-time guarantees. One selected named leaf through supported positive prefixes is not universal default completeness; unsupported profiles/contexts retain ordinary handling and may remain unknown. No theorem/exclusion/premise is weakened to expand that profile.

The measured post-anon loop's whole64/anon55→plan66 demonstrates a **proof-cost** repair (not smaller syntax): actual original4.551744s/64.651mrawHB→1.181506s/14.341m, with corresponding kernel soundness. Historical source profiling at60479dc… remains historical, not re-labelled as timing this final default route. Actual final build costs/resources above are separate. Deep-zero/square ordinary stress failures and earlier fallback slowdowns remain documented failures/limits, not new exclusions or claimed completion controls.

Kernel evidence concerns the intrinsic Solidity model under its exact existing premises. The frozen SolKey checker is an external taclet-text/sort agreement check, not EVM/solc/compiler adequacy. No new EVM conformance/PC-group claim or changed hash/validity premise follows. Undecidable/unprovable classes remain unknown under decisionsc,c-prime,d,e3-prime,e3-double-prime.

All earlier raw proof/import/trust failures, the resource/file-count stopped audit, Node-PATH failure and intentionally stopped failed census build remain in the evidence archive. They are not passing gates. Full assignment source reviews and census-repair reviews were independent/read-only finder+skeptic, with no Lean/server/build/writes; `reviews-va2-full-assignment.md` and checkpoint review files retain findings and fixes. Final static/review/package completion is appended below after its actual gates.

Final static gates: `checkpoint-static.py va2-final` PASS strict automatic source inventory, trust1091sources/253inventoriedsites/0findings, layers186core/0elaborator, orphans and whitespace. `node --test scripts/check-trust.test.mjs`2PASS/0FAIL. The actual `bash scripts/check-doc-paths.sh` remains **FAIL48**, frozen-base-identical outputSHA256 `01fd3beaa0d1694397f6231999418eea67e797d42150bf68d2d8a96bc4ea109a`; required baseline comparisonPASS, checker itself is not relabelled PASS. These pre-existing unrelated paths are not new exclusions or an unperformed Lean gate. Raw per-command outputs/hash/exit statuses in `work/va2-final-static.json`.

Final artifact destinations: VM location `va2-sharing-artifacts/checkpoint-va2-final/original.patch`, `va2-sharing.bundle`, `source.tar.gz`, `handoff.md`, `evidence.tar.gz`, `module-manifest.json`, `PARALLEL-INTERFACE.md`, `shared-registration.patch`, `revision.json` and `SHA256SUMS` in that same directory. Export is from the final clean committed head; patch/bundle/source/module/evidence checksums and bundle verification must complete before the goal/result is marked done. Previous checkpoint packages remain immutable. No later integration/default-branch publication is claimed.

Final independent delivery finder and skeptic reviews found no remaining assigned implementation/proof/check gap or hidden premise/budget/source-verdict/exclusion change. They confirmed the separate inherited-docpath FAIL/comparisonPASS and complete concrete gate accounting (`work/reviews-va2-final-delivery.md`). Source files remain byte-identical to validated856cd19640a52d1a21a7c3aaa7cb5ef94e08b362. The exported `delivery-verification.json` records patch-applied-tree, bundle-ref and archive-blob identities, plus full resolved head; the exported handoff receives the actual verification outcome. Final result/goal completion follows only after those checks and every SHA256SUMS entry pass.

## Master integration review (2026-11-02)

VA2 head `ae1a1d56` merged onto master `febf70a6`; the only conflicts were the
additive `Solidity.lean` imports and `docs/module-map.md` rows (both kept).
Master's memory-loop replay (`TestSuite/MemoryLoopReplay/`) recorded 903
visits of `returnLeavesNestedLoops`; `ifElseJoinSequence` makes it 987, so
`Discover09`/`Assemble09` now hold 87 steps and the literalized refusal
control uses node 973 (was 889). Gates: `./run-lean.sh` builds pass (sibling
SolKey sort check drifts, known baseline; pinned `solkeycheck` OK), fresh
memory-loop group 275.67 s ≤ 300 s, check-testsuite, check-automatic
`--strict`, check-trust, orphans and layers ok; doc paths equal master's.

Finder and skeptic reviews (read-only, no Lean server) found no soundness
defect. Fixed: stale "903 visits" in `docs/loops.md` and
`docs/compiler-verification.md`; the "walk unchanged" sentence in
`docs/lean-key-rule-map.md` now scopes to call sharing. Recorded, not changed
(Lean docstring edits would rebuild most of the tree):
`Calculus/CloseCallSharing.lean:7` says the walk is unchanged (true of call
sharing only); the `SolkeyFragment.lean` docstring names only `ifElseJoin`,
although multi-write `if`s now leave SolKey's `ifElseSplit` for the Lean-only
`ifElseJoinSequence`; `Sound/JoinSequence.lean` lacks a `#print axioms`
pin; `sol[]{}` literal-loop warnings now also appear in master's
`Evm/MemoryLoop*SourceExamples.lean` (outside `#guard_msgs`, noise only).
Walk headroom for `returnLeavesNestedLoops` fell from 121 to 37 steps.
