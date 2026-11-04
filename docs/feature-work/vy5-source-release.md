# VY5 held Source release inventory

Status: partial owner checkpoint; not standalone-consumer integration approval
or complete H16/H19/P8 realization. Source statements, budgets and implementations
are unchanged by this packaging step.

The scheduled standalone import of `Yul/Composition/MonetaryLifecycleControls`
failed on published master because it needs the held exact-money migration.
The original kernel failure is retained by the coordinator at
`receipts/sched-20261104T122441Z/lanes/vy5-composition/touched/1.log`.
Its downstream generated sorryAx diagnostics are not accepted proofs.

The actual changed dependency closure of that control requires all four of
`Source/Monetary`, `Source/World`, `Source/StateExamples` and
`Yul/World/Lifecycle`. Adding an import or casting the wide balance to Word
would not supply their missing implementations and would invalidate the control.
The selected full2^256 amount and refusal/self-beneficiary behavior are retained.

`scripts/yul-composition/source-release.py` inventories exact committed HEAD
bytes against the published base. It follows imports through unchanged modules,
checks reached working files against HEAD, handles rename destinations, parses
nested/line comments and rejects missing local dependencies or unsupported
import headers. It produces an inventory, not kernel validation or release
approval. Fifteen tests include temporary-Git CLI mutations for commented
imports, dirty unchanged intermediates, untracked selections, missing local
imports and renames. The real standalone selection is deliberately rejected
(exit1); the complete changed selection passes the dependency audit.

The coherent inventory contains35 held Source modules and175 changed Lean
modules including required consumer migrations and the generated root. Exact
per-module source hashes and changed import dependencies are generated into
the sealed release manifest. This is the whole changed closure, not a claim
that each consumer is independently mergeable. Source core ownership remains
H16/VY5; compiler/world/readonly consumers retain their owner-review boundaries.
H25 G01 authority review and readonly History review remain pending.

## Checking-time evidence

The retained fresh baseline has15 matching published-master Source files.
Its external imported source files have no changes between the recorded
baseline commit and current master. Reuse of an after measurement additionally
requires both exact current source bytes and every imported artifact hash to
match. Fourteen records meet that condition. StmtProgress's imports changed,
so it was measured freshly, including a matched before/after pair using the
hash-verified archived setups under the same serial bounded runner.

Original baseline StmtProgress35.951s; initial fresh after38.235s; matched
before37.522s and after35.200s, both kernel exit0. The complete15-module
comparison totals492.530s before and487.606s after. This supplies actual
checking times, not Lake cache/build duration. No noticeable regression is
shown by the matched comparison; all individual raw observations remain.

Horizon345.030s before and340.924s after remains a pre-existing FAIL against
the300-second module policy despite kernel exit0. That policy is not waived.
Fresh actual lifecycle control checking with the complete held closure passes
in0.244s; this is distinct from the failed published-master standalone attempt.
No fresh native execution, G01 authority/session wiring, full reachability,
fixed-plan session consistency, P8 inhabitant, original24 obligations/six
Source combinations or whole-lane gate pass is supplied by this release.

Finder and skeptic independently reviewed the inventory read-only, without
Lean/server/build/tests. Both found import/provenance gaps in the first draft;
all confirmed findings were fixed, tested and re-reviewed without further
findings. The original native five optimized-viaIR journal failures and
historical docs/G03 failures retain their actual exits. No verdict, observation,
proof budget or semantic hold is changed.


## Actual request-scope horizon increment

Two laws now prove Grow and Approx for the existing requestScope under genuine
per-balance body Grow/Approx premises and the same immutable plan. They use
actual Source operations; no execution result is assumed. Approx.attempt_bind
handles request cleanup followed by timeout rethrow without events; a blanket
Approx.attempt rule is not used. Twelve inhabited controls retain full caller
state, heap/log/function-local/journal prefixes and DEAD bytes. They cover
all completed horizons of a real body family, zero-horizon timeout, exact2^256
body input, drop versus request cut, cut0/cut1 and caught cuts that still halt.
Different successful plans returning257/258 are a concrete non-Approx control.
Input balance is not installed into an authority/account and is not a receipt.

The first automated approximation attempt failed at captured timeout; that
failure is retained. The corrected existing timeout-continuation rule passes.
Finder and skeptic independently reviewed read-only without Lean/build/tests
and found no issues. Actual plan-parametric evaluator induction (legacy
GrowAt/ApproxAt use default disabled plans), fixed-plan Session consistency,
H25 authority wiring and P8 realization remain open. This does not discharge
the original24 obligations/six combinations or create fresh native evidence.


Published dependency b419c3cf adopted during this increment. Its first coherent
checkpoint failed at two new H16 consumers: memory-internal-calls' comparison
control still supplied five St fields, and V17/G19's conditional proof applied
its EM result directly where the new optional plan occupied that position.
The first gains only Cursor.empty. The latter spells its two local equations
using .run and normalizes ExceptT.run for the existing sub-scope rewrite.
Public theorem statements/results, prior five state fields and budgets are
unchanged. Both fixes pass focused checks and read-only finder/skeptic review.
The first full build61s and library22s failures remain failures.

The published merge briefly committed documentation conflict markers after a
permission error did not stop the shell. Commit837c0793 immediately removes
only those markers, retaining both sides. Parent inventories and failed map
are retained; the regenerated axiom inventory equals the semantic three-way
merge, with fourteen new request-horizon pins. The known H19 transfers shrink
to an axiom-free proof is preserved, not overwritten by master's old Word pin.
No Source implementation was altered by that correction.


## Closed enabled-plan evaluator growth

FailureEvaluatorGrow proves GrowAt for every horizon, arbitrary intrinsic
program/global/state and any fixed enabled FailurePoints. All17 functions
of the actual mutual evaluator are included. The final growAt theorem has
no NoFail, body-growth, fragment or desired-execution premise. The generated
record/induction is proof-only, based on the existing Source.Horizon case
partition, with actual functions explicitly supplied some points. No AST,
state or evaluator is copied or replaced. The generator records a raw-byte
SHA256 basis and --check rejects stale/missing output, including CRLF changes.
Existing uniform unused induction-hypothesis warnings are retained rather
than suppressed. No proof/fuel/heartbeat/node budget changes.

Initial checking91.700s failed only at an explicit envLoop equation that
selected none. Selecting the actual some-points equation passes80.074s,
below the unchanged300-second module bound. The hot existing Horizon file
is unchanged; its pre-existing timing-policy failure remains a failure.
The VM then disconnected before control-file creation. On recovery, the
passing proof/source hash was confirmed; only controls/import materialization
resumed. A context-name collision and premature fixture reduction failed
that check; context qualification and existing fixture equalities fixed it
without increasing the heartbeat budget. No downstream generated sorryAx
is accepted as a proof. Raw failures remain under planned-grow-20261104.

Five controls consume actual mark/sub/enterInstance under both Source
pipeline settings: all-horizon/all-cut caller-prefix preservation, exact
existing fixture identity, changed-plan outcomes and event-erasure refusal.
FailureTransactionGrowth further proves Grow of actual runTxWithPlan with
the request timestamp-adjusted global, root credit/dispatch/rollback,
finalization and receipt operations. No body-growth/outcome oracle is supplied.
Headline induction, root and controls have only propext/Classical.choice/
Quot.sound, pinned by guard messages. Finder and skeptic reviewed read-only
without Lean/build/tests; generator byte-check precision was fixed and
re-reviewed, with no remaining findings.

This closes event growth only. Enabled-plan Approx/Below induction, cursor
coherence, full deployment/request ordinal/session consistency, exact-money
installation/authority wiring, H19 full reachability, P8 realization and
immutable/funds release remain open. It supplies no fresh native observation,
assembly embedding, original24-obligation/six-combination or full-lane closure.
