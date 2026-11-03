# S04.04 sender-funds request boundary

Owned H10 producer for V14 G43 and V16 G50.02. This is Source/session
validation, not assembly correctness or compiler/EVM correspondence.

`Source.RequestFunded F opening history q` compares `q.value.val` with
`(F.ledger opening history q.sender).val`. It never substitutes the receiver's
internal account balance for the external sender ledger. Both actual session
drivers (`sessionGo` and `sessionGoEvents`) test the corresponding Boolean
before `firstDone`/`runTx`. An invalid request consumes one action and advances
its index, retaining the entire Source state, history and previous outcome.
It produces no transaction event, revert or transaction finalization.

`Source.runCheckedTx` exposes exactly this boundary for arbitrary typed state
and horizons. `none` means invalid/dropped; `some` retains the actual raw
transaction result, including success, revert, timeout and stuck. Its laws
prove invalid whole-state identity, valid exact execution, necessary funding
for a result, and completed-horizon stability via the existing `runTx_stable`.
The session drop laws do not assume a successful execution result. Existing
prefix/monotonicity proofs are extended through the invalid-action branch.

`FundsControls` uses a real typed payable empty function and actual evaluator:
exact-balance and zero-value success, missing-code completed revert versus
funded timeout versus invalidity, recipient/sender distinction, heap/aliases,
logs and journal identity on drop, preserved last outcome, following valid
request, prior credit, and prior successful-transaction debit. The two history
ledgers are explicit finite control fixtures, not a general ledger model.
Both legacy and viaIR Source contexts are kernel checked; these are not fresh
solc/EVM observations.

## Exact remaining obligation

G01 `Lang.Affordable` uses the history immediately before the final `Event.tx`.
Admission uses history before the body, which can emit further events.
Arbitrary `Fixed.ledger` supplies no compatibility law relating those two
balances. To establish global affordability a consumer must prove that
admission funding implies funding at that actual pre-tx history, using the
real ledger/body semantics. This is open; neither `Lang.Affordable` nor its
premises are changed and no such theorem is assumed. Deployment, nested-call
transfers, fees, nonce validity and allocation/assembly/world adequacy remain
separate obligations. Existing `ExecState.transfer` already checks sender
funds (including self-transfer) and is unchanged.

## Measured reapplication on current Source

The concrete owned d5054e3f changes are reapplied to current Source without
copying stale Eval/Machine bodies. Changed existing modules: Source/World,
Semantics and Session. Added modules: Source/Funds and FundsControls.
Current H16 plan forwarding, cursors and ExtCall H22 fields are preserved.

Before/after per-file measurements, actual resource receipts, failed attempts
and final outcome are retained in
`/workspace/vy5-composition/funds-release-20261103`. This is a current
release checkpoint, not a claim that old funds-20261102 full gates ran on
this tree. Full current-tree gates remain pending until explicitly recorded.
H19 exact post-fee balances/resource execution, P8 realization and all24
original Y10 obligations/six combinations remain open. The existing Fixed
fixture ledgers in controls are not production ledger correctness evidence.

Independent read-only finder and skeptic reviewed the actual drivers/laws.
No fresh native compiler/EVM comparison is added. Historical docs/G03 and
original native journal failures remain failures, not zero-regression passes.

Measured kernel wall times, seconds (before→after): World0.5966→0.6347,
Semantics0.8600→0.8915, Session2.0973→2.1570. Aggregate growth0.13s;
no noticeable Source-checking regression measured. Full Session command366s
includes the fresh unchanged Horizon dependency and HorizonDeploy rebuilds;
it is retained separately, not reported as a2s complete closure. The known
Horizon300s policy overrun is not reclassified as a pass. Funds0.2536s and
FundsControls2.3571s. All five per-file kernel checks exit0;21 new laws have
exact generated standard-axiom guards. Finder/skeptic independently approved
with no findings. Full current-tree checkpoint remains pending.

Combined checkpoint attempt: a transport reconnect lost the original supervisor
while its bounded container survived. The same container was adopted under
the writer lock; the monitoring gap is retained. The actual checkpoint found
Source.St.mk expecting6 fields in Backend/Transient/Controls (five provided).
It was stopped to prevent a duplicate failing library retry: actual exit137,
OOMKilled=false, with an explicit non-resource stop reason. No full checkpoint
was restarted in that turn. Three authorized empty-cursor constructor fixes
in Backend/Transient/{Controls,WordControls,SourceCallback} pass individually;
reviewers confirmed no statement, observation or budget changes. Full closure
remains pending. New Source changes are still only World/Semantics/Session
and Funds/FundsControls; Eval/Machine/Horizon bodies are unchanged.
