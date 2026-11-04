# VY5 composition pieces

From the vy5-composition lane; the lane's Source core edits (immutables,
funds) and the modules that need them are not on master yet.

- `Lowering/P8/FailureProjection.lean` (`SpecFailures`): failure-plan
  operations on `FailureResources.Bound` (`Nat × FailurePoints`); no P8a
  `FailureProjection` or `Producer` instance is built.
- `Lowering/P8/SourceRealization.lean` (`SpecExecution`): the Source session
  machine (`run`, `Executes`); `MachineAgreement` holds definitionally;
  `no_countable_resource` restates `ResourceContractLaw1`'s obstruction.
- `Yul/Composition/CorrectnessInstances.lean`, `CorrectnessPublic.lean`:
  generic composition of the four G01 stages, giving `SpecTransfer` under a
  table-linking premise and `PublicCorrectness` when nine boundary fields are
  supplied as given. The controls use the G01 toy fixture only; no Yul or
  assembly instance exists.
- `Yul/Composition/P6FrameCorrectness.lean`: the physical MSTORE store, the
  Slice REVERT capture and journal restoration on one 96-byte image.

Open: the H16 Source resource extension, the immutable and funds Source edits,
a real assembly instance.

### H16 cursor interface (sched 2026-11-03)

- `Source/FailureCursor.lean` (`Source.FailureExecution`): typed request and
  frame budgets over `FailureResources.Bound`, with request-before-frame and
  oldest-frame priority. Executable cursor operations only; no Machine, Eval or
  Session hook is installed and no failure-aware language or P8a `Producer` is
  claimed.
- `SpecExecution.machineAgreement` (proved by `rfl`),
  `FailureProjection.requestCutWitness_not_noFail`, and `no_countable_resource`
  now delegates to `ResourceContractLaw1.nat_encodable_resource_impossible`.
- `P6FrameControls`: a fresh represented cell (byte 64, not initially owned)
  through the actual MSTORE and Slice REVERT.

The H16 Source edits (immutables, funds) are not on master.



### Review follow-up on published master (2026-11-03)

Rebased the helper branch onto `312ed47a9ff23fd6b0e9f0206770e8deac0246e2`,
retaining its pre-rebase tip on the `-pre-312ed47a` backup branch. The request-cut
proof now retains only its working existing-law application. Six exact axiom
reports in FailureProjection, SourceRealization and P6FrameControls are checked
message pins: the request witness uses no axioms; the other five retain exactly
`propext`, `Classical.choice` and `Quot.sound`. Statements and premises are unchanged.
All three focused per-file checks and three serial MCP diagnostics pass; separate
read-only finder and skeptic reviews found no issues. No full end-of-lane pass is
claimed for this small follow-up.

The interrupted prior checkpoint container exited255, without an OOM flag or a
terminal supervisor receipt. Its empty gate ledger and partial build remain
failed/incomplete evidence. The first new check failed because the timing wrapper
lacked its output-path variable; the corrected invocation and its passing logs
are retained separately. The recovered ephemeral writer-lock directory was
restored after an initial exit66.

Existing Source runtime modules remain published-master bodies, and all15 bodies
in the 492.530-second baseline still match their recorded hashes. Imported-artifact
equality and an after-change timing table are not asserted. H16 execution and
S02/S04 core edits, their nine dependent modules and V14's later Eval patch remain
pending. H16-TX1 and H16-BAL1 are already routed to the human; no answer is assumed.
All24 original full obligations and six Source combinations remain open. No
native compiler/EVM execution occurred in this follow-up.


### H16 explicit-plan frame execution leaf (2026-11-03)

New `Source/FailureMachine.lean` runs frame cursor operations in actual Source.EM,
reusing the actual Source event emitter. Source.St gains only a typed cursor;
St.init initializes it. The immutable RuntimePlan is an explicit argument, not
a mutable state field. None does not inspect stale metadata. A reached parent
stop prevents entry, and body pre/post checks are inside attempt; scope exit
retains ordinal progress and ancestor/request stops. This is not a second
interpreter, dispatch, rollback, catch selector, receipt policy or SourceSpec.
Actual Eval/session wiring and fixed-plan consistency remain unfinished.

Fresh single-thread checking before/after on the published Source bodies:

| Source file | Before seconds | After seconds |
|---|---:|---:|
| Machine | 1.7217 | 1.6521 |
| Eval | 7.9047 | 8.0273 |
| Semantics | 0.8670 | 0.9007 |
| Horizon | 339.6516 | 339.6591 |

Commands used unchanged j1/131072 stack and hard12GiB/no swap/H1 OS reserve.
Fresh setup/import hashes and raw results are retained in frame-machine evidence.
No noticeable checking-time regression appears in these measurements. They do
not constitute a full Source closure or full build; those gates remain required.
The independent draft reviews accepted the scoped operations. Frozen controls
include an existing nonempty heap/local alias, log/event prefix, swallowed own
failure, child/ancestor/request ownership, zero cuts and exact halt bytes.
The root TX1/BAL1 choices remain pending with the human. Existing immutable/funds
patches and all24 original obligations/six general Source combinations remain open.


The frame leaf now has27 closed actual-Source controls and31 generated exact
axiom pins. They prove complete Source states, owner distinction, full panic
bytes, actual zero-horizon dispatch through sub and a nonempty caller journal
prefix preserved by actual applyOp/mark/rollbackTo. A wrong mark loses that
prefix. Cursor scope exit itself performs no logical rollback. The affected
Source Session/HorizonDeploy/legacy SourceCallFrame closure builds (32 jobs).
Full source-language/Bound/P8 and assembly adequacy remain unfinished.

H18 resolves deployment indexing: deployment consumes tx0, ordinary requests
start at tx1, with initcode frame coverage retained. H19 resolves BAL1 by
extending the monetary representation. Those questions are not pending now.
Next, Source.Account and actual balance operations must migrate under measured
checking; no field bound may substitute for the explicit EVM-reachable invariant.


### H16 consumer-constructor migration (2026-11-03)

The coordinator authorized the Source writer to mechanically migrate all
consumer construction sites affected by the new cursor. The manifest
`vy5-cursor-consumers.json` lists39 files and their owners:26 VY2,11 V08,
one V16 and one V11. Each change appends only an explicit empty cursor;
removing that addition reproduces every original file byte-for-byte. No
statement, proof body, prior state field, observation or budget changes.
Independent read-only finder/skeptic reviews found no remaining common
five-field empty-local constructor pattern. All39 per-file checks pass.
The full checkpoint follows these focused checks, rather than searching
for sites by repeating the full build. Monetary migration drafts remain
unapplied outside this checkout.

Horizon checking was339.65 seconds both before and after the Source change.
That exceeds the300-second per-module bound: kernel completion is recorded
separately from this pre-existing policy failure. This checkpoint does not
fix that baseline debt or raise its budget. The lane remains partial.

## Actual Source catch binding on published059eb83d

The branch adopted059eb83d4e1d494f42c532513ffbcd3e65adaf75. Its actual
`RStmt.tryCall` and `execS` now provide raw-bytes catch binding: older absence
reports do not describe this published tree. Named Error/Panic selection and
general Yul/raw-frame admission/adequacy remain distinct obligations.

`Yul/Composition/SourceCatchBinding` executes the existing exact
`Lowering.Readonly.SourceHistory.Try.equation`, actual CALL, catch allocRef,
then actual canonical rethrow. A typed contract local is the receiver; the
caller has an old memory alias and bool. The initial St has persistent and
transient contents, a caller nonce journal, logs, fnLocals and an event prefix.
For every byte list, both pipelines and every horizon extra+3, the result is
the exact full bytes plus independently specified complete St: old world,
journal/log/fnLocals/resource retained, ordered call/answer appended, fresh
logical bytes entry1 allocated and old alias0 retained. These are logical heap
indices, not EVM pointers or an allocation-refinement theorem. The outer EM
locals are empty; this is not a raw caller cleanup/resumption theorem.

The global uses the explicit toy Fixed and source environment strategy
answer(revert bytes), not an assumed execution result or a compiler oracle.
Twenty component laws include completed-horizon equality, complete old/new
heap readback, empty/full-panic witnesses, same-length wrong-byte distinction
and fuel0/1 timeouts. Fuel2's exact partial-event state remains unproved after
monolithic reduction hit the unchanged200000 heartbeat budget. Its statement
and failed source snapshot are retained outside the checked tree. The main
proof was factored through actual producer equations instead of raising limits.

Evidence: `/workspace/vy5-composition/source-catch-binding-20261103/`. No fresh
native comparison or full checkpoint pass is claimed here. Constructor-plan
before timings were collected, but its source functions were not edited;
current published try support was selected instead. H16 full Bound/session
execution, H19 monetary migration/shared-ledger contract, immutable/funds
release, P8 realization, all24 original obligations and six full Source
combinations remain open. Source/Lowering/Readonly producer bodies were read
only; this checkpoint adds no Source core change. Independent finder and
skeptic approved the concrete proof scope with no findings.

## H16 root execution leaf (2026-11-04)

The actual `Source.runTxWithPlan` root and fourteen both-pipeline controls
retain full selected source states, ownership and panic bytes; see
[source execution and timings](source-failure-execution.md#scheduled-root-transaction-execution-2026-11-04).
Legacy runTx remains unchanged after rejecting a slower optional-signature
draft. This is kernel Source component evidence, not native comparison,
H18/H19 session integration, P8 realization or completion of the24 original
obligations/six general combinations.
