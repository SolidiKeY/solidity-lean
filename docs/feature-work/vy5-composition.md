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
