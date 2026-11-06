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

