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
