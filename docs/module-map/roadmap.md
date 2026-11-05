# Roadmap statements

| Module | What it defines |
|---|---|
| `Roadmap/Contracts.lean` | Roadmap G01: the six final source-to-bytecode contracts, observations, resourced prefix families and compositional pass certificates as statements only (`Cert.comp`, `PublicCorrectness`); no final theorem is claimed ([roadmap-g01-interfaces.md](../feature-work/roadmap-g01-interfaces.md)). |
| `Roadmap/Frontend.lean` | Roadmap G05: checked frontend certificate interfaces as statements only: raw input, parse, resolution and metadata checkers (`Chain.checked`), digests as identity (`Digests.identity`, `Digests.only_invariant`), admitted settings: solc's two pipelines (three order/coder pairs) and the empty link map ([roadmap-g05-frontend.md](../feature-work/roadmap-g05-frontend.md)). |
| `Roadmap/Evm.lean` | Roadmap G06: the pinned Osaka EVM interface as statements only: the pin and its idealizations (`pinned`), the Osaka precompile table, the shared fixed functions with the per-run hash premise and `CREATE` addresses (`Fixed`), resources as gas schedules, fuel and source failure points (`GasRes`, `FailurePoints`), frame observation (`Halt.observe`) and the core/Bridge `Certificate` ([roadmap-g06-evm.md](../feature-work/roadmap-g06-evm.md)). |
| `Roadmap/TypedRun.lean` | `typedRunPrefixes`: the fuelled typed run (`Prog.runF`) read as a G01 prefix family, kept apart from `Roadmap/Contracts.lean` so that a source semantics importing the contracts does not reach the intrinsic run. |
| `Roadmap/Controls.lean` | Roadmap G07: inhabited and negative controls for the G01 contracts: a toy source, intrinsic layer, EVM and compiler meeting `PublicCorrectness` (`toy_publicCorrectness`), and refutations of an always-reverting, a byte-altering, a data-erasing and a malformed-source-accepting compiler; `PublicCorrectness.observes`, `PublicCorrectness.rejects`, `SourceSpec.not_nonVacuous_of_no_parse`. |
| `Roadmap/V16/SSCP2/NewAllocation.lean` | Actual dynamic-new data validity and MemOK preservation, with a closed local-length consumer. |
| `Roadmap/V16/SSCP2/NewAllocationControls.lean` | Live caller references, both pipelines, exact allocation-size/timeout/refusal phases and wrong-reference controls. |
| `Roadmap/V16/SourceTransactionConsumer.lean` | Bounded actual Source transaction pairs, exact states, rollback and Hoare consumer; no compiler/session closure |
| `Bridge/SolidityBridge/RoadmapV15/P10/PublishedBitwise.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/PublishedBitwiseControls.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Roadmap/V16/CreationReturnConsumer.lean` | Bounded v16-correctness-transfer checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/PublishedRemainder.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/PublishedRemainderControls.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained obligations are stated in the module. |
