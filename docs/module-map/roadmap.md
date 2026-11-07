<!-- Generated from docs/module-map/roadmap.d/ by scripts/coord-tools/fragments.sh; edit the fragments there, not this file. -->
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
| `Bridge/SolidityBridge/RoadmapV15/P10/InstructionSelectionAgreement.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/InstructionSelectionControls.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/P8/SourceSize.lean` | Bounded v16-correctness-transfer checkpoint; typed scope and retained obligations are stated in the module. |
| `Roadmap/V16/SourceSizeControls.lean` | Bounded v16-correctness-transfer checkpoint; typed scope and retained obligations are stated in the module. |
| `Roadmap/V16/NativeRevertConsumer.lean` | Bounded v16-correctness-transfer checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/EqualityConsumer.lean` | G46.01 fetched EQ consumer of actual Scalar and pinned native definitions. |
| `Bridge/SolidityBridge/RoadmapV15/P10/EqualityControls.lean` | Populated exact native EQ states and typed equality clients. |
| `Examples/Roadmap/V16/FramedReasonConsumer.lean` | Literal source Error(string) specification consumer. |
| `Roadmap/V16/CreationLibrarySpec.lean` | Bounded v16-correctness-transfer checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/InvocationEnvironment.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/InvocationEnvironmentControls.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/PublishedShifts.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/PublishedShiftsControls.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Roadmap/G49Final/PassCorrect.lean` | H64 pass template: one `Behaviour` type, one constructive refinement `PassCorrect` (explicit `need`, forward A/F/G and backward A/G transport, environment soundness/surjectivity), `PassCorrect.trans`, the intrinsic `PassList`, its `fold` and `public_end_to_end` ([h55-g49-final-theorem.md](../feature-work/h55-g49-final-theorem.md)). |
| `Roadmap/G49Final/PassCorrectAdapters.lean` | `Behaviour.ofLang`; the one full-`Cert` adapter (`cert_adapter`) and its Lowering/Compilation/Execution/P8b carriers; the single source-end boundary (`source_from_admitted`, `source_ready`) and `PassCorrect.refines`. |
| `Roadmap/G49Final/FoldedPublic.lean` | `g49_g50_of_fold`: the conditional G49/G50 statement as a fold over the three frozen G01 passes (`pipeline`, `FoldStatement`), with the frozen `PublicCorrectness`/`SpecTransfer`; fifteen residual obligations stay explicit `PublicObligations` fields. |
| `Roadmap/G49Final/BridgeGoal.lean` | H68 owner-bridge target type `BridgeGoal` (the existing `PassCorrect` with prescribed map, bound and the entire original local conclusion), its projections and the full-`Cert` positive control `cert_bridge`; no bridge is assumed. |
| `Roadmap/G49Final/PassChain.lean` | Frozen G01 certificate-chain backfill: composes the existing Lowering, Compilation and Execution certificates at the lowered world and assembled artifact; constructs no producer. |

# VX1 full-scope proposal leaf

| Module | What it defines |
|---|---|
| `Language/EnvironmentFields/Contracts.lean` | Provisional G01 D1–D6/H38 byte-memory, artifact/oracle and run-indexed contracts in the preserved FullScope namespace; no producer certificate or freeze. |
| `Language/EnvironmentFields/ContractControls.lean` | Inhabited and falsifying toy models for unsafe writeback, opacity, exact compilation, artifact soundness, oracle linkage and optimizer refinement; independent of production Source/EVM adequacy. |
| `Language/EnvironmentFields/Frozen.lean` | Frozen version 1 (`Solidity.Roadmap.FullScope.V1`) of the G01 full-scope relation contracts D1–D6 and their bundle `Contract`, with the D1 oracle, D5, D1→D6, totality and adequacy lemmas; changes go to a new `V2` namespace (H57). |
| `Language/EnvironmentFields/FrozenControls.lean` | One toy model inhabiting the whole V1 bundle with live domains (joint satisfiability, H62/H69), and negative controls: rejecting compiler, always-reverting target, empty or shifted physical relation, overlapping fields, unsafe-block rewriting. |
