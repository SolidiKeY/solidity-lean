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
| `Goals/ElabTotal.lean` | The elaborator-kernel totalization goal `elabKernelTotal` (et3-elab-knot-total), open: the knot of `Syntax/Elab/Stmt.lean` satisfies its defining equations (`ElabKernelFix`, `ElabKernelNames`), admits induction over its successful runs (`ElabKernelInduction`), and the helpers it reaches keep theirs (`ElabKernelHelpers`). |
| `Examples/Goals/ElabTotal.lean` | Pinned `#roadmap_goal` open check for `elabKernelTotal`, with failing-knot controls. |
| `Goals/FrontendValidation.lean` | `frontendValidatorsExercised`: external solc execution assumptions and compositional structural acceptance guarantees; frozen inventory of 269 resolving validator names. |
| `Examples/Goals/FrontendValidation.lean` | Pinned open roadmap status for `frontendValidatorsExercised` and validator inventory length 269. |
| `Interfaces/FrontendExecution.lean` | External exact compiler artifact, successful invocation, faithful JSON and selected IR boundary; no compiler semantic correctness assumption. |
| `Interfaces/FrontendValidation.lean` | Fixed structural contracts for reader refusals and identities, JSON/arithmetic, call attachment, Yul static/safety/reference checks, and IR/data admission. |
| `Goals/{Headline,Endpoint,Loops,Hash,Panic,Taclets,Total}.lean` | One finish-line component goal per module, each owned by the lane that states or proves it. |
| `Goals/Plan.lean`, `Goals/Finish.lean` | The plan goals outside the finish line, and `projectFinished`, the conjunction of the seven components. |
| `Examples/Goals/*` | One pinned `#roadmap_goal` status check per goal module; `Finish.lean` checks the finish line's structure instead of its shrinking `blocked by` list. |
| `Finish/Assembly.lean` | `project_finished_of_open`: `projectFinished` from the two open components (`lowerLoopsCorrect`, `runCarriesPanicCodes`) and the five proved ones; not the finish claim (H798). |
| `Examples/Finish/Assembly.lean` | Axiom pin of `project_finished_of_open`; audit of the finish contract: `compilerTotal` on `ProgOk []`, the endpoint's refusals and world premises, the `Evm.run` boundary. |
| `Roadmap/G49Final/PassCorrect.lean` | H64 pass template: one `Behaviour` type, one constructive refinement `PassCorrect` (explicit `need`, forward A/F/G and backward A/G transport, environment soundness/surjectivity), `PassCorrect.trans`, the intrinsic `PassList`, its `fold` and `public_end_to_end` ([h55-g49-final-theorem.md](../feature-work/h55-g49-final-theorem.md)). |
| `Roadmap/G49Final/PassCorrectAdapters.lean` | `Behaviour.ofLang`; the one full-`Cert` adapter (`cert_adapter`) and its Lowering/Compilation/Execution/P8b carriers; the single source-end boundary (`source_from_admitted`, `source_ready`) and `PassCorrect.refines`. |
| `Roadmap/G49Final/FoldedPublic.lean` | `g49_g50_of_fold`: the conditional G49/G50 statement as a fold over the three frozen G01 passes (`pipeline`, `FoldStatement`), with the frozen `PublicCorrectness`/`SpecTransfer`; fifteen residual obligations stay explicit `PublicObligations` fields. |
| `Roadmap/G49Final/BridgeGoal.lean` | H68 owner-bridge target type `BridgeGoal` (the existing `PassCorrect` with prescribed map, bound and the entire original local conclusion), its projections and the full-`Cert` positive control `cert_bridge`; no bridge is assumed. |
| `Roadmap/G49Final/PassChain.lean` | Frozen G01 certificate-chain backfill: composes the existing Lowering, Compilation and Execution certificates at the lowered world and assembled artifact; constructs no producer. |
| `Goals/IntrinsicSession.lean` | The intrinsic-session plan goal `intrinsicSessionSemantics` (`is0-intrinsic-session`) with its `IntrinsicSession` law vocabulary, moved out of `Goals/Plan.lean` (H666). |
| `Examples/Goals/IntrinsicSession.lean` | The pinned `#roadmap_goal` check and negative controls for `intrinsicSessionSemantics`. |
| `Goals/LoweringDiagram.lean` | The `Shrink.Lowering` simulation-diagram vocabulary (`Diagram`, `CallerBound`, `productionNames`, …) that `loweringBySimulation` is stated over; no goal. |
| `Goals/LoweringSim.lean` | `loweringBySimulation`: the H517 lowering shrink goal, open (one simulation diagram over the actual production lowering on t0's fragment; session lift deferred by H556). |
| `Examples/Goals/{LoweringSim,YulLayoutView,YulLayoutPilot}.lean` | One pinned `#roadmap_goal` open check per shrink goal; `Examples/Goals/Shrink.lean` imports the three. |
| `Goals/TrustedSurfaceClosed.lean` | The plan goal `trustedSurfaceClosed` (`va1-trust-surface`), moved out of `Goals/Plan.lean` (H666). |
| `Goals/DifferentialAgreement.lean` | The plan goal `differentialAgreement` (`va3-semantic-validation`), moved out of `Goals/Plan.lean` (H666). |
| `Goals/BenchmarkBudgetsMet.lean` | The plan goal `benchmarkBudgetsMet` (`vu1-benchmarks`), moved out of `Goals/Plan.lean` (H666). |
| `Goals/FastModeAgrees.lean` | The plan goal `fastModeAgrees` (`vu2-fast-mode`), moved out of `Goals/Plan.lean` (H666). |
| `Goals/CertificateCheckSound.lean` | The plan goal `certificateCheckSound` (`vu3-certificates`), moved out of `Goals/Plan.lean` (H666). |
| `Goals/CallSummarySound.lean` | The plan goal `callSummarySound` (`vu4-modular`), moved out of `Goals/Plan.lean` (H666). |
| `Goals/GenericYulViewsPreserve.lean` | The plan goal `genericYulViewsPreserve` (`t1-yul-views-generic`), moved out of `Goals/Plan.lean` (H666). |
| `Goals/OffCriticalPath.lean` | The plan goal `controlsOffCriticalPath` (`t2-controls-off-path`), moved out of `Goals/Plan.lean` (H666). |
| `Goals/DedupStatementsPreserved.lean` | The plan goal `dedupStatementsPreserved` (`t3-dedup-rollout`), moved out of `Goals/Plan.lean` (H666). |
| `Goals/DocLintClean.lean` | The plan goal `docLintClean` (`g2-doc-lint`), moved out of `Goals/Plan.lean` (H666). |
| `Goals/DocHistoryPurged.lean` | The plan goal `docHistoryPurged` (`g3-history-purge-docs`), moved out of `Goals/Plan.lean` (H666). |
| `Goals/CommentsAsCode.lean` | The plan goal `commentsAsCode` (`g4-comments-to-code`), moved out of `Goals/Plan.lean` (H666). |
| `Goals/OpcodeEvalUniversal.lean` | The plan goal `opcodeEvalUniversal` (`v1-yul-checks-universal`) with its `OpcodeSpec` vocabulary and the three family obligations, moved out of `Goals/Plan.lean` (H666). |
| `Goals/LeanInventorySound.lean` | The plan goal `leanInventorySound` (`k1-lean-inventory`) with its `Inventory` vocabulary, moved out of `Goals/Plan.lean` (H666). |
| `Goals/YulAcceptedCompilesWithArtifact.lean` | The plan goal `yulAcceptedCompilesWithArtifact` (`y1-yul-artifact-producers`) with its `YulArtifact` accepted language, moved out of `Goals/Plan.lean` (H666). |
| `Goals/ProseRatioRuleSound.lean` | The plan goal `proseRatioRuleSound` (`pb2-prose-ratio-rule`) with its `ProseRatio` vocabulary, moved out of `Goals/Plan.lean` (H666). |
| `Goals/GoalPinSpecBase.lean` | The goal-pin vocabulary `GoalPinSpec` opened by `Goals/GoalPinsSpec.lean`, moved out of `Goals/Plan.lean` (H666). |
| `Examples/Goals/TrustedSurfaceClosed.lean` | The pinned `#roadmap_goal` check for `trustedSurfaceClosed`. |
| `Examples/Goals/DifferentialAgreement.lean` | The pinned `#roadmap_goal` check for `differentialAgreement`. |
| `Examples/Goals/BenchmarkBudgetsMet.lean` | The pinned `#roadmap_goal` check for `benchmarkBudgetsMet`. |
| `Examples/Goals/FastModeAgrees.lean` | The pinned `#roadmap_goal` check for `fastModeAgrees`. |
| `Examples/Goals/CertificateCheckSound.lean` | The pinned `#roadmap_goal` check for `certificateCheckSound`. |
| `Examples/Goals/CallSummarySound.lean` | The pinned `#roadmap_goal` check for `callSummarySound`. |
| `Examples/Goals/GenericYulViewsPreserve.lean` | The pinned `#roadmap_goal` check for `genericYulViewsPreserve`. |
| `Examples/Goals/OffCriticalPath.lean` | The pinned `#roadmap_goal` check for `controlsOffCriticalPath`. |
| `Examples/Goals/DedupStatementsPreserved.lean` | The pinned `#roadmap_goal` check for `dedupStatementsPreserved`. |
| `Examples/Goals/DocLintClean.lean` | The pinned `#roadmap_goal` check for `docLintClean`. |
| `Examples/Goals/DocHistoryPurged.lean` | The pinned `#roadmap_goal` check for `docHistoryPurged`. |
| `Examples/Goals/CommentsAsCode.lean` | The pinned `#roadmap_goal` check for `commentsAsCode`. |
| `Examples/Goals/LeanInventorySound.lean` | The pinned `#roadmap_goal` check for `leanInventorySound`. |
| `Examples/Goals/YulAcceptedCompilesWithArtifact.lean` | The pinned `#roadmap_goal` check for `yulAcceptedCompilesWithArtifact` and its `YulArtifact` controls. |
| `Examples/Goals/ProseRatioRuleSound.lean` | The pinned `#roadmap_goal` check for `proseRatioRuleSound` and its `ProseRatio` controls. |
| `Goals.lean`, `Tools/Goal.lean`, `Examples/Goals.lean` | Roadmap `@[goal]` definitions, the attribute and `#roadmap`, and pinned output, respectively. |
| `Goals/IntrinsicStorage.lean` | The storage/preimage strengthening `intrinsicStorageAccounting` (`is0-intrinsic-session`) of the intrinsic-session goal: `IntrinsicSession.Laws` plus `StorageLaws` (concrete `View.stored`, `FrameInputs`, `call_inputs`, `create_inputs` over `IntrinsicStorage.Preimages`). |
| `Examples/Goals/IntrinsicStorage.lean` | The pinned open `#roadmap_goal` check for `intrinsicStorageAccounting`, with storage layout and preimage controls. |
| `Goals/Shrink.lean` | The two H517 shrink goals, open: `yulLayoutView` (one view recursive over `Shrink.Layout`, with laws, pinned geometry and per-shape instances) and `loweringBySimulation` (one simulation diagram over the actual production lowering on t0's fragment; its `Lowering`/`PassCorrect` lift is added after the intrinsic session semantics, H556). |
| `Examples/Goals/Shrink.lean` | Pinned `#roadmap_goal` open checks for both shrink goals. |
| `Goals/LoweringSession.lean` | `Shrink.Lowering.SessionLift`, the session-level conjunct of `loweringBySimulation` (H556 A): the raw compilation and `loweredWorld`, the program-to-body binding `Bound`, `envAbs`, a `PassCorrect` into `IntrinsicSession.spec F` with resource transport `D.fuel`, and boundary storage/event agreement through `globRel` (`Agrees`); no goal. |
| `Goals/PanicRun.lean` | `panicRunOutcomes`, proved in the module by `Correctness.Panic.run_outcomes` from the existing runner lemmas: the outcome contract of the panic-carrying runner `Panic.Run.program` / `Run.stmt` (sequencing, blocks, loops, internal calls, self-catch, assertion, revert and catch data, the local V1 projections); a component of `runCarriesPanicCodes`. |
| `Goals/PanicProvenance.lean` | `panicCodeProvenance`, open: every intrinsic halt of `Panic.Run.program` / `Run.stmt` carries `siteCode origin.site`; a component of `runCarriesPanicCodes`. |
