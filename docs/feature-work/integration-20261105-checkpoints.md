# Scheduled lane checkpoints, 2026-11-05

These bounded source increments were integrated from master `1e367905c938186aac1680f25d1059721ddce333`. Each selected packet
passed its touched, library, trust, registration, documentation and axiom-pin
checks plus separate read-only finder and skeptic reviews. Selected Bridge
modules also passed their focused Bridge build. Statements, premises, exclusions
and proof budgets are preserved; these increments do not complete their lanes.

| Lane | Producer | Modules |
|---|---|---|
| v15-evm-agreement | `2b95a68536e9f35969ff1d1ad04a11a9017ce5ac` | `Bridge/SolidityBridge/RoadmapV15/P10/PublishedRemainder.lean`, `Bridge/SolidityBridge/RoadmapV15/P10/PublishedRemainderControls.lean` |
| v07-lowering | `6afcfc32a8dbc5ea3d66b55d4e7839298bbf1f62` | `Solidity/Lowering/V07/FixedBytesAssignment.lean`, `Solidity/Lowering/V07/FixedBytesAssignmentControls.lean` |
| v09-compiler-passes | `8d57859a7f41d0e0d0372a8a6e2c07e1abaef117` | `Solidity/Backend/Passes/ReturnedStorageCapture.lean`, `Solidity/Backend/Passes/ReturnedStorageCaptureControls.lean` |
| v11-memory-operations | `3abe04ab2ec5ec24d844986f8249ffa173238984` | `Solidity/Backend/MemoryOps/SourceRawBoolCopy.lean`, `Solidity/Backend/MemoryOps/SourceRawBoolCopyControls.lean`, `Solidity/Backend/MemoryOps/SourceRawBoolEntry.lean` |
| vy1-words | `2f2c9cacdd89a15f271c4eea703163be42d08669` | `Solidity/Yul/Checks/LocalBoolDoDivergence.lean`, `Solidity/Yul/LocalBoolDoDivergence.lean` |
| vy2-physical | `eede63765e7286329d2f9ad439112e0f47a15e5d` | `Solidity/Yul/Views/RetainedCallerHeaders.lean`, `Solidity/Yul/Views/RetainedCallerHeadersControls.lean` |
| vy3-compilation | `66bf5e0c139d1d9f357a8649d7d5bd5bc9af7d02` | `Solidity/Yul/Compilation/FramedWordLowering.lean`, `Solidity/Yul/Compilation/FramedWordLoweringControls.lean` |
| executable-bytecode | `8f642fb19755b2224bbc90c8bcd0960620e97085` | `Solidity/Backend/Selection/ArithmeticSelection.lean`, `Solidity/Backend/Selection/BitwiseSelection.lean` |
| abi-entry | `36af1d3b8c4f4fc51ce852d5e7ee2f18302565d9` | `Solidity/Backend/AbiEntry/ValueGateBodyInterface.lean`, `Solidity/Backend/AbiEntry/ValueGateInterface.lean` |
| memory-copies | `a0e9b9d59cb94f199cf293b274b4a89032722d3d` | `Solidity/Backend/MemoryCopies/NestedDefaultInterface.lean`, `Solidity/Backend/MemoryCopies/RuntimeArrayInterface.lean`, `Solidity/Backend/MemoryCopies/SelectedArrayDefaultInterface.lean` |
| memory-internal-calls | `c649305132cbfc55171637fa3b76f7a62d6c48c3` | `Solidity/Backend/FailurePaths/RuntimeGuard.lean`, `Solidity/Backend/FailurePaths/RuntimeGuardControls.lean` |
| numeric-literals | `08df5fecdce821df5e1b90a3a70a1bf62bab5308` | `Solidity/Frontend/NumericLiteralProofs/WordTable/Part03.lean`, `Solidity/Frontend/NumericLiteralProofs/WordTable/Part04.lean` |
| c3-exactness | `4a949a392f7a9087ba4f600ffa7cc3d9281be43f` | `Solidity/Frontend/C3Exactness/GraphControls.lean`, `Solidity/Frontend/C3Exactness/Identity.lean`, `Solidity/Frontend/C3Exactness/OrderObstruction.lean`, `Solidity/Frontend/C3Exactness/Renaming.lean` |
| memory-references | `add8c29eb771996dfde3b912e4a47bf3d41226ca` | `Solidity/Frontend/ExecutableAst/Memory/Reader.lean` |
| va1-decision | `3817fe576e42cbbaa1fc8ca7241be1d9db2b6219` | `Solidity/Examples/DecisionHashFamilyCheck.lean`, `Solidity/Examples/DecisionHashFiveChain.lean` |
| vo1-optimizer | `da9154696995be4a1dd8fc9bedaaed44cc79fe68` | `Solidity/Optimizer/Controls.lean`, `Solidity/Optimizer/Laws.lean`, `Solidity/Optimizer/Pass.lean`, `Solidity/Optimizer/RoadmapComposition.lean` |
| qualified-units | `2db3dfcd6a4a765ed24898d11f7ed20f04398865` | `Solidity/Frontend/QualifiedUnits/DifferentialControls.lean`, `Solidity/Frontend/QualifiedUnits/SignatureGap.lean` |
| v14-payments-bytecode | `4531b0f851befa8ceb686e08758bb6dd15801f0b` | `Solidity/Backend/Executable/CreationLinkIdentity.lean`, `Solidity/Backend/Executable/CreationLinkIdentityControls.lean` |
| v12-flow-calls | `bcfe52540e6182a1aeb0b52123d99e19efa04881` | `Solidity/Backend/InternalFlow/RuntimeFrameV3ScalarSourceCheck.lean`, `Solidity/Backend/InternalFlow/RuntimeFrameV3ScalarSourceCheckLaws.lean` |
| v13-abi-world | `63af886c12bf31398b4bdb0c339cb0c48272bc4a` | `Solidity/Lowering/V08/LiteralFailureStatementReason.lean`, `Solidity/Lowering/V08/LiteralFailureStatementReasonControls.lean` |
| v08-world-lowering | `a30c71c5225513922d598515c8264a622a541004` | `Solidity/Lowering/V08/WordCastCallable.lean` |
| v17-validation-release | `cb79b5334744c489a7e766deca687f2dff2167e5` | `Solidity/Backend/StructuredFlow/MappedBranch.lean`, `Solidity/Backend/StructuredFlow/MappedBranchControls.lean` |
| v10-storage-operations | `6ed768e281ece64d67652cffeff3ffec17cb29c5` | `Solidity/Lowering/StorageOps/SourceStorageCopyPayload.lean`, `Solidity/Lowering/StorageOps/SourceStorageCopyPayloadControls.lean` |
| vy4-world | `297e0c89646af68ac86e41401b3a050602c8c896` | `Solidity/Yul/World/ReturndataByteLoad.lean`, `Solidity/Yul/World/ReturndataByteLoadControls.lean` |
| literal-grammar | `0858098f1f278d99ca2d1b8f19100cef441f7cb0` | `Solidity/Frontend/LiteralGrammarH28/Body.lean`, `Solidity/Frontend/LiteralGrammarH28/BodyControls.lean` |
| control-tuples | `7e7ca1f3574fb78d15831a3221c16ef88c88951c` | `Solidity/Frontend/ExecutableAst/ControlTuple/Adapter.lean`, `Solidity/Frontend/ExecutableAst/ControlTuple/AdmissionControls.lean` |
| override-validation | `1f20b062f02daadf0edd74263493b67192196b7d` | `Solidity/Frontend/OverrideValidation/Selection.lean`, `Solidity/Frontend/OverrideValidation/Validity.lean` |

The coordinator receipt `sched-20261105T0200Z` keeps producer-byte hashes,
per-area review results, original failures, standard-only axiom-pin reconciliation,
combined validation and publication readback. Publication requires passing
exact-head combined gates and final independent reviews. Protected H16 Source
and frozen Core ExtCall modules are excluded. Unavailable historical seals stay
unverifiable; no evidence or seal is reconstructed.

The initial planned-path documentation repair was superseded when VC1 landed.
The combined tree retains upstream’s published assumption/profile documentation.
No declaration or proof was changed by that documentation resolution.

The [VC1 inventory reconciliation](integration-vc1-trust-20261105.md) records
the two reviewed lexical data-token fingerprints; scanner policy is unchanged.
