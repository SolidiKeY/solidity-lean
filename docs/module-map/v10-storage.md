# V10 storage operations

| Modules | Purpose |
|---|---|
| `Backend/StorageOps/Traversal.lean`, `Backend/StorageOps/RecursiveCopy.lean`, `Backend/StorageOps/RecursiveClear.lean`, `Backend/StorageOps/RecursivePop.lean` | Runtime-shaped graph copy/clear/pop, equal to `Value.overlay` ([V10](../feature-work/roadmap-v10-storage-operations.md)). |
| `Backend/StorageOps/CommonPrefix.lean`, `Backend/StorageOps/PrefixLaws.lean`, `Backend/StorageOps/PathOperations.lean`, `Backend/StorageOps/Commutation.lean` | Prefix transport and disjoint-path commutation. |
| `Backend/StorageOps/PathRepresentation.lean`, `Backend/StorageOps/RepresentedOperations.lean`, `Backend/StorageOps/TargetOperations.lean` | Operations against `Represented`; scalar save/copy to numeric stores and `Evm.Slot`. |
| `Backend/StorageOps/NumericTraversal.lean`, `Backend/StorageOps/CopyTransport.lean`, `Backend/StorageOps/LayoutAccess.lean` | `FiniteRun` numeric transport, footprints, G27 layout access. |
| `Backend/StorageOps/TargetArrayCopy.lean`, `Backend/StorageOps/TargetArrayClear.lean`, `Backend/StorageOps/OutputRootComplete.lean` | Structured target loops; nested-array root composition. |
| `Backend/StorageOps/RuntimeCopyRepeat.lean`, `Backend/StorageOps/RuntimeCopyComposition.lean`, `Backend/StorageOps/TargetArrayRepeat.lean` | Runtime-header repetition and footprint shrinkage. |
| `Lowering/StorageOps/SourceScalarDeleteLog.lean` | Registered above-core actual Source storage operation law/client; independent Source semantics, no whole-pipeline closure. |
| `Lowering/StorageOps/SourceArrayDeleteTarget.lean` | Registered above-core actual Source storage operation law/client; independent Source semantics, no whole-pipeline closure. |
| `Lowering/StorageOps/SourceReadFrames.lean` | Registered above-core actual Source storage operation law/client; independent Source semantics, no whole-pipeline closure. |
| `Lowering/StorageOps/SourceStorageCopy.lean` | Registered above-core actual Source storage operation law/client; independent Source semantics, no whole-pipeline closure. |
| `Lowering/StorageOps/SourceCopyFrames.lean` | Registered above-core actual Source storage operation law/client; independent Source semantics, no whole-pipeline closure. |
| `Lowering/StorageOps/SourceCopyReadbacks.lean` | Registered above-core actual Source storage operation law/client; independent Source semantics, no whole-pipeline closure. |
| `Lowering/StorageOps/SourceCopyCommutation.lean` | Registered above-core actual Source storage operation law/client; independent Source semantics, no whole-pipeline closure. |
| `Lowering/StorageOps/SourceCopyCommutationControls.lean` | Registered above-core actual Source storage operation law/client; independent Source semantics, no whole-pipeline closure. |
| `Lowering/StorageOps/SourceCopyRepeat.lean` | Registered above-core actual Source storage operation law/client; independent Source semantics, no whole-pipeline closure. |
| `Lowering/StorageOps/SourceCopyRepeatControls.lean` | Registered above-core actual Source storage operation law/client; independent Source semantics, no whole-pipeline closure. |
| `Backend/StorageOps/TargetSelfCopy.lean` | Target-only runtime self-copy; compatible legacy import and canonical exported names |
| `Lowering/StorageOps/SourceArrayDeleteNumeric.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceArrayReadback.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceBoolStorageCopy.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceBoolCopyReadbacks.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceBoolArrayDeleteNumeric.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceBoolArrayDeleteNumericControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceBoolFixedStorageCopy.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceBoolFixedStorageCopyControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceBoolFixedStorageCopyTarget.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceBoolFixedStorageCopyTargetControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceBoolStorageCopyTarget.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceBoolStorageCopyTargetControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceCopyFramesControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceFixedStorageCopy.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceIntCopyReadbacks.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceFixedStorageCopyControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceFixedStorageCopyTarget.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceFixedStorageCopyTargetControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceIntArrayDeleteNumeric.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceIntArrayDeleteNumericControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceMappingDelete.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceSelfCopy.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceSignedStorageCopyTarget.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceSignedStorageCopyTargetControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceStorageCopyControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceStorageCopyTarget.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceStorageCopyTargetControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceTwoArrayDeletes.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceTwoArrayDeleteControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceTwoArrayDeleteNumeric.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceTwoArrayDeleteNumericControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/TwoClearRepresentationControls.lean` | Actual Source storage-operation correspondence or complete ordered client above the core |
| `Lowering/StorageOps/SourceWordWrite.lean` | Actual Source scalar-word store execution and runtime-stack target correspondence |
| `Lowering/StorageOps/SourceWordWriteControls.lean` | Populated actual Source/target readbacks, ordered context and refusal/operand controls |
| `Lowering/StorageOps/SourceWordRead.lean` | Total typed Source reads and SLOAD correspondence under explicit raw input observations |
| `Lowering/StorageOps/SourceWordReadControls.lean` | Inhabited certificate and complete ordered read/context/refusal controls |
| `Lowering/StorageOps/SourceArrayIndex.lean` | Raw-header Source indexing, represented primitive read and exact bounds-failure composition |
| `Lowering/StorageOps/SourceArrayIndexControls.lean` | Inhabited representation/target inputs and complete live/retained/wrong-guard observations |
| `Lowering/StorageOps/SourceArrayWrite.lean` | Fresh Source indexed writes with PUBLIC represented frames and per-run numeric transport |
| `Lowering/StorageOps/SourceArrayWriteControls.lean` | Actual arbitrary-budget writes, retained-location distinction and complete context observations |
| `Lowering/StorageOps/SourceArrayWriteNumericControls.lean` | Concrete finite-region Source/target/represented/numeric write client and complete numeric readbacks |
| `Lowering/StorageOps/SourceArrayWriteFailure.lean` | Bounds-first actual Source panic and guarded target revert for arbitrary payload types |
| `Lowering/StorageOps/SourceArrayWriteFailureControls.lean` | Complete retained/default/raw-absence, type/static/fuel precedence controls |
| `Lowering/StorageOps/SourceArrayWriteFrameControls.lean` | Nonempty live/retained owner frames through actual Source, represented and numeric writes |
| `Backend/StorageOps/LoopLaws.lean` | Shared intrinsic loop-turn/exit/single-loop adapters with explicit operational premises |
| `Backend/StorageOps/LoopLawsControls.lean` | Populated ordered positive/negative loop controls and concrete termination witness |
| `Backend/StorageOps/StackWordWrite.lean` | Destination-only SSTORE code with runtime word operand and full context preservation |
| Other `Backend/StorageOps/*.lean`, `*Controls.lean` | Lifecycles, snapshots, cycles, fixed/nested targets; inhabited fixtures and counterexamples. |

| `Lowering/StorageOps/SourceWordCommutation.lean` | Captured typed Source writes: full-world commutation, actual execution and exact journal order |
| `Lowering/StorageOps/SourceWordCommutationControls.lean` | Heterogeneous writes, nonempty journal/locals, state-order and overlap negatives, explicit undo |

| `Lowering/StorageOps/SourceWriteRollback.lean` | Typed static refusal and actual original-mark rollback for a captured account-write poststate |
| `Lowering/StorageOps/SourceWriteRollbackControls.lean` | Full captured failure/restoration outcomes, nonempty prefixes, wrong-mark, skipped-bind and type/static order controls |

| `Lowering/StorageOps/SourceStorageCopyPrefix.lean` | Prepared-fuel actual storage-to-storage Source copy: exact runtime journal prefix or header-last success |
| `Lowering/StorageOps/SourceStorageCopyPrefixControls.lean` | Uniform and populated length/fuel controls, raw/default observations and complete outcomes/context/journal snapshots |

| `Lowering/StorageOps/SourceStorageCopyBarrier.lean` | Actual primitive capture timeout: arbitrary runtime fuel/count and full-state preservation before destination work |
| `Lowering/StorageOps/SourceStorageCopyBarrierControls.lean` | Populated complete barrier/boundary outcomes, ordered raw/default/context/journal controls and source/self-copy negatives |

| `Lowering/StorageOps/SourceStorageCopyPayload.lean` | Actual nonempty Source copy payload-boundary timeout with exact runtime write prefix |
| `Lowering/StorageOps/SourceStorageCopyPayloadControls.lean` | Complete payload-failure outcomes/journals and actual fresh-versus-retained alias readbacks |

| `Lowering/StorageOps/SourceStorageCopyEmpty.lean` | Actual primitive empty-source fuel3 boundary with header-only success or pre-clear timeout |
| `Lowering/StorageOps/SourceStorageCopyEmptyControls.lean` | Complete empty-copy outcomes/journals, raw-zero materialization and actual fresh/retained alias controls |

| `Lowering/StorageOps/SourceByteStorageCopy.lean` | Actual Source OLD byte capture and all-fuel journaled byte-write prefix, including final-write timeout |
| `Lowering/StorageOps/SourceByteStorageCopyControls.lean` | Inhabited byte capture/write clients, complete ordered outcomes/raw cells/journals and static/malformed controls |

| `Lowering/StorageOps/SourceByteStorageClear.lean` | All-fuel actual primitive byte-clear operation transport to checked scalar range |
| `Lowering/StorageOps/SourceByteStoragePrepared.lean` | Exact byte payload/clear-prefix/header-last phase execution at runtime lengths |
| `Lowering/StorageOps/SourceByteStoragePreparedControls.lean` | Actual storRef byte-copy outcomes, ordered journals, raw/default/live aliases and retained shadows |

| `Lowering/StorageOps/SourceByteStorageBarrier.lean` | Arbitrary-fuel byte capture timeout with OLD-read premises and exact full-state preservation |
| `Lowering/StorageOps/SourceByteStorageBarrierControls.lean` | Static/shifted witnesses, complete capture/destination/malformed/self ordering and unchanged journals |

| `Lowering/StorageOps/SourceNestedByteCapture.lean` | Actual empty-reference allocation and arbitrary runtime nested-capture timeout allocation prefixes |
| `Lowering/StorageOps/SourceNestedByteCaptureControls.lean` | Actual storRef nested captures separating storage/journal preservation from changed heap, old objects and static failure |

| `Lowering/StorageOps/SourceNestedByteValues.lean` | Actual distinct nonempty byte capture and runtime index allocation-prefix law at arbitrary common inner length |
| `Lowering/StorageOps/SourceNestedByteValuesControls.lean` | Full nonempty capture outcomes/headers/heaps/journals, retained tails and wrong-order negative control |

| `Lowering/StorageOps/SourceVaryingByteCapture.lean` | Actual capture prefixes with independent runtime child lengths, payloads and original per-child fuel conditions |
| `Lowering/StorageOps/SourceVaryingByteCaptureControls.lean` | Complete variable-length copy outcomes, retained tails, heap/journal observations and necessary-fuel counterexample |

| `Lowering/StorageOps/SourceByteCaptureSuccess.lean` | Successful varying-length Source capture with exact returned fresh references and heap footprint |
| `Lowering/StorageOps/SourceByteCaptureSuccessControls.lean` | Full/shifted/static/empty capture identities, complete state/journals, actual heap reads and wrong-offset control |

| `Backend/StorageOps/ProducerInterface.lean` | Explicit typed path, represented reached-state and selected-code execution endpoints for downstream consumers |
| `Backend/StorageOps/ProducerInterfaceControls.lean` | Inhabited finite-region bool SSTORE client with changed readback and preserved context |

| `Lowering/StorageOps/SourceCaptureReadback.lean` | Arbitrary capture allocation-prefix typed readbacks and preservation of all older objects |
| `Lowering/StorageOps/SourceCaptureReadbackControls.lean` | Actual full/shifted capture heap reads, dangling/type failures and complete ordered state/journal observations |
