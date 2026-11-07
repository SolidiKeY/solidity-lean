
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

| `Lowering/StorageOps/SourceCapturedByteCommit.lean` | Runtime nested snapshot commit over actual Source operations, captured heap readbacks and reached-prefix headers |
| `Lowering/StorageOps/SourceCapturedByteCommitControls.lean` | Whole storage-reference copy, dirty tails, ordered journals, retained/live aliases and wrong-reference/fuel controls |

| `Lowering/StorageOps/SourceByteCommitFrames.lean` | Actual byte-operation/prefix read frames and structural OLD next-header transport |
| `Lowering/StorageOps/SourceByteCommitFramesControls.lean` | OLD-header runtime commit client, complete prefix/journal observations and visited-header/malformed-query controls |

| `Lowering/StorageOps/SourceCapturedBytePhase.lean` | Actual captured-byte child phase execution, including partial cleanup failure |
| `Lowering/StorageOps/SourceCapturedByteTimeout.lean` | Runtime successful-child prefix followed by exact cleanup timeout from OLD header observations |
| `Lowering/StorageOps/SourceCapturedByteTimeoutControls.lean` | Whole storage-reference failure, complete ordered journals, stale/older shadows and explicit rollback boundaries |

| `Lowering/StorageOps/SourceCapturedByteWriteTimeout.lean` | Actual captured payload timeout and arbitrary successful-child failure-prefix transport |
| `Lowering/StorageOps/SourceCapturedByteWriteTimeoutControls.lean` | Whole-copy empty-tail fuel boundary, unchanged headers, complete journals and explicit rollback contrasts |
