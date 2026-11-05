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
| `Lowering/StorageOps/SourceWordCommutation.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained premises are in the module. |
| `Lowering/StorageOps/SourceWordCommutationControls.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained premises are in the module. |
| `Lowering/StorageOps/SourceWriteRollback.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained premises are in the module. |
| `Lowering/StorageOps/SourceWriteRollbackControls.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained premises are in the module. |
| `Lowering/StorageOps/SourceStorageCopyPrefix.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/StorageOps/SourceStorageCopyPrefixControls.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/StorageOps/ProducerInterface.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/StorageOps/ProducerInterfaceControls.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/StorageOps/SourceStorageCopyBarrier.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/StorageOps/SourceStorageCopyBarrierControls.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/StorageOps/SourceStorageCopyPayload.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/StorageOps/SourceStorageCopyPayloadControls.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/StorageOps/SourceStorageCopyEmpty.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/StorageOps/SourceStorageCopyEmptyControls.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/StorageOps/SourceNestedByteCapture.lean` | Operation-side footprints of actual nested Source capture allocations. |
| `Lowering/StorageOps/SourceNestedByteCaptureControls.lean` | Nested Source snapshots can allocate before failure. |
| `Lowering/StorageOps/SourceByteStorageCopy.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/StorageOps/SourceByteStorageCopyControls.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/StorageOps/SourceByteStorageClear.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/StorageOps/SourceByteStoragePrepared.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/StorageOps/SourceByteStoragePreparedControls.lean` | Bounded v10-storage-operations checkpoint; typed scope and retained obligations are stated in the module. |
