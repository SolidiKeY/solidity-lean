# Executable bytecode selection

| Module | Role |
|---|---|
| `Backend/Selection/Interface.lean` | Selection, frame, structured-control and same-program composition certificate statements; see [executable bytecode selection](../feature-work/executable-bytecode-selection.md). |
| `Backend/Selection/Premises.lean` | Typed G24.03 and G45.05-BR premises and G49.02 runtime-consumer statement; no external result assumed or runtime proof claimed. |
| `Backend/Selection/InterfaceV2.lean` | Versioned frame certificate requiring actual prefix capacity on an inhabited peak/room domain; V1 capacity remains insufficient. |
| `Backend/Selection/PremisesV2.lean` | Nonempty compiler premise and admitted numeric-case runtime-consumer statement; reuses the existing decoder contract. |
| `Backend/Selection/FrameCapacityV2.lean` | Required V2 capacity yields empty-tail, prefix and output bounds; inhabited identity and DUP frame certificates. |
| `Backend/Selection/InterfaceV2Controls.lean` | Actual legacy 1025-PUSH witness, V2 output/program rejection, admitted frames and false-relation/wrong-IR-result controls; no G49 proof. |
| `Backend/Selection/ScalarSequence.lean` | Bounded executable-bytecode checkpoint; typed scope and retained premises are in the module. |
| `Backend/Selection/ScalarSequenceControls.lean` | Bounded executable-bytecode checkpoint; typed scope and retained premises are in the module. |
| `Backend/Selection/ScalarSequenceFrames.lean` | Bounded executable-bytecode checkpoint; typed scope and retained premises are in the module. |
| `Backend/Selection/ScalarSequenceResources.lean` | Bounded executable-bytecode checkpoint; typed scope and retained premises are in the module. |
| `Backend/Selection/ScalarSequenceFrameControls.lean` | Inhabited V2 consumers with nonempty suffixes; corrupted-tail and hidden-peak rejection. |
| `Backend/Selection/LiteralSelection.lean` | Existing compiler-IR numeric PUSH literal to actual PUSH32 certificate, injective numeric-stack representation and full machine-frame equality; literal component only. |
| `Backend/Selection/LiteralSelectionControls.lean` | Populated-tail IR/scalar correspondence, all emitted bytes, wrong-value/encoding/tail negatives and component-local symbolic-literal refusal. |
| `Backend/Selection/ArithmeticSelection.lean` | Actual numeric IR ADD/MUL/SUB/EXP selection, success/refusal and full caller-frame preservation; wraparound, underflow, operand-order, output/tail and opcode controls; capacity remains V2. |
| `Backend/Selection/BitwiseSelection.lean` | Actual numeric IR bitwise/unsigned-comparison certificates, Boolean/word representation bridges, full-frame/underflow and width/flag/tail/opcode controls; physical capacity remains V2. |
| `Backend/Selection/UnsignedSelection.lean` | Actual numeric IR DIV/MOD/SHL/SHR certificates, zero-divisor and full-count semantics, complete-frame/underflow and boundary/order/tail/opcode controls; capacity remains V2. |
| `Backend/Selection/SignedSelection.lean` | Actual numeric IR SLT/SGT/SDIV/SMOD certificates reusing signed bridges; sign/truncation/minimum-overflow/zero/frame/underflow and opcode controls, without caller exclusions. |
| `Backend/Selection/NumericSequence.lean` | Common selector-parametric certified sequence compiler and numeric specialization; total IR/Scalar execution/fault equality and existing lowering-contract inhabitants, without capacity or byte-runtime claims. |
| `Backend/Selection/StackSelection.lean` | Native POP/DUP/SWAP IR selection, tight V2 frames and actual-prefix1024 capacity composition; conservative successful-program consumer and depth/overflow/frame/opcode controls. |
| `Backend/Selection/MixedSelection.lean` | Mixed numeric/native-stack compiler specialization, exact numeric-code compatibility, actual lowering/fault and caller-frame/prefix controls, with discriminating order mutants and explicit depth limits. |
| `Backend/FailurePaths/Interface.lean`, `Backend/FailurePaths/Premises.lean` | G38 failure-path predicates over the indexed source statement and its execution, and explicit producer boundaries (see [G38 failure paths](../feature-work/g38-failure-paths.md)). |
| `Backend/FailurePaths/Statements.lean` | Completed failure statements compiled with G21's literal recognizer and Boolean custom-error encoder. |
| `Backend/FailurePaths/Parametric.lean`, `Backend/FailurePaths/ParametricControls.lean` | Failure statements independent of the function return signature, with reference-returning controls. |
| `Backend/FailurePaths/Returns.lean` | Payload return after the actual source encoder; the encoding equation is an explicit G41 premise. |
| `Backend/FailurePaths/BooleanReturn.lean`, `Backend/FailurePaths/BooleanReturnControls.lean` | Literal Boolean return statements and executed controls. |
| `Backend/FailurePaths/TransientUnwind.lean`, `Backend/FailurePaths/TransientControls.lean` | Empty-failure transient rollback consuming P7 unchanged, with empty-failure and nonempty-refusal controls. |
| `Backend/FailurePaths/WorldUnwind.lean` | Explicit world unwind after a completed failure statement. |
| `Backend/FailurePaths/Controls.lean` | Inhabited G38 statement and payload controls. |
| `Backend/FailurePaths/ReasonCodec.lean` | Source Error(string) failures, checked emission and published G41 readback. |
| `Backend/FailurePaths/ReasonCodecControls.lean` | Inhabited G41 consumer: actual reference-signature source statements, constant-packet execution, complete readback and malformed-selector refusal. |
| `Backend/FailurePaths/TransientCallback.lean` | Selected-cell consumer of the actual registered Source callback fixture. |
| `Backend/FailurePaths/TransientComposition.lean` | G39 actual target composition: transient write, ordinary persistent/memory instructions, and a later observed same-owner read. |
| `Backend/FailurePaths/TransientSharing.lean` | G39 selected-slot sharing under supplied source frames. |
| `Backend/FailurePaths/TransientSharingControls.lean` | Nonempty-prefix sharing, reset, mixed-root and refusal controls. |
| `Bridge/SolidityBridge/AccessBridge/Interface.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryCharged.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryControls.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoad.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoadControls.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoadInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Backend/Selection/ExecutionTrace.lean` | Actual bounded byte-PC traces, scalar placement and frozen code/sequence control certificates reused by whole branch/loop realization. |
| `Backend/Selection/ExecutionTraceControls.lean` | Inhabited placed sequence after PUSH32, all-prefix capacity and wrong-PC/result/tail/underflow controls. |
| `Backend/Selection/ControlPackets.lean` | Bounded actual assembled JUMP/JUMPI/ISZERO tests, placed fetch and exact tag/byte-offset/JUMPDEST clients of existing LabelExec packets. |
| `Backend/Selection/ControlPacketControls.lean` | Inhabited assembled packet arms plus independent literal-byte controls for exact1024/hidden1025 peaks, target corruption, PC/result/tail and untaken-target behavior. |
| `Backend/Selection/BranchLayout.lean` | Static prefix views equal to existing conditional expansion and fixed-whole-items adapters for proved scalar/control packets and byte coordinates. |
| `Backend/Selection/BranchPackets.lean` | Bounded selected-body, condition, test, join and tag traces at exact whole-branch placements. |
| `Backend/Selection/BranchExecution.lean` | Frozen ControlCertificate constructor for whole conditional execution, actual selected body reachability and every prefix bound. |
| `Backend/Selection/BranchControls.lean` | Inhabited assembled true/false arms, wrong-arm/tail negatives, overwritten-condition operand execution and join-capacity refusal. |
| `Backend/Selection/LoopLayout.lean` | Static prefix views equal to existing loop expansion, head/exit tag coordinates and reused fixed-items adapters. |
| `Backend/Selection/LoopPackets.lean` | Bounded actual loop head, condition/test, arbitrary certified-body entry, backedge and exit-tag traces. |
| `Backend/Selection/LoopExecution.lean` | General body iteration/backedge and zero exit; finite StructuredExec induction and frozen whole-loop certificate. |
| `Backend/Selection/StructuredExecution.lean` | Whole-byte ControlCertificate constructor for every existing BlockShape with its explicit ExpansionRoom. |
| `Backend/Selection/LoopControls.lean` | Inhabited assembled nested-branch loop, repeated backedges/zero exit, changed condition stack and wrong-head/result/tail/header-capacity controls. |
| `Backend/Selection/Composition.lean` | Same-artifact assembly/encoding/byte execution and named decoder-premise transport; concrete compositions from proved mixed scalar selection. |
| `Backend/Selection/CompositionControls.lean` | Inhabited70-byte selector-to-runtime composition, full caller frame, independent six-step bytes, wrong artifact/tail and nonvacuous decoder-premise controls. |
| `Backend/Selection/FramedLoweringInterface.lean` | Signature-only strengthening of existing lowering: reflect arbitrary successful IR outcomes into numeric stacks, complete caller frames and zero pending skips; local proof obligation. |
| `Backend/Selection/FramedLowering.lean` | Proved scalar and sequence constructors for successful IR reflection, numeric outputs, complete caller frames and zero pending skips. |
| `Backend/Selection/IRBranchPackets.lean` | Existing G36 relative-branch emitter laws extended to arbitrary numeric conditions, retaining actual pending-skip continuation. |
| `Backend/Selection/IRBranchLowering.lean` | Constructed two-sided lowering and arbitrary-success reflection for actual relative IR branches. |
| `Backend/Selection/IRLoopPackets.lean` | Actual IR loop singleton/turn laws, finite-success extraction and abstract finite-iterator composition. |
| `Backend/Selection/IRLoopLowering.lean` | Recursive actual IR loop lowering in both directions using finite witnesses derived from loopRun and complete intermediate frames. |
| `Backend/Selection/StructuredIRComposition.lean` | Checked assembly factory consuming recursively constructed framed lowering and existing shape/room, preserving assembly refusal. |
| `Backend/Selection/StructuredIRControls.lean` | Closed nested IR-loop/branch byte compositions, independent named IR-turn witnesses, false-arm/wrong-distance and frame/escaping-skip/underflow controls. |
| `Bridge/SolidityBridge/AccessBridge/HostWriteControls.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/CalldataPackets/RawUint/Controls.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/CalldataPackets/RawUint/Execution.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Selection/P20ConsumerInterface.lean` | Statement-only assembly consumer of the published P20 pending G24 lowering field, retaining actual compilation and same assembler output. |
| `Backend/Selection/P20Consumer.lean` | H26 consumer of explicit P20 lowering into existing same-artifact composition, finite IR byte execution and false-domain refusal. |
| `Backend/Selection/P20ConsumerControls.lean` | Reused nonidentity closed Yul producer lowered to actual numeric IR and35 fetched bytes, protected suffix and dirty-word/wrong-slot negatives; no pending G24 instance. |
| `Backend/AbiEntry/CalldataWordInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Executable/CreationFreshness.lean` | Bounded v14-payments-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Executable/CreationFreshnessControls.lean` | Bounded v14-payments-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/AbiEntry/ValueGateBodyInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/AbiEntry/ValueGateInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Executable/CreationLinkIdentity.lean` | Bounded v14-payments-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Executable/CreationLinkIdentityControls.lean` | Bounded v14-payments-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/AbiEntry/OffsetChecksInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/AbiEntry/RawTailGuardInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/AbiEntry/TailGuardInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Executable/CreationReturnProducer.lean` | Bounded v14-payments-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Executable/CreationReturnProducerControls.lean` | Bounded v14-payments-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Executable/CreationReturnPartition.lean` | Complete byte observations of actual finite constructor RETURN. |
| `Backend/Executable/CreationReturnPartitionControls.lean` | Actual constructor return with all three byte classes and adjacent regions. |
| `Backend/AbiEntry/HeadCheck.lean` | Actual short-head predicate in the existing numeric bytecode slice. |
| `Backend/AbiEntry/HeadCheckInterface.lean` | Ordinary indexed ABI entry's initial selector-inclusive head predicate. |
| `Backend/AbiEntry/LengthCheck.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/AbiEntry/LengthCheckControls.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/AbiEntry/LengthCheckInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |


## V15 selected stack consumers

| Module | Role |
|---|---|
| `Bridge/SolidityBridge/RoadmapV15/P10/StackSelectionAgreement.lean` | Published one-based IR DUP/SWAP and POP certificates composed with charged fetched execution and separate complete frames. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StackSelectionControls.lean` | Every-depth DUP/SWAP and arbitrary-tail POP clients, populated whole-State expectations, ordered observations and index/resource negatives. |


| `Bridge/SolidityBridge/ExternalEvm/TryPanicOperational.lean` | Operational adapter for the H8 proof-only normalization. |
| `Bridge/SolidityBridge/ExternalEvm/TryPanicRelative.lean` | H8 relative closure over explicit missing P1/P3 producers. |
| `Bridge/SolidityBridge/ExternalEvm/TryPanicSourcePadding.lean` | H8 consumers of the published H7 logical padding supplier. |
| `Bridge/SolidityBridge/ExternalEvm/TryPanicSourceScanner.lean` | H8 original-runtime consumers of the published H7 bounded scanner. |
| `Bridge/SolidityBridge/AccessBridge/Calldata.lean` | Actual CALLDATALOAD payload and charged execution over the existing pinned state/driver, reusing its decoder, byte readers and H7 padding. |
| `Bridge/SolidityBridge/AccessBridge/ByteWorldInterface.lean` | H26 paired-load consumer signature over exact P6 byte-world producer and initial native image; no concrete producer. |
| `Bridge/SolidityBridge/AccessBridge/ByteWorldLoad.lean` | Conditional transport from initial word/byte images to intrinsic load, byte program and pinned MLOAD serialization. |
| `Bridge/SolidityBridge/AccessBridge/ByteWorldLoadControls.lean` | Inhabited all-word/pipeline images, saved-tail conditional use, literal refusal and resource-domain controls. |
| `Bridge/SolidityBridge/AccessBridge/ByteWorldNumericInterface.lean` | Additive numeric paired-load signature retaining all H26 producer and initial-image premises. |
| `Bridge/SolidityBridge/AccessBridge/ByteWorldNumeric.lean` | Existing word serializer/reader identity and exact numeric paired-load consequence, reusing the original transport. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoadExtentInterface.lean` | Additive exact MLOAD active-word and P6 touch post-image iff signatures. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoadExtent.lean` | All-offset native extent arithmetic and exact post-image boundary reusing published P6 touch. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoadExtentControls.lean` | Inhabited either-pipeline images, crossed-word expansion and aligned word-fit endpoint refusal. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoadExecutionInterface.lean` | Additive fetched charged-load/P6 payload and post-image linkage, retaining all existing access failures and budgets. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoadExecution.lean` | Derives the actual charged load, saved tail, exact raw-byte value and P6 touch post-image iff from initial images and the real gate. |
| `Backend/AbiEntry/ValueGateInterface.lean` | Intrinsic payable/non-payable gate contracts indexed by actual public compiler selection. |
| `Backend/AbiEntry/ValueGate.lean` | Typed require/value-check family, checked compiler selection and exact whole-machine intrinsic execution. |
| `Backend/AbiEntry/ValueGateControls.lean` | Inhabited context, saved-tail/protected-memory and all-word payable/nonzero rejection controls. |
| `Backend/AbiEntry/ValueGateBodyInterface.lean` | Actual checked compiler selection and exact body-result composition signatures for core-classified typed bodies. |
| `Backend/AbiEntry/ValueGateBody.lean` | Public compiler selection of typed guarded bodies and preservation of their entire intrinsic outcome. |
| `Backend/AbiEntry/ValueGateBodyControls.lean` | Context-growing mutation, protected memory/tail, blocked body and raw fault/skip controls. |
| `Backend/AbiEntry/CalldataWordInterface.lean` | Exact all-offset zero-padded semantic/source word access contracts, separate from entry span checks. |
| `Backend/AbiEntry/CalldataWord.lean` | Reuses published window padding and bounds to prove semantic/source word reader equality. |
| `Bridge/SolidityBridge/AccessBridge/AbiWordInterface.lean` | Native semantic-word and all-kind numeric validation/rejection contracts, retaining charged-load failures and budgets. |
| `Bridge/SolidityBridge/AccessBridge/AbiWord.lean` | Actual native load to indexed decoder and existing validator agreement without an assumed decoded word. |
| `Bridge/SolidityBridge/AccessBridge/AbiWordControls.lean` | Prefixed/unaligned fetched word, validation/refusal, padding/large-offset and distinct zero-fuel controls. |
| `Backend/AbiEntry/HeadCheckInterface.lean` | Emitted ordinary short-head predicate contracts with explicit initial size-word representation and no success-admission claim. |
| `Backend/AbiEntry/HeadCheck.lean` | Exact unbounded head-threshold emission, initial semantic rejection and non-vacuous Selection V2 capacity certificate. |
| `Backend/AbiEntry/HeadCheckControls.lean` | Selector/head boundaries, static/dynamic and huge metadata, semantic fuel ordering, passed-head rejection and stack-height controls. |
| `Backend/AbiEntry/OffsetChecksInterface.lean` | Signed modular tail and region emitted predicate contracts over four runtime words. |
| `Backend/AbiEntry/OffsetChecks.lean` | Exact signed/modular arithmetic emission with preserved numeric suffix and non-vacuous V2 capacity frames. |
| `Backend/AbiEntry/OffsetChecksControls.lean` | Boundary, wrapping, signed-offset, actual semantic-reference acceptance and stack-height controls. |
