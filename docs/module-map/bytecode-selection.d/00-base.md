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
| `Backend/Selection/P20ConsumerInterface.lean` | Frozen V1 assembly consumer plus additive V2 represented-success consumer contract, retaining actual compilation, G24 Input/Rep and joint witness. |
| `Backend/Selection/P20Consumer.lean` | Frozen V1 assembly composition and H198 V2 represented-success consumption, actual joint Input/source/Yul/target witness and false-domain refusal; no inferred stack-only lowering. |
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
| `Backend/AbiEntry/ValueGate.lean` | Typed require/value-check family, checked compiler selection and exact whole-machine intrinsic execution. |
| `Backend/AbiEntry/ValueGateControls.lean` | Inhabited context, saved-tail/protected-memory and all-word payable/nonzero rejection controls. |
| `Backend/AbiEntry/ValueGateBody.lean` | Public compiler selection of typed guarded bodies and preservation of their entire intrinsic outcome. |
| `Backend/AbiEntry/ValueGateBodyControls.lean` | Context-growing mutation, protected memory/tail, blocked body and raw fault/skip controls. |
| `Backend/AbiEntry/CalldataWord.lean` | Reuses published window padding and bounds to prove semantic/source word reader equality. |
| `Bridge/SolidityBridge/AccessBridge/AbiWordInterface.lean` | Native semantic-word and all-kind numeric validation/rejection contracts, retaining charged-load failures and budgets. |
| `Bridge/SolidityBridge/AccessBridge/AbiWord.lean` | Actual native load to indexed decoder and existing validator agreement without an assumed decoded word. |
| `Bridge/SolidityBridge/AccessBridge/AbiWordControls.lean` | Prefixed/unaligned fetched word, validation/refusal, padding/large-offset and distinct zero-fuel controls. |
| `Backend/AbiEntry/HeadCheckControls.lean` | Selector/head boundaries, static/dynamic and huge metadata, semantic fuel ordering, passed-head rejection and stack-height controls. |
| `Backend/AbiEntry/OffsetChecks.lean` | Exact signed/modular arithmetic emission with preserved numeric suffix and non-vacuous V2 capacity frames. |
| `Backend/AbiEntry/OffsetChecksControls.lean` | Boundary, wrapping, signed-offset, actual semantic-reference acceptance and stack-height controls. |
| `Bridge/SolidityBridge/AccessBridge/HeadSizeInterface.lean` | Fetched charged native calldata extent to numeric short-head consumer signature. |
| `Bridge/SolidityBridge/AccessBridge/HeadSize.lean` | Published P10 fetched extent and whole-State/X transport consumed by the existing numeric head-check compiler. |
| `Bridge/SolidityBridge/AccessBridge/HeadSizeControls.lean` | Inhabited charged native execution, protected state, short input and word-size wraparound limitation controls. |
| `Bridge/SolidityBridge/AccessBridge/MemorySizeExecutionInterface.lean` | Fetched charged MSIZE/P6 image-preserving execution and continuation contract. |
| `Bridge/SolidityBridge/AccessBridge/MemorySizeExecution.lean` | Initial-image-derived MSIZE value, complete saved stack and preserved post-image, reusing P10 execution. |
| `Bridge/SolidityBridge/AccessBridge/MemorySizeExecutionControls.lean` | Either-pipeline inhabited execution, arbitrary reserved capacity, wrong-active and short-fuel controls. |
| `Backend/AbiEntry/TailGuard.lean` | Single actual numeric program for the three guards, exact semantic reference classification and explicit V2 capacity. |
| `Backend/AbiEntry/TailGuardControls.lean` | Individual refusals, accepted signed offset, raw empty-array reference and inhabited/capacity controls. |
| `Backend/AbiEntry/RawTailGuard.lean` | All-input raw-byte numeric agreement and exact length-prefixed semantic reference result without supplied load facts. |
| `Backend/AbiEntry/RawTailGuardControls.lean` | Raw malformed/empty-array, actual signed-offset acceptance and beyond-word stride controls. |
| `Bridge/SolidityBridge/AccessBridge/EmptyCopyInterface.lean` | Arbitrary-offset zero-length CALLDATACOPY charged execution contract retaining inherited failures. |
| `Bridge/SolidityBridge/AccessBridge/EmptyCopy.lean` | Actual zero-copy identity, zero expansion/three-gas execution, continuation and preserved P6 empty-touch image. |
| `Bridge/SolidityBridge/AccessBridge/EmptyCopyControls.lean` | Host-gap/maximal offset, protected dirty memory, either-pipeline image and gas/fuel refusal controls. |
| `Backend/AbiEntry/SelectorMatchInterface.lean` | Intrinsic four-byte emitted matcher, raw complete-prefix agreement and explicit capacity contract. |
| `Backend/AbiEntry/SelectorMatch.lean` | Actual SHR/EQ execution, raw first-four-byte/source fixed-hash selector correspondence and short-prefix distinction. |
| `Backend/AbiEntry/SelectorMatchControls.lean` | Raw match/mismatch, payload invariance, padded partial collision, short-input and capacity/frame controls. |
| `Backend/AbiEntry/SelectorRoutesInterface.lean` | Public checked compiler selector-local table routing and exact reached-machine contract. |
| `Backend/AbiEntry/SelectorRoutes.lean` | Typed arbitrary table family, proved compiler admission/selection and actual first-match IR execution. |
| `Backend/AbiEntry/SelectorRoutesControls.lean` | Duplicate priority, later match/fallback, protected state, malformed fault and empty-table controls. |
| `Backend/AbiEntry/SourceRoutesInterface.lean` | Ordinary Source lookup from raw selector to checked route-result contract. |
| `Backend/AbiEntry/SourceRoutes.lean` | Input-independent tables from actual exposed declarations/body/signatures and exact Source pickFn/runtime agreement. |
| `Backend/AbiEntry/SourceRoutesControls.lean` | Both-pipeline Source body-less/collision filtering, actual compiled route/miss and short-input mismatch controls. |
| `Backend/AbiEntry/PayableRoutesInterface.lean` | Checked first-match routing with per-entry payability and terminal value rejection. |
| `Backend/AbiEntry/PayableRoutes.lean` | Public compiler selection and actual IR execution, reusing the existing value gate inside matched branches. |
| `Backend/AbiEntry/PayableRoutesControls.lean` | Zero/nonzero value, payable collision/nonmatch priority, protected state and malformed-selector controls. |
| `Backend/AbiEntry/SourcePayableInterface.lean` | Source declaration payability lookup and execution certificate. |
| `Backend/AbiEntry/SourcePayable.lean` | Source-derived payable routes, actual compiler execution and Source rejection bytes. |
| `Backend/AbiEntry/SourcePayableControls.lean` | Source mutability, collision, arbitrary-value and exact rejection controls. |
| `Backend/AbiEntry/ShortRoutesInterface.lean` | Short-input guard compiler and exact execution certificate. |
| `Backend/AbiEntry/ShortRoutes.lean` | Typed length guard and Source-linked payable routing with general short exclusion. |
| `Backend/AbiEntry/ShortRoutesControls.lean` | Short lengths, padded collision, value boundary and protected-state controls. |
| `Backend/AbiEntry/SpecialRoutesInterface.lean` | Receive/fallback continuation selection and rejection certificates. |
| `Backend/AbiEntry/SpecialRoutes.lean` | Typed special choice, declaration payability and exact Source rejection bytes. |
| `Backend/AbiEntry/SpecialRoutesControls.lean` | Receive preference, fallback value, absence and protected-state controls. |
| `Backend/AbiEntry/EntryRoutesInterface.lean` | Combined ordinary/special continuation execution certificate. |
| `Backend/AbiEntry/EntryRoutes.lean` | One typed length/ordinary/special tree with exact public compiler execution. |
| `Backend/AbiEntry/EntryRoutesControls.lean` | Precedence, terminal rejection, equal-label and saved-state controls. |
| `Backend/AbiEntry/GetterRoutesInterface.lean` | Source ordinary/getter/special precedence execution certificate. |
| `Backend/AbiEntry/GetterRoutes.lean` | Actual getter tables and full-length/short Source-linked continuation execution. |
| `Backend/AbiEntry/GetterRoutesControls.lean` | Public-variable collision, getter value refusal and Source-byte controls. |
| `Backend/AbiEntry/DispatchRefusalInterface.lean` | Exact routing refusal and Source empty-byte failure certificate. |
| `Backend/AbiEntry/DispatchRefusal.lean` | Value-aligned actual compiled rejection iff Source routing refusal. |
| `Backend/AbiEntry/DispatchRefusalControls.lean` | Inhabited refusal combinations and later short-head counterexample. |
| `Backend/AbiEntry/HeadGateInterface.lean` | Actual typed/public-compiler ABI head guard certificate. |
| `Backend/AbiEntry/HeadGate.lean` | Full-extent head-span guard with exact execution and semantic rejection. |
| `Backend/AbiEntry/HeadGateControls.lean` | Boundary, oversized-no-wrap and passed-head decoder-failure controls. |
| `Backend/AbiEntry/UnsignedGateInterface.lean` | Actual public compiler unsigned range guard certificate. |
| `Backend/AbiEntry/UnsignedGate.lean` | Unsigned uint/bool/enum guard execution and raw decoder rejection equivalence. |
| `Backend/AbiEntry/UnsignedGateControls.lean` | Dirty bits, enum/word boundaries, wide no-wrap and raw decoding controls. |
| `Backend/AbiEntry/SignedGateInterface.lean` | Actual signed cleanup compiler execution certificate. |
| `Backend/AbiEntry/SignedGate.lean` | Signed two-range guards with exact execution and raw decoder correspondence. |
| `Backend/AbiEntry/SignedGateControls.lean` | Sign-extension edges, full/wide widths and raw negative-word controls. |
| `Backend/AbiEntry/BytesGateInterface.lean` | Actual fixed-byte padding compiler execution certificate. |
| `Backend/AbiEntry/BytesGate.lean` | Fixed-byte mask validation with exact intrinsic compiler execution. |
| `Backend/AbiEntry/WordGateInterface.lean` | Unified actual compiler certificate for every existing ABI word kind. |
| `Backend/AbiEntry/WordGate.lean` | Delegated all-kind validation with raw scalar rejection equivalence. |
| `Backend/AbiEntry/WordGateControls.lean` | Unified kind acceptance/rejection, byte padding and raw value controls. |
| `Backend/AbiEntry/SingleWordGateInterface.lean` | Composed singleton value-entry guard certificate with raw representation/fuel boundary. |
| `Backend/AbiEntry/SingleWordGate.lean` | Actual head/word compiler composition and exact singleton raw decoder agreement. |
| `Backend/AbiEntry/SingleWordGateControls.lean` | Raw success/rejection, trailing bytes, head ordering, fuel and protected-state controls. |
| `Backend/AbiEntry/UIntBindingInterface.lean` | Actual compiler contract for a validated singleton uint parameter local. |
| `Backend/AbiEntry/UIntBinding.lean` | Typed uint declaration with exact compiler execution and raw semantic value agreement. |
| `Backend/AbiEntry/UIntBindingControls.lean` | Raw bound frame, dirty/width/head/fuel controls and compiled typed argument read. |
| `Backend/AbiEntry/UIntBindingBodyInterface.lean` | One-artifact uint validation, binding and core-admitted typed body contract. |
| `Backend/AbiEntry/UIntBindingBody.lean` | Public whole/body selection and exact ordered raw uint entry/body execution. |
| `Backend/AbiEntry/UIntBindingBodyControls.lean` | Checked allocating body, decoder/body failure distinction, short/fuel and saved-state controls. |
| `Backend/AbiEntry/BoolBindingInterface.lean` | Actual compiler contract for validated typed Boolean parameter binding. |
| `Backend/AbiEntry/BoolBinding.lean` | Typed Boolean declaration with exact execution, accepted-bit preservation and raw entry agreement. |
| `Backend/AbiEntry/BoolBindingControls.lean` | True/false binding, dirty-value rejection and compiled typed Boolean branch controls. |
| `Backend/AbiEntry/BoolBindingBodyInterface.lean` | One-artifact Boolean validation, binding and typed-body compiler contract. |
| `Backend/AbiEntry/BoolBindingBody.lean` | Actual whole/body selection and ordered raw Boolean entry/body execution. |
| `Backend/AbiEntry/BoolBindingBodyControls.lean` | Both-bit allocating bodies, decoder/body failure distinction and saved-state controls. |
| `Backend/AbiEntry/ValueCheckedBodiesInterface.lean` | Ordered value-check/uint-or-Boolean entry/body compiler certificates. |
| `Backend/AbiEntry/ValueCheckedBodies.lean` | Public combined compilation, early value refusal and raw typed-body agreement. |
| `Backend/AbiEntry/ValueCheckedBodiesControls.lean` | Payable/zero/nonzero ordering, malformed locals, strict decoding and body failure controls. |
| `Backend/AbiEntry/SignedBindingInterface.lean` | Actual compiler contract for validated typed signed parameter binding. |
| `Backend/AbiEntry/SignedBinding.lean` | Bit-preserving typed signed declaration, exact execution and raw signed-reading agreement. |
| `Backend/AbiEntry/SignedBindingControls.lean` | Signed boundaries, raw negative input, wide metadata and typed signed branch controls. |
| `Backend/AbiEntry/SignedEntryBodyInterface.lean` | Ordered value/signed-entry/binding/body compiler certificate. |
| `Backend/AbiEntry/SignedEntryBody.lean` | Actual signed body and value-check compilation with raw signed-local agreement. |
| `Backend/AbiEntry/SignedEntryBodyControls.lean` | Both-sign allocating bodies, early value/short rejection and decoder/body failure controls. |
| `Backend/AbiEntry/WordCarrierBindingInterface.lean` | Compiler contract for validated primitive raw-word binding into the existing uint carrier. |
| `Backend/AbiEntry/WordCarrierBinding.lean` | Actual validated primitive raw-word declaration, exact execution and raw semantic agreement. |
| `Backend/AbiEntry/WordCarrierBindingControls.lean` | Enum/cardinality, fixed-bytes padding, raw bytes, saved-state and selected carrier-read controls. |
| `Backend/AbiEntry/WordCarrierEntryBodyInterface.lean` | Compiler contract for value checking, primitive raw binding and actual typed body execution. |
| `Backend/AbiEntry/WordCarrierEntryBody.lean` | Public compiler composition of value guard, raw primitive binding and actual typed body execution. |
| `Backend/AbiEntry/WordCarrierEntryBodyControls.lean` | Whole-artifact enum/fixed-bytes bodies, failure ordering, wide metadata and saved-state controls. |
| `Backend/AbiEntry/SelectorGateBodyInterface.lean` | Actual compiler contract for an arbitrary typed selector-local guard and continuation body. |
| `Backend/AbiEntry/SelectorGateBody.lean` | Actual typed selector-local guard, exact continuation execution and Source selector-predicate adapter. |
| `Backend/AbiEntry/SelectorGateBodyControls.lean` | Distinct selector/argument/length locals using existing weakening, actual entry/body execution and raw match/miss controls. |
| `Backend/AbiEntry/SelectorBranchesInterface.lean` | Actual selector branch compilation contract retaining exact compiler join behavior. |
| `Backend/AbiEntry/SelectorBranches.lean` | Actual public compiler selector branching with exact branch join/outcome behavior. |
| `Backend/AbiEntry/SelectorBranchesControls.lean` | Existing entry versus value-checked miss branch, jump skipping, terminal validation failures and saved state. |
| `Backend/AbiEntry/CoreJoinInterface.lean` | Actual core join-removal contract under existing input representation and allocation bounds. |
| `Backend/AbiEntry/CoreJoin.lean` | Represented core join removal and selected branch outcomes from existing compiler correctness. |
| `Backend/AbiEntry/CoreJoinControls.lean` | Inhabited representation, return/revert/divergence joins and escaping raw-code counterexample. |
| `Backend/AbiEntry/CoreDispatchInterface.lean` | Finite typed-body dispatch contract with actual classifier witnesses and first-match outcome agreement. |
| `Backend/AbiEntry/CoreDispatch.lean` | Finite first-match dispatch to actual typed core bodies using represented join removal. |
| `Backend/AbiEntry/CoreDispatchControls.lean` | Heterogeneous body outputs, first/later/default dispatch, terminal collisions and saved-state controls. |
| `Backend/AbiEntry/CoreSpecialInterface.lean` | Actual typed receive/fallback body choice and value-guard compiler contract. |
| `Backend/AbiEntry/CoreSpecial.lean` | Public compiler receive/fallback body routing with terminal value guards and absent-endpoint rejection. |
| `Backend/AbiEntry/CoreSpecialControls.lean` | Inhabited receive/fallback execution, typed argument reads, terminal rejection and saved-state controls. |
| `Backend/AbiEntry/SizeBranchesInterface.lean` | Actual short/full typed-body compiler selection and exact branch outcome contracts at size four. |
| `Backend/AbiEntry/CoreJoin/Shared.lean` | Existing represented join proof shared independently of selector/decoder imports. |
| `Backend/AbiEntry/SizeBranches.lean` | Public short/full typed-body compilation and exact raw/represented branch outcomes. |
| `Backend/AbiEntry/SizeBranchesControls.lean` | Inhabited size boundaries, heterogeneous body execution, malformed input, terminal failure and escaping skip controls. |
