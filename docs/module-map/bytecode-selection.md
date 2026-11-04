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
| `Bridge/SolidityBridge/AccessBridge/Interface.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryCharged.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryControls.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoad.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoadControls.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoadInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |

| `Backend/Selection/ExecutionTrace.lean` | Actual bounded byte-PC traces, scalar placement and frozen code/sequence control certificates; branch and loop realization remain open. |
| `Backend/Selection/ExecutionTraceControls.lean` | Inhabited placed sequence after PUSH32, all-prefix capacity and wrong-PC/result/tail/underflow controls. |

| `Backend/Selection/ControlPackets.lean` | Bounded actual assembled JUMP/JUMPI/ISZERO tests, placed fetch and exact tag/byte-offset/JUMPDEST clients of existing LabelExec packets. |
| `Backend/Selection/ControlPacketControls.lean` | Inhabited assembled packet arms plus independent literal-byte controls for exact1024/hidden1025 peaks, target corruption, PC/result/tail and untaken-target behavior. |
