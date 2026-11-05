# Executable bytecode selection

| Module | Role |
|---|---|
| `Backend/Selection/Interface.lean` | Selection, frame, structured-control and same-program composition certificate statements; see [executable bytecode selection](../feature-work/executable-bytecode-selection.md). |
| `Backend/Selection/Premises.lean` | Typed G24.03 and G45.05-BR premises and G49.02 runtime-consumer statement; no external result assumed or runtime proof claimed. |
| `Backend/Selection/InterfaceV2.lean` | Versioned frame certificate requiring actual prefix capacity on an inhabited peak/room domain; V1 capacity remains insufficient. |
| `Backend/Selection/PremisesV2.lean` | Nonempty compiler premise and admitted numeric-case runtime-consumer statement; reuses the existing decoder contract. |
| `Backend/Selection/FrameCapacityV2.lean` | Required V2 capacity yields empty-tail, prefix and output bounds; inhabited identity and DUP frame certificates. |
| `Backend/Selection/InterfaceV2Controls.lean` | Actual legacy 1025-PUSH witness, V2 output/program rejection, admitted frames and false-relation/wrong-IR-result controls; no G49 proof. |
| `Backend/FailurePaths/Interface.lean`, `Backend/FailurePaths/Premises.lean` | G38 failure-path predicates over the indexed source statement and its execution, and explicit producer boundaries (see [G38 failure paths](../feature-work/g38-failure-paths.md)). |
| `Backend/FailurePaths/Statements.lean` | Completed failure statements compiled with G21's literal recognizer and Boolean custom-error encoder. |
| `Backend/FailurePaths/Parametric.lean`, `Backend/FailurePaths/ParametricControls.lean` | Failure statements independent of the function return signature, with reference-returning controls. |
| `Backend/FailurePaths/Returns.lean` | Payload return after the actual source encoder; the encoding equation is an explicit G41 premise. |
| `Backend/FailurePaths/BooleanReturn.lean`, `Backend/FailurePaths/BooleanReturnControls.lean` | Literal Boolean return statements and executed controls. |
| `Backend/FailurePaths/TransientUnwind.lean`, `Backend/FailurePaths/TransientControls.lean` | Empty-failure transient rollback consuming P7 unchanged, with empty-failure and nonempty-refusal controls. |
| `Backend/FailurePaths/WorldUnwind.lean` | Explicit world unwind after a completed failure statement. |
| `Backend/FailurePaths/Controls.lean` | Inhabited G38 statement and payload controls. |
| `Backend/Selection/ScalarSequence.lean` | Bounded executable-bytecode checkpoint; typed scope and retained premises are in the module. |
| `Backend/Selection/ScalarSequenceControls.lean` | Bounded executable-bytecode checkpoint; typed scope and retained premises are in the module. |
| `Backend/Selection/ScalarSequenceFrames.lean` | Bounded executable-bytecode checkpoint; typed scope and retained premises are in the module. |
| `Backend/Selection/ScalarSequenceResources.lean` | Bounded executable-bytecode checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/Interface.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryCharged.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryControls.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoad.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoadControls.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/AccessBridge/MemoryLoadInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained premises are in the module. |
| `Backend/Selection/LiteralSelection.lean` | Bounded executable-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Selection/LiteralSelectionControls.lean` | Bounded executable-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/AccessBridge/HostWriteControls.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Selection/ScalarSequenceFrameControls.lean` | Bounded executable-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/CalldataPackets/RawUint/Controls.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/CalldataPackets/RawUint/Execution.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Selection/FramedLoweringInterface.lean` | Bounded executable-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/AbiEntry/CalldataWordInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Executable/CreationFreshness.lean` | Bounded v14-payments-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Executable/CreationFreshnessControls.lean` | Bounded v14-payments-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Selection/ArithmeticSelection.lean` | Bounded executable-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Selection/BitwiseSelection.lean` | Bounded executable-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/AbiEntry/ValueGateBodyInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/AbiEntry/ValueGateInterface.lean` | Bounded abi-entry checkpoint; typed scope and retained obligations are stated in the module. |
