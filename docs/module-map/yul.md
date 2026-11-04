# Inline assembly (Yul)
| Modules | Purpose |
|---|---|
| `Yul.lean`, `Yul/Words.lean`, `Yul/Builtins.lean`, `Yul/Syntax.lean`, `Yul/ExpressionCheck.lean` | Yul library root; words, builtins, intrinsic syntax and checking ([VY1](../feature-work/inline-assembly-vy1.md)). |
| `Yul/BlockTyping.lean`, `Yul/ClosedRun.lean`, `Yul/OpenComposition.lean` | Block typing; closed fuelled execution; direct tier-A runner. |
| `Yul/WordLogic.lean`, `Yul/WordRules.lean`, `Yul/WordAdapterLogic.lean` | Shallow Lean-only word logic and raw-cell runner. |
| `Yul/RawSource.lean`, `Yul/RawSourceAdapter.lean` | Concrete bool-control Source statement adapters. |
| `Yul/Checks/**`, `Frontend/SolcJson/Yul*.lean` | Kernel controls and integer-oracle vectors; solc JSON ingress. |
| `Evm/MemoryLoopHorizon.lean`, `Evm/MemoryLoopFiniteHorizon.lean` (+`Controls`) | P5 all-depth and finite-horizon loop transport ([VY2](../feature-work/yul-physical-memory.md)). |
| `Evm/MemoryRecursiveDemandViews.lean`, `Evm/MemoryRecursiveDemandBounds.lean` | Typed recursive demand/cost cases and allocation-word bounds from computed finite heads and stopping bodies. |
| `Evm/MemoryRecursiveOneTurn.lean` | Stopping-body prefix-room reduction and full recursive loop transport with initial body room. |
| `Evm/MemoryRecursiveCert.lean`, `Evm/MemoryRecursiveCompile.lean`, `Evm/MemoryRecursiveSound.lean`, `Evm/MemoryRecursiveDispatch.lean`, `Evm/MemoryMixedLoop.lean` | Recursive and mixed-body loop certificates, compiler, correctness, dispatch fallback. |
| `Yul/Views/**` | Byte/word memory views, codecs, arrays, objects, heap inventories. |
| `Yul/Adapters/P6ByteWriteOrder{,Controls}` | Complete typed-frame disjoint byte-write commutation, metadata and empty-span controls. |
| `Yul/Adapters/MemoryBytes{,Controls}` | Exact byte-view/backend snapshot-copy and unchanged-map agreement; overlap controls. |
| `Yul/Adapters/RawPhysical{,Controls}` | Existing H11 raw-local frame to bounded P6 physical bytes; explicit readback boundaries and overlay administration |
| `Yul/Views/ComputedPlacement{,Controls}` | Checked actual-heap ordinary placement witness with exact unsupported/overflow accounting. |
| `Yul/Views/ComputedAllocation{,Controls}` | Actual Source allocation preserves computed old geometry and derives fresh extent and every-initial-H MemOK; target refinement remains separate. |
| `Yul/Views/ComputedAllocationWrite{,Controls}` | Incremental typed allocation encoding with computed geometry, whole-map/source identity and exact residual/ReservedOK transport. |
| `Yul/Views/MemoryImageOrder{,Controls}` | All existing typed image constructors: point locality, whole-map disjoint order, generic allocation/FMP order and actual Source program order. |
| `Yul/Views/MixedHeapOrder{,Controls}` | Complete typed-inventory encoding permutation/idempotence and actual unchanged source writeback, with derived separation and tail bounds. |
| `Yul/Views/InventoryDecodeOrder{,Controls}` | Fixed-candidate changed-snapshot visit permutations with exact None, actual Source result and sequential placement/history refresh. |
| `Yul/Views/InventoryCandidateOrder{,Controls}` | Derived owned-pointer candidate order, object decoder invariance, and complete candidate/visit writeback plus sequential refresh permutation. |
| `Yul/Views/InventoryReplay{,Controls}` | Successful changed-snapshot output profile and whole-source replay identity from actual type preservation and retained allocation history. |
| `Yul/Views/SnapshotHashBinding{,Controls}` | Actual source keccak after changed physical-snapshot writeback, using derived exact raw payload and preserved aliases. |
| `Yul/Views/CalldataHashBinding{,Controls}` | Actual calldata-local keccak with implicit memory allocation, clipped payload copy, complete source result and MemOK. |
| `Yul/Adapters/ComputedFrameHeap{,Controls}` | Computed geometry, canonical inventory and complete Source/frame roundtrip; allocator refinement remains separate. |
| `Yul/Adapters/**` | Source/frame-memory agreement with the P6 interface; writeback and slices. |
| `Yul/Compilation/**` | Target-side Yul compilation combinators: stack slots, lowering, opcodes, control ([VY3](../feature-work/inline-assembly-vy3.md)). |
| `Yul/Compilation/PureStatements.lean`, `Yul/Compilation/ScopedStatements.lean` | Intrinsic Yul skip/assignment/sequence and initialized/zero scope compilation; actual Yul evaluator/Scalar certificates, not full Source/G24 adequacy. |
| `Yul/Compilation/OpenExpressions.lean`, `Yul/Compilation/OpenStatements.lean`, `Yul/Compilation/ScopedRawStatements.lean` | Actual VY1 raw binding pack/evaluation/writeback consumers; same-fuel raw Yul/Scalar compilation, with typed Solidity/G24 embedding still open. |
| `Yul/Compilation/NormalControl.lean`, `Yul/Compilation/NormalStackTransport.lean` | Actual intrinsic nested-normal-control compiler evidence; complete stack-only block execution in the existing model, with native/Source/G24 adequacy open. |
| `Yul/Compilation/PhysicalStore.lean` | Actual VY2 byte-view/typed-image agreement with the existing constant-byte compiler slice; native/Source/G24/MemOK closure remains open. |
| `Yul/World/**` | Yul world interface: raw windows, observations, adapters, creation, lifecycle ([VY4](../feature-work/inline-assembly-vy4.md)). |
| `Lowering/P8/FailureProjection.lean`, `Lowering/P8/SourceRealization.lean` | Failure-plan operations on `FailureResources.Bound`; Source session machine; no P8a instance ([VY5](../feature-work/vy5-composition.md)). |
| `Yul/Composition/**` | Generic G01 stage composition with toy controls; P6 MSTORE/REVERT frame correctness. |
| `Yul/Views/NominalInventory.lean` | Bounded vy2-physical checkpoint; typed scope and retained premises are in the module. |
| `Yul/Views/NominalInventoryControls.lean` | Bounded vy2-physical checkpoint; typed scope and retained premises are in the module. |
| `Yul/Views/NominalInventoryLaws.lean` | Bounded vy2-physical checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/Yul/ControlCompleteness.lean` | Bounded vy3-compilation checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/Yul/ControlRealization.lean` | Bounded vy3-compilation checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/Yul/QuotientControl.lean` | Bounded vy3-compilation checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/Yul/QuotientControlControls.lean` | Bounded vy3-compilation checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/Yul/QuotientSelection.lean` | Bounded vy3-compilation checkpoint; typed scope and retained premises are in the module. |
| `Yul/World/SelfDestructBuiltin.lean` | Bounded vy4-world checkpoint; typed scope and retained premises are in the module. |
| `Yul/World/SelfDestructBuiltinControls.lean` | Positive and negative controls for the SelfDestructBuiltin binding; exclusions are stated in the binding module. |
| `Yul/Checks/LocalBoolDivergence.lean` | Constant-true noncompletion and false-condition/timeout controls from inhabited scoped bodies. |
| `Yul/Checks/LocalBoolWhile.lean` | Fuel-boundary, condition-effect, repeated-state and clean Source loop controls. |
| `Yul/LocalBoolDivergence.lean` | Bounded vy1-words checkpoint; typed scope and retained premises are in the module. |
| `Yul/LocalBoolWhile.lean` | Bounded vy1-words checkpoint; typed scope and retained premises are in the module. |
| `Yul/Checks/LocalBoolFor.lean` | Bounded vy1-words checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/LocalBoolFor.lean` | Bounded vy1-words checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/Yul/BranchModel.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/Yul/BranchModelControls.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedLocalAlias.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedLocalAliasControls.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |

| `Bridge/SolidityBridge/Yul/**` | VY3 concrete numeric instruction certificates, typed stack/frame and structured source/model lowering adapters; native/G24/full composition remains scoped ([lane](../feature-work/inline-assembly-vy3.md)). |

| `Bridge/SolidityBridge/Yul/LoopClassification.lean`, `Bridge/SolidityBridge/Yul/LoopSelection.lean`, `Bridge/SolidityBridge/Yul/LoopSelectionControls.lean` | Derived finite macro-prefix classification and concrete nested target-loop whole-iff selection; source/native horizons remain open. |

| `Bridge/SolidityBridge/Yul/JsonCompilation.lean`, `Bridge/SolidityBridge/Yul/JsonCompilationControls.lean` | Closed checked JSON word preparation to scoped instruction/model certificates; synthetic decoder, arithmetic and refusal controls. Source attachment, Body admission and full G24/native adequacy remain open. |

| `Bridge/SolidityBridge/Yul/ScopedControl.lean`, `Bridge/SolidityBridge/Yul/ScopedControlControls.lean` | Original Yul let/zero scopes with concrete normal structured bodies; exact source/target prefix entry and retirement, arbitrary caller tail and explicit depth-zero domain. |

| `Bridge/SolidityBridge/Yul/RecursiveScopes.lean`, `Bridge/SolidityBridge/Yul/RecursiveScopesControls.lean` | Original context/horizon-indexed recursive scope/branch/sequence compiler; same-horizon source and structured execution proofs with caller-tail preservation. |

| `Bridge/SolidityBridge/Yul/StructuredJson.lean`, `Bridge/SolidityBridge/Yul/StructuredJsonControls.lean` | Actual checked JSON to nested normal scope/switch compilation; unchanged same-horizon source/model certificates, separate admission/native/G24 obligations. |

| `Bridge/SolidityBridge/Yul/SwitchCompilation.lean`, `Bridge/SolidityBridge/Yul/SwitchCompilationControls.lean` | Original-case switch compiler component: single selector evaluation, ordered full-word matching, source/structured proofs and exact selector retirement before scoped body/default. |

| `Bridge/SolidityBridge/Yul/SwitchControl.lean`, `Bridge/SolidityBridge/Yul/SwitchControlControls.lean` | Original-statement sequence/conditional visitor over concrete switch and normal-body compilers; same-horizon source and whole-block structured execution with exact caller tails. |

| `Bridge/SolidityBridge/Yul/ScopedSwitch.lean`, `Bridge/SolidityBridge/Yul/ScopedSwitchControls.lean` | Original-statement lexical-scope adapter over concrete switch/control lowering; exact source horizons, initialized prefix entry/retirement and arbitrary caller-tail preservation. |

| `Bridge/SolidityBridge/Yul/NestedSwitch.lean`, `Bridge/SolidityBridge/Yul/NestedSwitchControls.lean` | Concrete mutual original-statement/case compiler constructing source and structured-target certificates; nested normal-word cases/defaults/scopes, exact horizons and caller-tail transport. |

| `Bridge/SolidityBridge/Yul/StructuredSwitchJsonControls.lean` | Synthetic actual JSON-to-nested-lowering/model controls, emitted-fixture prefix values and unchanged ingress refusals; exact fixture kernel certificate supplied by the NJ1 attachment module. |

| `Bridge/SolidityBridge/Yul/StructuredSwitchJsonKernelControls.lean` | Kernel-inhabited exact syntax/preparation/lowering plus packet reconstruction under the explicit remaining decoder equality; conditional constructors reused by the concrete NJ1 attachment. |

| `Bridge/SolidityBridge/Yul/StructuredSwitchJsonKernelAttachment.lean` | Exact original NJ1 decoder equality and unconditional fixed-fixture packet/compilation/source/model witnesses; existing decoder child equations, unchanged bounds20/16. |

| `Bridge/SolidityBridge/Yul/LoweredWhile{,Controls}.lean` | Actual `lowerWhile` emission to finite structured/model execution with exact pre-body/final guards; original pure AST leaf compiler witnesses, prefix/caller preservation and separate capacity/refusal controls. Not a Source FOR-loop or native/resource theorem. |

| `Bridge/SolidityBridge/Yul/NormalFor{,Controls}.lean` | Original intrinsic closed Yul normal FOR component preparation/emission; finite original evalLoop/for_ horizon proofs and matching structured/model execution, with explicit guards. Body-before-post dirty-word witness; not logical Source/G24 or native adequacy. |
