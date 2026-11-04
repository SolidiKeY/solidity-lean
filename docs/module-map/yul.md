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
| `Yul/LocalBoolWhile.lean`, `Yul/Checks/LocalBoolWhile.lean` | fuelled Boolean scope iteration and all-fuel clean Source agreement. |
| `Yul/LocalBoolDivergence.lean`, `Yul/Checks/LocalBoolDivergence.lean` | universal no-normal-completion laws for literal-true certified scoped loops. |
| `Yul/LocalBoolDoWhile.lean`, `Yul/Checks/LocalBoolDoWhile.lean` | body-first scoped iteration and concrete all-fuel clean Source agreement. |
| `Yul/LocalBoolDoDivergence.lean`, `Yul/Checks/LocalBoolDoDivergence.lean` | constant-true do/while noncompletion laws and guard controls. |
| `Yul/LocalBoolFor.lean`, `Yul/Checks/LocalBoolFor.lean` | Boolean initializer and context-growing for-body scope composition, without post. |
| `Yul/LocalBoolPostIter.lean`, `Yul/LocalBoolForPost.lean`, `Yul/Checks/LocalBoolForPost.lean` | scoped for posts and initializer composition. |
| `Yul/LocalBoolForNoGuard.lean`, `Yul/Checks/LocalBoolForNoGuard.lean` | exact omitted-guard Source transport and concrete scoped adapters. |
| `Yul/LocalBoolUnchecked.lean`, `Yul/Checks/LocalBoolUnchecked.lean` | unchecked/ordinary Boolean item scope composition and concrete Source laws. |
| `Yul/LocalDefaultBinding.lean`, `Yul/Checks/LocalDefaultBinding.lean` | constant-default declarations followed by certified local item bodies. |
| `Yul/LocalDefaultItems.lean`, `Yul/Checks/LocalDefaultItems.lean` | certified heterogeneous constant-default declaration sequences and concrete Source item composition. |
| `Yul/LocalDefaultUnchecked.lean`, `Yul/Checks/LocalDefaultUnchecked.lean` | unchecked heterogeneous default scopes, ordinary continuations and concrete Source composition. |
| `Yul/LocalItemWorld.lean`, `Yul/Checks/LocalItemWorld.lean` | universal raw-input world preservation for pure local item/default/unchecked execution. |
| `Yul/LocalDefaultIfElse.lean`, `Yul/Checks/LocalDefaultIfElse.lean` | conditional default scopes, concrete Source agreement and raw world preservation. |
| `Yul/LocalDefaultWhile.lean`, `Yul/Checks/LocalDefaultWhile.lean` | scoped default-loop Source agreement, raw purity and finite-normal exclusion. |
| `Yul/LocalDefaultDoWhile.lean`, `Yul/Checks/LocalDefaultDoWhile.lean` | body-first default scopes, Source agreement, raw purity and finite-normal exclusion. |
| `Yul/LocalDefaultPostIter.lean`, `Yul/Checks/LocalDefaultPostIter.lean` | scoped default for-iterations with Boolean post evaluation, Source agreement and raw purity. |
| `Yul/LocalDefaultNoGuard.lean` | Concrete default-scoped omitted-guard iterations using existing Source transport. |

| `Yul/LocalBoolFailure.lean`, `Yul/Checks/LocalBoolFailure.lean` | All-fuel raw Boolean expression/control error classification and dirty-state refusal/branch controls. |

| `Yul/LocalItemFailure.lean`, `Yul/Checks/LocalItemFailure.lean` | Statement, initialization and context-growing Boolean/default item failure classification with retained-context controls. |

| `Yul/LocalLoopFailure.lean`, `Yul/Checks/LocalLoopFailure.lean` | Scope/while failure classification and concrete all-horizon omitted-guard timeout laws, including exact Source output and a break counterexample. |

| `Yul/LocalPostHorizon.lean`, `Yul/Checks/LocalPostHorizon.lean` | Post-iteration/do-while failure classification and concrete omitted-guard post-loop horizon results. |

| `Yul/LocalLoopReductions.lean`, `Yul/Checks/LocalLoopReductions.lean` | Exact constant-loop reductions, retained do/while timeout witnesses and Source horizon output, with effectful-post/break counterexamples. |

| `Yul/Interfaces/P16.lean` | Import-only intrinsic syntax and bounded raw-local Source adapter contract freeze; no general producer instance. |

| `Yul/LocalBoolRepresentation.lean`, `Yul/Checks/LocalBoolRepresentation.lean` | Exact-word Boolean representation relation and all-fuel four-form expression congruence; dirty-word/projection/error controls. |

| `Yul/LocalBoolControlRepresentation.lean`, `Yul/Checks/LocalBoolControlRepresentation.lean` | All-fuel exact-word six-form control congruence; skipped writes, dirty observations and retained timeout updates. |

| `Yul/LocalBoolItemRepresentation.lean`, `Yul/Checks/LocalBoolItemRepresentation.lean` | All-fuel Boolean initializer/item exact-word congruence, retaining reached contexts and halt reasons. |

| `Yul/LocalBoolScopeRepresentation.lean`, `Yul/Checks/LocalBoolScopeRepresentation.lean` | Exact-word suffix restoration, scope closure and conditional congruence with retained halt contexts/guard writes. |

| `Yul/LocalBoolWhileRepresentation.lean`, `Yul/Checks/LocalBoolWhileRepresentation.lean` | All-fuel while/do-while exact-word congruence with scoped declarations and precise halted contexts. |

| `Yul/LocalBoolForRepresentation.lean`, `Yul/Checks/LocalBoolForRepresentation.lean` | All-fuel Boolean-initialized no-post for congruence, preserving initializer/body halt contexts and outer writes. |

| `Yul/LocalBoolPostRepresentation.lean`, `Yul/Checks/LocalBoolPostRepresentation.lean` | All-fuel guarded post-iteration congruence preserving body/post halt states and discarded post values. |

| `Yul/LocalBoolForPostRepresentation.lean`, `Yul/Checks/LocalBoolForPostRepresentation.lean` | All-fuel Boolean initializer/guard/post for congruence with precise scope and outer-write controls. |

| `Yul/LocalDefaultRepresentation.lean`, `Yul/Checks/LocalDefaultRepresentation.lean` | All-fuel heterogeneous default/scope/unchecked congruence with related clean/raw frames and unequal projection controls. |

| `Yul/LocalDefaultControlRepresentation.lean`, `Yul/Checks/LocalDefaultControlRepresentation.lean` | All-fuel independently indexed default branch/loop congruence with typed failure-prefix controls. |

| `Yul/LocalDefaultPostRepresentation.lean`, `Yul/Checks/LocalDefaultPostRepresentation.lean` | All-fuel default-scope post and omitted-guard congruence with post-effect/continuation controls. |

| `Yul/LocalU8Representation.lean`, `Yul/Checks/LocalU8Representation.lean` | Exact checked-u8 result/error congruence and comparison/Boolean composition, retaining per-pipeline operand order. |

| `Yul/LocalU8Horizon.lean`, `Yul/Checks/LocalU8Horizon.lean` | Exact full-run stability after non-timeout checked-u8 results, arbitrary added fuel and timeout counterexamples. |

| `Yul/LocalU8CompareHorizon.lean`, `Yul/Checks/LocalU8CompareHorizon.lean` | Exact comparison result/state stability after non-timeout, preserving operand order and invalid-operation halts. |

| `Yul/LocalBoolHorizon.lean`, `Yul/Checks/LocalBoolHorizon.lean` | Full raw-frame terminal fuel stability for base and short-circuit Boolean expressions, with selected-branch and timeout controls. |

| `Yul/LocalCompareHorizon.lean`, `Yul/Checks/LocalCompareHorizon.lean` | Concrete checked-u8 comparison and Boolean branch terminal horizon composition, retaining raw states, panic and timeout controls. |

| `Yul/LocalItemHorizon.lean`, `Yul/Checks/LocalItemHorizon.lean` | Exact final indexed raw-frame stability for completed Boolean declaration/expression lists, with multi-declaration and reached-context controls. |

| `Yul/LocalDefaultHorizon.lean`, `Yul/Checks/LocalDefaultHorizon.lean` | Exact completed heterogeneous default-item and restored-block frame stability, with numeric-prefix/dirty-local controls. |

| `Yul/LocalUncheckedHorizon.lean`, `Yul/Checks/LocalUncheckedHorizon.lean` | Completed-run stability for the existing unchecked default scope, ordinary continuation and enclosing block; distinct inner/continuation timeout frames. |

| `Yul/LocalIfHorizon.lean`, `Yul/Checks/LocalIfHorizon.lean` | Completed heterogeneous conditional-scope fuel stability using concrete guard and selected restored-block producers. |
| `Yul/Compilation/P20InterfaceV1.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Compilation/P20InterfaceV1Controls.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Agreement.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Controls.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Selected.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Source.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Target.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedLocalAliasImage.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedLocalAliasImageControls.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
