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

- Yul/LocalBoolWhile.lean and Yul/Checks/LocalBoolWhile.lean: fuelled Boolean scope iteration and all-fuel clean Source agreement.

- Yul/LocalBoolDivergence.lean and Yul/Checks/LocalBoolDivergence.lean: universal no-normal-completion laws for literal-true certified scoped loops.

- Yul/LocalBoolDoWhile.lean and Yul/Checks/LocalBoolDoWhile.lean: body-first scoped iteration and concrete all-fuel clean Source agreement.

- Yul/LocalBoolDoDivergence.lean and Yul/Checks/LocalBoolDoDivergence.lean: constant-true do/while noncompletion laws and guard controls.

- Yul/LocalBoolFor.lean and Yul/Checks/LocalBoolFor.lean: Boolean initializer and context-growing for-body scope composition, without post.

- Yul/LocalBoolPostIter.lean, Yul/LocalBoolForPost.lean and Yul/Checks/LocalBoolForPost.lean: scoped for posts and initializer composition.

- Yul/LocalBoolForNoGuard.lean and Yul/Checks/LocalBoolForNoGuard.lean: exact omitted-guard Source transport and concrete scoped adapters.

- Yul/LocalBoolUnchecked.lean and Yul/Checks/LocalBoolUnchecked.lean: unchecked/ordinary Boolean item scope composition and concrete Source laws.

- Yul/LocalDefaultBinding.lean and Yul/Checks/LocalDefaultBinding.lean: constant-default declarations followed by certified local item bodies.
