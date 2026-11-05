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

| `Bridge/SolidityBridge/Yul/DirectMemory{,Controls}.lean` | Direct MSTORE versus VY2 byte view/materializer; real typed-image framing and canonical hash composition; exact all-prefix local capacity. Native host-writer/global MemOK/Source-G24 closure remains open. |

| `Bridge/SolidityBridge/Yul/ForSource.lean` | Shared original finite-loop source law with explicit normal body/post laws; concretely discharged by NormalFor and StructuredFor. No new source syntax or state. |
| `Bridge/SolidityBridge/Yul/StructuredFor{,Controls}.lean` | Branch/sequence-aware original FOR component compilation, finite closed-source/structured/model proofs; actual high-only-word branch and zero-exit witnesses. Full G24/native/admission/early-flow/divergence remains open. |

| `Bridge/SolidityBridge/Yul/ForPrefixes{,Controls}.lean` | Actual compiled FOR all-horizon source noncompletion and exact finite model macro-turn transport; real branch-bearing invariant, caller/frame preservation and whole selected noncompletion denotation. Not native prefixes/exception correspondence or general Source-G24. |

| `Bridge/SolidityBridge/Yul/ForCompletion{,Controls}.lean` | Extract first-zero count/normal output from any actual successful original FOR horizon; exact source-output to real emission/selected model transport without caller-supplied stopping count. Branch/zero/horizon/noncompletion controls; no native/G24/capacity adequacy. |

| `Bridge/SolidityBridge/Yul/StructuredUnique.lean` | Determinism of the unchanged finite StructuredExec relation, including branches/loops; no new target evaluator. |
| `Bridge/SolidityBridge/Yul/ForReflection{,Controls}.lean` | Recover guard/count/exact locals from actual finite FOR target evidence, then original source completion from structured/selected model success; full frame/pending-zero and noncompletion/capacity controls. Not native/G24 adequacy. |

| `Yul/Compilation/P20InterfaceV1{,Controls}.lean` | H26 closed-normal success interface: reuses real closed compiler certificates; uninstantiated G24 source/link/represented-success laws with genuine success and represented/payment-free witness fields. Not full P20 adequacy. |

| `Bridge/SolidityBridge/Yul/ForShape{,Controls}.lean` | Actual compiled FOR numeric operand/height and all-prefix capacities; exact existing BlockShape threshold h+2<=1024 for h>=5, separate ExpansionRoom and caller boundaries. No ControlCertificate.realize/native/G24 claim. |

| `Bridge/SolidityBridge/Yul/ScopedFor{,Controls}.lean` | Actual scope/switch component compilation within original FOR; concrete prepare/emission/selection, finite source/whole structured/model proofs, scoped-temp/order-sensitive dirty-word and early-flow refusals. Depth0/caller-only frame; full frontend/G24/native closure open. |

| `Bridge/SolidityBridge/Yul/ForCompletionSource.lean` | Shared original-loop completion induction with explicit normal source laws; actual old/new compiler clients discharge both premises, not a final simulation interface. |
| `Bridge/SolidityBridge/Yul/ScopedForCompletion{,Controls}.lean` | Actual scope/switch FOR source success at arbitrary horizon derives count/guards/normal exact output and selected-model transport; no supplied stopping count or minimum horizon. Source10/all-input witness and horizon/order refusals. |

| `Bridge/SolidityBridge/Yul/ScopedForReflection{,Controls}.lean` | Actual scope/switch FOR finite target-to-original-source reflection; source horizon recovered from target, exact raw locals/caller/full model frame and pending0. Model/native capacity separation and order refusals; no G24/native adequacy. |

| `Bridge/SolidityBridge/Yul/ScopedForAdequacy{,Controls}.lean` | Exact-output iff and all-horizon source noncompletion iff selected-model fault for actual closed normal scope/switch FOR packets; genuine literal-true unending compiler witness. Denotational model only, not native/G24/resource adequacy. |

| `Bridge/SolidityBridge/Yul/ScopedForPrefixes{,Controls}.lean` | Actual scope/switch FOR finite model macro-turn prefixes with exact raw locals/caller/full-frame preservation; separate concrete prelude execution, universal unending prefixes and bounded modular-wrap controls. Not fetched/native prefixes or G24/resource adequacy. |

| `Yul/Compilation/ShapeCapacity{,Controls}.lean` | Constructive actual scalar execution from intrinsic CodeShape, generic caller framing and static height lifting, exact all-boundary shifted capacity; actual last-slot dirty update and underflow/peak-overflow separation. Target preparation, not native/G24 adequacy. |

| `Yul/Compilation/ExpressionShapes{,Controls}.lean` | Actual literal/local/binary emitted-code operand certificates, with explicit primitive row and child metadata; original intrinsic SUB visitor/source/target, shifted DUP16, raw order/caller and capacity-versus-underflow controls. Not full native/G24/compiler coverage. |

| `Yul/Compilation/ArithmeticVisitorShapes{,Controls}.lean` | Actual successful ProducerExpressions arithmetic visitor/emission derives recursive operand metadata without public child/primitive-row assumptions; nested original MUL/ADD/SUB source/target, shifted access and peak-three controls. Wider visitors/native/G24 remain separate. |

| `Yul/Compilation/StatementVisitorShapes{,Controls}.lean` | Actual normal statement visitor/emission derives balanced CodeShape, closing RHS metadata/slot range/recursive children; dependent two-assignment source/target witness, shifted prefix/caller and peak-three controls. Wider control/native/G24 remain separate. |

| `Yul/Compilation/WordVisitorShapes{,Controls}.lean` | Actual word visitor/emission derives operand metadata for arithmetic, unsigned quotients, comparisons and unary word operations; mixed DIV/MOD/EQ/NOT source/target, universal zero-divisor/full-complement and access/capacity controls. Wider pure/native/G24 remain separate. |

| `Yul/Compilation/P20InterfaceV1.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Compilation/P20InterfaceV1Controls.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Agreement.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Controls.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Selected.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Source.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/PrimitivePackets/CheckedAdd/Target.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Interfaces/P16.lean` | Bounded vy1-words checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedLocalAliasImage.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedLocalAliasImageControls.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Checks/LocalBoolDoWhile.lean` | Bounded vy1-words checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/LocalBoolDoWhile.lean` | Bounded vy1-words checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedCallerCoverage.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedCallerCoverageControls.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Compilation/ShapeCapacity.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Compilation/ShapeCapacityControls.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/World/CreationReturnWindow.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/World/CreationReturnWindowControls.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |

| `Yul/Compilation/ClzShapes{,Controls}.lean` | Operand shapes and exact every-boundary capacity for the existing256-step software CLZ; intrinsic Code packet, exact4867 size, dirty/zero/caller and underflow/1024-boundary controls. Explicit child-shape premise in lowering helper; no native/G24 closure. |

| `Yul/Compilation/ArityShapes.lean` | Existing copied-argument/inline/unary/ternary operand transport with explicit child/body metadata and physical rows; not function-frame or capacity correctness. |
| `Yul/Compilation/PureVisitorShapes{,Controls}.lean` | Actual full pure visitor success/emission derives recursive operand metadata, including ternary and software BYTE/CLZ; original closed-Yul source/target conjunction, separately capacity-checked packet, dirty-index and unbounded modular controls. No logical Source/G24/native closure. |

| `Yul/Compilation/PureAssignmentShapes{,Controls}.lean` | Actual full-pure assignment and two-assignment sequence operand producers, original closed-source/update/run transport and separately capacity-checked packets; dirty read-after-write and physical SWAP16 controls. Reuses the existing statement assignment proof; no general statement/native/G24 closure. |

| `Yul/Compilation/ScopedVisitorShapes{,Controls}.lean` | Actual scoped visitor success derives operand metadata for skip/sequence/full-pure assignment/singleton let/arbitrary zero prefixes; original closed-source/update/run, independently capacity-checked packets and nested/17-local access controls. Scope emission keeps its depthzero restriction; no native/G24/general-control closure. |

| `Yul/Compilation/NumericExecution{,Controls}.lean` | General success transport for unchanged ten-operator NumericMachine selection plus stack operations; real lowerer/original closed-Yul compiler consumers discharge scalar-run premises, preserve symbolic caller/nonstack fields. Actual21-instruction/all-ten-operator and scoped-update controls; no native/byte/PC/gas/capacity/G24 closure. |

| `Yul/Compilation/NormalNumericTransport{,Controls}.lean` | Whole numeric normal branch/sequence execution using existing compiler derivations and selector; same-horizon closed-Yul result, symbolic caller/newer-prefix preservation, high-bit/shifted-slot/refusal controls. Capacity, native execution and Source/G24 adequacy remain separate. |

| `Yul/Compilation/WordExecution{,Controls}.lean` | General unchanged WordMachine success transport, six additional word-step laws and real expression/statement source/compiler consumers; combined dirty-word, dependent-write, symbolic-tail and DUP16 controls. Native/resource and Source/G24 adequacy remain separate. |

| `Yul/Compilation/NormalWordTransport{,Controls}.lean` | Whole normally completing branch/sequence execution under the existing WordControl selector and actual compiler derivations; original closed-source result, raw EXP guard/EQ join, dependent writes, symbolic framing and shifted-slot controls. No native/resource/general-loop/G24 closure. |

| `Yul/Compilation/SignedExecution{,Controls}.lean` | General existing SignedMachine success transport consuming concrete signed producers plus WordExecution; original-source/compiler consumers, signed corner cases, dirty words, dependent writes, symbolic framing and shifted DUP16 controls. Native/resource and Source/G24 adequacy remain separate. |

| `Yul/Compilation/WhileWordExecution{,Controls}.lean` | Concrete unchanged word-selected lowerWhile turns, finite running prefixes/exits, whole model execution and all-prefix model fault; actual emitter consumer without abstract realization, raw-word counter/NOT/zero/boundary controls. No source-divergence/native/resource/G24 adequacy. |

| `Bridge/SolidityBridge/Yul/WordForExecution{,Controls}.lean` | Existing original normal FOR source theorem composed with concrete WordControl-selected prelude/loop execution, without abstract realization callback; general raw-local/newer/symbolic-tail, ordered post, horizon and access controls. Native/resource/Source-G24 closure remains separate. |

| `Yul/Compilation/WordBlockExecution.lean` | Forward actual finite StructuredExec transport under unchanged WordControl selection, one-sided branches and real loop witnesses; symbolic caller/nonstack preservation. No termination/failure iff/native/G24 claim. |
| `Bridge/SolidityBridge/Yul/WordStructuredCompilation{,Controls}.lean` | Actual nested scope/switch and scoped FOR source/compiler consumers of concrete structured word execution, without realization callbacks; original horizon13/10, selector mutation, lexical scratch, symbolic framing and skipped bad/endless-arm controls. |
| `Yul/Checks/LocalBoolDoDivergence.lean` | Bounded vy1-words checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/LocalBoolDoDivergence.lean` | Bounded vy1-words checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedCallerHeaders.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Views/RetainedCallerHeadersControls.lean` | Bounded vy2-physical checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Compilation/FramedWordLowering.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/Compilation/FramedWordLoweringControls.lean` | Bounded vy3-compilation checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/World/ReturndataByteLoad.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Yul/World/ReturndataByteLoadControls.lean` | Bounded vy4-world checkpoint; typed scope and retained obligations are stated in the module. |
