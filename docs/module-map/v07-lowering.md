# V07 source lowering

| Module | Purpose |
|---|---|
| `Lowering/V07/Conversions.lean`, `Lowering/V07/Controls.lean` | Implicit/explicit integer, address and UDVT conversion runs (value-level); width, sign and narrowing controls. |
| `Lowering/V07/SourceReads.lean`, `Lowering/V07/Operands.lean`, `Lowering/V07/ReadControls.lean` | Source local reads against `Val.evalT`; pure-pair order; local `DeferredSource.Operand` transport and `Thin` extension. |
| `Lowering/V07/AssignmentOperands.lean`, `Lowering/V07/AssignmentOrder.lean`, `Lowering/V07/AssignmentControls.lean` | Local assignment operand and assignment/read pairs in legacy and via-IR order; capture/drop controls. |
| `Lowering/V07/IntegerSubtraction.lean`, `Lowering/V07/AssignmentSubtraction.lean`, `Lowering/V07/AssignmentBoundaries.lean` | In-range subtraction at every width and over an assignment operand; signed and underflow boundary controls. |
| `Lowering/V07/IntegerLocalFamily.lean`, `Lowering/V07/IntegerAssignmentPrefixes.lean`, `Lowering/V07/LocalFamilyControls.lean` | Fixed-width selected local family with alias reflection; writes and arbitrary assignment prefixes. |
| `Lowering/V07/ContextMap.lean`, `Lowering/V07/ContextMapWrite.lean` | P12 `ContextMap` between Source and intrinsic contexts; `Related` and its write laws. |
| `Lowering/V07/EffectfulCondition.lean`, `Lowering/V07/P12Controls.lean`, `Lowering/V07/ConditionLoopControl.lean` | `x = y` Boolean condition transport; P12 nonvacuity controls; stale once-captured loop condition negative. |
| `Lowering/V07/ReferenceCapture.lean`, `Lowering/V07/ReferenceEffects.lean`, `Lowering/V07/ReferenceControls.lean`, `Lowering/V07/MixedAssignmentControls.lean` | Memory/storage alias captures keep `HRef`/`SRef` identity across rebinds; live mixed-reference frames. |
| `Lowering/V07/DoubleAssignment.lean`, `Lowering/V07/DoubleAssignmentFamily.lean`, `Lowering/V07/DoubleSubtraction.lean`, `Lowering/V07/DoubleControls.lean`, `Lowering/V07/DoubleNegativeControls.lean` | `(i = a) - (a = b)` under `i ≠ b`; the counterexample showing that premise is needed. |
| `Lowering/V07/AllAliasPair.lean`, `Lowering/V07/AliasRhsSubtraction.lean`, `Lowering/V07/AllAliasControls.lean` | Two assignments without disjointness; the `i = b` subtraction clause. |
| `Lowering/V07/ShortCircuit.lean`, `Lowering/V07/ShortCircuitControls.lean` | `&&`/`||` over two Boolean local assignments, all alias patterns; skipped-RHS law. |
| `Lowering/V07/UnsignedNarrowing.lean`, `Lowering/V07/UnsignedNarrowingControls.lean` | Unchecked unsigned subtraction wrap at every width; assignment-operand transport. |
| `Lowering/V07/WrappedAssignmentPair.lean`, `Lowering/V07/WrappedPairControls.lean` | Wrapped subtraction of two assignment operands, all alias patterns. |
| `Lowering/V07/GraphControls.lean`, `Lowering/V07/GraphIdentityControls.lean` | Inhabited `DeclarationGraph` certificates; distinct identity for equal-field structs. |
| `Lowering/V07/PrimitiveGraph.lean`, `Lowering/V07/PrimitiveGraphControls.lean` | Computed graph producer for int/bool/address fields. |
| `Lowering/V07/RecursiveGraph.lean`, `Lowering/V07/GraphRanks.lean`, `Lowering/V07/RecursiveGraphControls.lean` | Computed recursive graph producer (arrays, structs, mappings, enums, UDVTs) and rank monotonicity; mapping-in-memory obstruction. |
| `Lowering/V07/GraphAdmissionBoundary.lean` | Inline self-struct accepted by current metadata yet not certifiable; guarded recursive witness. |
| `Lowering/V07/P8Bindings.lean` | Consumers of the frozen `P8a.Producer`; `AcceptedGraph` at the accepted source origin. |
| `Lowering/V07/AcceptedGraphProducer.lean` | `RecursiveGraph.produce` bound to the P8a accepted source. |
| `Lowering/V07/LocationGraphInterface.lean` | Admissible-location policy, `LocationDeclarationGraph` and the per-location `Admission` target. |
| `Lowering/V07/LocationGraphLaws.lean` | Mixed-location certificates; `refusal_missing` (Source admits a memory local of a mapping struct). |
| `Lowering/V07/LocationGraphProducer.lean`, `Lowering/V07/LocationProducerControls.lean` | Computed admissible-location graph producer. |
| `Lowering/V07/RankConvergence.lean` | `rankIter` stabilization past a valid comparison rank. |
| `Lowering/V07/NodeRank.lean` | Stabilization at the node count; discharges the producer's rank check. |
| `Lowering/V07/FieldCompleteness.lean` | Graph lowering succeeds for every `GraphTypeRel` under global UDVT support. |
| `Lowering/V07/LocalFieldSupport.lean` | Same completeness with support only for traversed UDVTs. |
| `Lowering/V07/LocationGraphCompleteness.lean` | Exact ordered field output and executable location-graph success from structural correspondence, local support and comparison ranks; accepted-Source completeness remains open. |
| `Lowering/V07/ReferenceCaptureRelated.lean` | Initial context-derived reference captures, fresh context extensions and exact caller restoration. |
| `Lowering/V07/ReferenceOrderRelated.lean` | Actual pipeline-ordered reference assignment/read captures and all mapped caller bindings from initial alignment. |
| `Lowering/V07/UnsignedAddition.lean` | Actual unchecked unsigned addition, width narrowing, pipeline-ordered assignment/read capture transport and context extension. |
| `Lowering/V07/WrappedAdditionPair.lean` | Two effectful unchecked unsigned-addition operands, all local aliases, reached RHS captures and initial-derived postfamilies. |
| `Lowering/V07/UnsignedMultiplication.lean` | Unchecked unsigned multiplication over all approved widths, actual pipeline assignment/read capture transport and initial-derived postfamilies. |
| `Lowering/V07/ReferenceRegisteredControls.lean` | Closed mixed-location memory/storage capture and distinct-reference assignment clients. |
| `Lowering/V07/LocationGraphCompletenessControls.lean` | Inhabited three-node executable field/producer completeness clients and negative controls. |
| `Lowering/V07/RegisteredScalarClients.lean` | Closed actual clients for every unsigned addition/multiplication headline, including pair premise discharge and fresh context transport. |
| `Lowering/V07/WordCasts.lean` | Actual full-word integer sign casts and initial-family assignment transport |
| `Lowering/V07/WordCastControls.lean` | Inhabited cast clients, thresholds, alias/capture and mixed-reference controls |
| `Lowering/V07/ConditionalAssignments.lean` | Actual effectful conditional expressions, selected-only captures and initial context transport |
| `Lowering/V07/ConditionalControls.lean` | Inhabited conditional clients, aliases, ordered observations and bounded failure controls |
| `Lowering/V07/WrappedMultiplicationPair` | Actual effectful unsigned multiplication pairs with all local aliases |
| `Lowering/V07/WrappedMultiplicationControls` | Closed multiplication-pair clients and ordered alias/width controls |
| `Lowering/V07/SignedNarrowing.lean` | Bounded v07-lowering checkpoint; typed scope and retained premises are in the module. |
| `Lowering/V07/SignedWidthCasts.lean` | Bounded v07-lowering checkpoint; typed scope and retained premises are in the module. |
| `Lowering/V07/SignedWordSubtraction.lean` | Bounded v07-lowering checkpoint; typed scope and retained premises are in the module. |
| `Lowering/V07/UnsignedCasts.lean` | Bounded v07-lowering checkpoint; typed scope and retained premises are in the module. |
| `Lowering/V07/UnsignedWidthCasts.lean` | Bounded v07-lowering checkpoint; typed scope and retained premises are in the module. |
| `Lowering/V07/UnsignedComplement.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V07/UnsignedComplementControls.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
