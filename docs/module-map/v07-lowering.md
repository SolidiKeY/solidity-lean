<!-- Generated from docs/module-map/v07-lowering.d/ by scripts/coord-tools/fragments.sh; edit the fragments there, not this file. -->
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
| `Lowering/V07/UnsignedLocalUpdate.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V07/UnsignedLocalUpdateControls.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V07/P12NextInterface.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V07/FixedBytesAssignment.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V07/FixedBytesAssignmentControls.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V07/IntegerConstantControls.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V07/IntegerConstants.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V07/IntegerConstantAssignment.lean` | Literal assignment uses existing source locations and intrinsic typed writes. |
| `Lowering/V07/IntegerConstantAssignmentControls.lean` | Scoped proofs and retained obligations for IntegerConstantAssignmentControls. |
| `Lowering/V07/P12AssignedCondition.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V07/P12AssignedConditionControls.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V07/P12ContextExtension.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V07/P12ContextExtensionControls.lean` | Bounded v07-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V07/SignedSubtractionControls.lean` | Signed subtraction clients, boundaries, capture/sign negatives and mixed frames |

| `Lowering/V07/HeadlineAxioms.lean` | Registered exact axiom guards for selected scalar, effect, reference and structural graph headlines |

| `Lowering/V07/SignedWordAddition.lean` | Actual full-range unchecked int256 addition and initial-family effect transport |
| `Lowering/V07/SignedWordMultiplication.lean` | Actual full-range unchecked int256 multiplication and initial-family effect transport |
| `Lowering/V07/SignedArithmeticControls.lean` | Inhabited signed add/multiply clients, boundaries, captures, frames and wrong-program controls |

| `Lowering/V07/UnsignedCastControls.lean` | All unsigned widths, capture order, caller identity and live-reference frames |

| `Lowering/V07/UnsignedWidthCastControls.lean` | All unsigned width pairs, cast order and caller frame controls |
| `Lowering/V07/SignedWidthCastControls.lean` | Signed thresholds, all width pairs, negative extension and caller frame controls |
| `Lowering/V07/SignedNarrowAddition.lean` | Unchecked signed addition at every approved width, with initial-family effect transport |
| `Lowering/V07/SignedNarrowSubtraction.lean` | Unchecked signed subtraction at every approved width, preserving operand positions |
| `Lowering/V07/SignedNarrowMultiplication.lean` | Unchecked signed multiplication at every approved width, including wide intermediate overflow |
| `Lowering/V07/SignedNarrowArithmeticControls.lean` | Inhabited all-width arithmetic clients, captures, checked-classification and wrong-program controls |
| `Lowering/V07/SignedNegation.lean` | Actual unchecked signed negation at all widths, local/reached-state laws and minimum-value controls |
| `Lowering/V07/SignedNegationEffects.lean` | Actual unchecked negation of local assignment, fresh result capture and initial alias-family transport. |
| `Lowering/V07/SignedNegationEffectControls.lean` | Inhabited alias/context/mixed-reference clients, ordered observations and incorrect capture/store/narrowing controls. |
| `Lowering/V07/SignedComplement.lean` | All-width signed bitwise complement through actual Source unary evaluation and typed subtraction; initial-family local transport. |
| `Lowering/V07/SignedComplementControls.lean` | Both checkedness modes/pipelines, all signed widths, live-context clients and missing-minus-one/reversed-operand controls. |
| `Lowering/V07/SignedLocalUpdate.lean` | Actual unchecked local signed prefix/postfix increment/decrement with fresh old/result captures and derived alias-family updates. |
| `Lowering/V07/SignedLocalUpdateControls.lean` | All signed widths, MAX/MIN wrap and missing-narrowing controls, mixed caller/context clients and actual pipeline observations. |
| `Lowering/V07/UnsignedQuotRem.lean` | Actual unsigned division/remainder, derived result bounds and initial-family local transport; distinct Source/native zero observations. |
| `Lowering/V07/UnsignedQuotRemControls.lean` | All widths/modes/pipelines, zero and reversed-operand controls, inhabited alias/context/live-reference clients and payload mismatch witness. |
| `Lowering/V07/UnsignedQuotRemGuard.lean` | Published division panic guards, exact Source panic payloads, fresh result capture and initial-family success/failure local transport. |
| `Lowering/V07/UnsignedQuotRemGuardControls.lean` | Guard metadata, all-width/mode/pipeline cases, live caller/context clients and exact wrong-code/plain-revert/drop controls. |
| `Lowering/V07/UnsignedQuotRemEffects.lean` | Effectful assignment/read quotient and remainder transport with actual pipeline captures and panic payloads. |
| `Lowering/V07/UnsignedQuotRemEffectsControls.lean` | Inhabited ordered alias, zero-divisor, context and mixed-reference controls. |
| `Lowering/V07/UnsignedQuotRemPass.lean` | Exact published panic insertion for pure and effectful quotient/remainder clauses, with independent Source transport. |
| `Lowering/V07/UnsignedQuotRemPassControls.lean` | Inhabited pass clients, alias/context controls and ordered payload negatives. |
| `Lowering/V07/LessThan.lean` | Signed/unsigned less-than and actual assignment/read Source transport with fresh captures. |
| `Lowering/V07/LessThanControls.lean` | Inhabited boundaries, alias/context/frame and operand-order controls. |
| `Lowering/V07/NumericComparisons.lean` | All six numeric comparison clauses with actual Source transport, ordered captures and panic-pass identity. |
| `Lowering/V07/NumericComparisonControls.lean` | Inhabited operators, signed/width boundaries, alias/context and ordered observation controls. |
| `Lowering/V07/BooleanComparisons.lean` | Boolean equality/inequality transport with heterogeneous caller and capture-context frames. |
| `Lowering/V07/BooleanComparisonControls.lean` | Inhabited mixed-reference, alias/context, effect-order and wrong-binding controls. |
| `Lowering/V07/AddressConversions.lean` | Existing-carrier address/uint160 value and actual expression/local/assignment conversion certificates. |
| `Lowering/V07/AddressConversionControls.lean` | Inhabited mixed-reference conversion, admission-refusal, alias and capture-lifetime controls. |
| `Lowering/V07/AddressComparisons.lean` | Six address comparison clauses over independent Source execution and existing native captures; initial canonical context alignment. |
| `Lowering/V07/AddressComparisonControls.lean` | Inhabited address comparison, context-extension and ordered negative controls with exact axiom guards. |
| `Lowering/V07/AddressQualifiers.lean` | Actual payable/explicit-erasure assignment transport from canonical initial context alignment. |
| `Lowering/V07/AddressQualifierControls.lean` | Inhabited both-qualifier, mixed-reference, composition and capture controls. |
| `Lowering/V07/EnumConversions.lean` | Existing enum/uint256 successful assignment transport and exact Source-only invalid-cast observations, with explicit representation obligations. |
| `Lowering/V07/EnumConversionControls.lean` | Real enum-declaration, mixed-reference, alias, full-panic and oversized-layout countercontrols. |
| `Lowering/V07/EnumGuard.lean` | Native enum range guard and actual assignment/capture success/panic transport, including zero/full word capacities. |
| `Lowering/V07/EnumGuardControls.lean` | Inhabited guarded enum, reached-state order, prefix and zero/full-capacity controls with exact pins. |
| `Lowering/V07/UnsignedEnumGuard.lean` | Approved unsigned-width Source enum conversions reuse the existing native guard, with initial-derived success/failure transport. |
| `Lowering/V07/UnsignedEnumGuardControls.lean` | Inhabited narrow-width alias, context and maximum-bound controls across all 32 widths. |
| `Lowering/V07/EnumUnsignedCasts.lean` | Enum-to-approved-unsigned assignment transport; only the result narrows, with full caller-context alignment. |
| `Lowering/V07/EnumUnsignedCastControls.lean` | Inhabited mixed-reference, all-width, capture-extension and incorrect caller-narrowing controls with exact axiom guards. |
| `Lowering/V07/EnumSignedWord.lean` | Actual enum-to-int256 assignment/sign-result transport, deriving full caller-context alignment from initial relations. |
| `Lowering/V07/EnumSignedWordControls.lean` | Inhabited mixed-reference, sign-boundary, capture-extension and stale/truncation controls with exact axiom guards. |
| `Lowering/V07/EnumSignedCasts.lean` | Enum assignment-to-signed-width transport through existing sign and narrowing laws; original caller ordinal preserved. |
| `Lowering/V07/EnumSignedCastControls.lean` | Proved256-member Source enum witness, negative int8 assignments, all-width/mathematical boundaries and exact axiom guards. |
| `Lowering/V07/SignedEnumGuard.lean` | Actual signed assignment, nonnegative panic check, UInt capture and existing enum membership guard, including zero/full capacity. |
| `Lowering/V07/SignedEnumTransport.lean` | Source-to-native signed-input enum conversion success/panic at all approved widths, with initial-derived caller-family transport. |
| `Lowering/V07/SignedEnumControls.lean` | Inhabited mixed-reference, all-width panic/order/sign/capacity controls and exact axiom guards. |
| `Lowering/V07/UdvtAssignment.lean` | Integer-underlying UDVT local assignment and same-tag identity conversion, nominal-refusal boundaries and initial-derived context transport. |
| `Lowering/V07/UdvtAssignmentControls.lean` | Real two-tag UDVT metadata, mixed-reference and all64 integer-type controls with nominal-erasure/stale-read negatives and exact guards. |
| `Lowering/V07/UdvtBoolAssignment.lean` | Boolean-underlying UDVT same-tag assignment and initial-derived full mapped caller transport. |
| `Lowering/V07/UdvtBoolAssignmentControls.lean` | Inhabited mixed-reference Boolean matrix, self/capture extension, stale-read and nominal-refusal controls with exact guards. |
| `Lowering/V07/UdvtAddressAssignment.lean` | Address-underlying UDVT same-tag assignment with canonical UInt capture and initial-derived caller-context transport. |
| `Lowering/V07/UdvtAddressAssignmentControls.lean` | Both payable flags, 160-bit boundaries, mixed references and executed wrong-narrowing/stale/nominal controls with exact guards. |
| `Lowering/V07/UdvtFixedBytesAssignment.lean` | Fixed-byte-underlying UDVT same-tag assignment, canonical UInt capture and exact width-indexed content observation. |
| `Lowering/V07/UdvtFixedBytesAssignmentControls.lean` | Real nominal metadata, all32 byte widths, mixed references and stale/truncation/nominal-refusal controls with exact guards. |
| `Lowering/V07/FixedBytesComparisons.lean` | All six fixed-byte comparison clauses with actual assignment/read pipeline order and initial-derived caller transport. |
| `Lowering/V07/FixedBytesComparisonControls.lean` | All-width/operator ordered observations, live-reference framing and executed uncaptured/reversed-capture negative programs. |
| `Lowering/V07/IntegralRationalConstants.lean` | Arbitrary integral rational meaning, Source conversion/assignment and native capture transport with existing range typing. |
| `Lowering/V07/IntegralRationalControls.lean` | All64 integer types, four denominator representations, ordered observations and executed numerator/floor/cast negatives. |
| `Lowering/V07/P12NegatedCondition.lean` | Published condition-contract negation preserving exact operand code, effects, state and error payloads; double-negation run identity. |
| `Lowering/V07/P12NegatedConditionControls.lean` | Effectful producer composition, source horizons, actual failure bytes and discriminating duplicated-prefix/wrong-write controls. |
| `Lowering/V07/P12AtomicConditions.lean` | Actual Source Boolean literal and local-read producers of the published condition contract |
| `Lowering/V07/P12AtomicConditionControls.lean` | Mixed caller framing, actual negated Source composition and discriminating wrong atomic clauses |
| `Lowering/V07/P12StorageCaptureControls.lean` | Concrete full P12 storage-capture producer with derived initial alias reflection, exact caller frames and empty-alias negative |
| `Lowering/V07/P12MemoryCaptureControls.lean` | Concrete full memory-capture record, derived heap-typed identity and equal-content fresh-allocation counterexample |

| `Lowering/V07/SourceRefusal.lean` | Exact current-Source local-declaration refusal characterization; environment-aware repair predicate only, no Source repair |
| `Lowering/V07/GraphAdmissionAssembly.lean` | Shared H24 assembly from explicit environment obligations; empty-model instances do not establish actual Source adequacy |
| `Lowering/P8/DeclarationGraphConstraints.lean` | Necessary H24 mapping-free constraint for the exact accepted environment-indexed Source program; no producer or universal impossibility claim |
| `Lowering/P8/PlanGraphAdmission.lean` | MODEL-only H24 instance preserving the existing PlanWitness base; no actual Source or library adequacy |
| `Lowering/P8/SourceAstTypes.lean` | Incomplete compiler-AST leaf type/parameter conversion into existing Source syntax; no admission or program claim |
| `Lowering/P8/SourceAstParameters.lean` | Ordered parameter/result containers in Source syntax, with exact list/error preservation; no function or admission claim |
| `Lowering/P8/SourceAstExpressions.lean` | Partial compiler-expression reader preserving intrinsic receivers, tuples and literal bytes; no resolution or admission claim |
| `Lowering/P8/SourceAstCompoundTypes.lean` | Recursive compiler type syntax using existing leaves/expressions; no resolution or admission claim |
| `Lowering/P8/SourceAstStatements.lean` | Partial compiler block/statement/catch reader retaining original bodies; no resolution, origin or admission claim |
