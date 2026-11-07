
### P1 paired allocating scalar transport

| Module | Purpose |
|---|---|
| `Backend/InternalFlow/RuntimeFrameV3ScalarDescentInterfaceV1.lean` | Frozen typed public-guard and allocating three-cell prefix obligations, parameterized by an existing compiler certificate. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarAllocatingDescent.lean` | Actual scalar allocating descent horizons with reached representation, exact ownership growth, three-cell parent history and complete exact new-object inventory. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarDescentControls.lean` | Populated zero/one/two descent horizons, old-array observations, capture-order negatives and the actual terminal guard. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarPairedExecution.lean` | Actual allocating descent history feeds the same-state scalar return loop. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarPairedTransport.lean` | All-count descent and return execution against the frozen producer, with derived history and allocator transport. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarPairedTransportControls.lean` | Populated actual producer, scalar result and restored pointer controls for paired transport. |
| `Backend/InternalFlow/RuntimeFrameV3NativeScalarAgreement.lean` | All-count actual native recursive source and paired target scalar observation agreement, with heap identity separate. |
| `Backend/InternalFlow/RuntimeFrameV3NativeScalarAgreementControls.lean` | Populated source/target scalar result and distinct native exhaustion versus target success controls. |
| `Backend/InternalFlow/RuntimeFrameV3NativeAllocationCoherence.lean` | Complete native allocating-recursive output coherence across all sufficient quotation indices; target heap identity remains separate. |
| `Backend/InternalFlow/RuntimeFrameV3NativeAllocationCoherenceControls.lean` | Exact populated two-allocation output at two sufficient indices and genuine insufficient-index exhaustion. |
| `Backend/InternalFlow/RuntimeFrameV3FreshAllocationContents.lean` | Exact fresh private array source contents and physical words after arbitrary allocating descent tails. |
| `Backend/InternalFlow/RuntimeFrameV3FreshAllocationContentsControls.lean` | Populated one/two-turn fresh object observations and header/payload ordering negatives. |
| `Backend/InternalFlow/RuntimeFrameV3AllocationInventory.lean` | Typed complete new-object inventory, every-reference coverage, distinct addresses and same-state physical observations. |
| `Backend/InternalFlow/RuntimeFrameV3AllocationInventoryControls.lean` | Populated zero/one/two actual descent inventories and new-object address distinctness. |
| `Backend/InternalFlow/RuntimeFrameV3TypedHeapExtensionality.lean` | Intrinsic object/heap extensionality, derived output typings and uniqueness from exact old/new contents. |
| `Backend/InternalFlow/RuntimeFrameV3NativeHeapProfile.lean` | Actual native recursive allocation supplies exact new-object contents and State-field preservation for every sufficient quotation index. |
| `Backend/InternalFlow/RuntimeFrameV3NativeDescentHeap.lean` | Actual native output and reached target descent have identical complete dependent heaps; local return transport remains separate. |
| `Backend/InternalFlow/RuntimeFrameV3TypedHeapExtensionalityControls.lean` | Two actual allocations preserve old objects yet differ in fresh contents; the altered heap fails the exact profile. |
| `Backend/InternalFlow/RuntimeFrameV3NativeDescentHeapControls.lean` | Populated source/target heap identity with the native-result versus descent-slot mismatch retained. |
| `Backend/InternalFlow/RuntimeFrameV3StateShell.lean` | Equality of existing non-memory State fields for allocation-only internal execution; no external/world-call adequacy. |
| `Backend/InternalFlow/RuntimeFrameV3NativeReturnRepresentation.lean` | Actual native recursive output represented after actual target parent returns, with derived heaps, locals and remaining State fields. |
| `Backend/InternalFlow/RuntimeFrameV3NativeReturnRepresentationControls.lean` | Populated actual-output representation, complete ordered 20-word observation vector and cursor/alias/halt negatives. |
| `Backend/InternalFlow/RuntimeFrameV3AllocationInventoryControls.lean` | Populated zero/one/two actual descent inventories and new-object alias negatives. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingCallCoherence.lean` | Frozen recursive-return source-coherence duty for the allocating family, all compatible callers/arguments/return binders and quotation indices. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingCallCoherenceControls.lean` | Actual outer calls at indices two/four with private allocation and preserved caller scalar; zero-index exhaustion distinguished from bare revert. |
| `Backend/InternalFlow/RuntimeFrameV3OuterScalarRestore.lean` | Same-reference outer scalar restore preserving the live result and reached heap. |
| `Backend/InternalFlow/RuntimeFrameV3OuterAllocatingCall.lean` | Executed allocating scalar call with actual exported caller representation and ordered result/control observations. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingOuterFamily.lean` | Fixed-image actual outer return over all capacity-admitted counts and sufficient source indices, with exported caller representation, total allocator transport, base extension and older-word preservation below an arbitrary runtime start. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingOuterFamilyControls.lean` | Inhabited zero/one-allocation families, complete ordered observations, changed-caller-result transport, starts9/11 and protected-word/scalar/halt negatives. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingOuterPlan.lean` | State-indexed argument demand and positive-allocation frozen Returned transport from existing Entry capacity; zero-cost transport is supplied by AllocatingOuterZero; universal claims are supplied by AllocatingOuterClaims. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingOuterPlanControls.lean` | Inhabited complete Entry and Returned across sufficient source indices, exact cursor/reference/counter/result/pointer vector and revert rejection. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingOuterZero.lean` | Owner-free zero-cost execution and frozen Returned; combined nonwrapped-count transport under original depth bounds. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingOuterZeroControls.lean` | Represented input with no allocator witness, actual zero-cost Entry/Returned and exact observations with cursor/halt negatives. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingOuterClaims.lean` | Universal frozen ReturnClaim/BareRevertClaim for the existing allocating family and plan; checked zero-counter argument failure and insufficient-depth exhaustion remain distinct. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingOuterClaimsControls.lean` | Inhabited universal success/revert consumers and complete failure entries at every index, rejecting panic/exhaustion/wrong-success outcomes. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingSourceCertificate.lean` | Closed syntax certificates for canonical/scoped allocating recursion; full source-run equality and frozen claim transport are derived, with no arbitrary-input parser or public-selector claim. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingSourceCertificateControls.lean` | Inhabited scoped recursion success/failure at all supplied indices and uncertifiability of malformed base/quotation inputs. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingSourceViews.lean` | Context-generalized intrinsic sequence/statement views and executable exact recBase certification; recursive-head recognition remains open. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingSourceViewsControls.lean` | Actual base acceptance and nil/revert/extra-statement refusal receipts, with extracted-certificate revert/exhaustion consumers. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingHeadViews.lean` | Generalized typed conditional/callRec/block/declaration/assignment views retaining actual children and constructor equations. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingDeclarationCheck.lean` | Executable exact scoped private bool-array allocation recognition from actual typed views; derives source syntax equality. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingHeadViewsControls.lean` | Actual head/allocation receipts, malformed-declaration refusals and the existing public allocation compiler-leaf link. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingTurnViews.lean` | Executable allocating conditional-root recognition retaining the actual guard, continuation and alternative with an exact syntax reconstruction; child/guard/whole-selector checks remain open. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingTurnViewsControls.lean` | Actual recursive-turn acceptance, preserved arbitrary continuation/alternative, and malformed root/allocation/extended-branch refusals. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingValueViews.lean` | Generalized typed simple/local/binary value views retaining actual primitive indices, operands and constructor equations. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingScalarLeaves.lean` | Exact allocating-family guard/zero/increment syntax recognition from actual value/assignment views; no indexed statement/argument match or semantic premise. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingGuardedTurn.lean` | Actual allocating root recognition checks original guard and zero arm, retains original continuation, and checks exact increment suffix independently. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingScalarLeavesControls.lean` | Populated guard/zero/increment/root/suffix receipts and actual wrong-operator/slot/literal/destination/alternative/extra-tail refusals. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingCallViews.lean` | Generalized intrinsic argument/memory-variable/value-return readers retain actual indices, payloads and constructor equations. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingCallLeaves.lean` | Exact original allocating argument labels/order/decrement/alias slot and result destination recognition through typed views. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingRecursiveCheck.lean` | Actual allocating recursive-head recognition retains child thunks, verifies original quotation indices, constructs existing source certificates and derives full source-run agreement from checker success. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingRecursiveCheckControls.lean` | Canonical acceptance at every index for fixed reference `A`, actual child retention, and wrong arguments/returns/function-name/index/child/base/signature refusals proved by `rfl`/`simp`. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingScopeView.lean` | Generalized exact unused-default-local decorator recognition, retaining the actual closed inner program and constructor equations. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingScopedCheck.lean` | Existing scoped allocating-family certification follows actual inner programs and children at original quotation indices; checker success derives full source-run agreement. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingScopedCheckControls.lean` | All-index scoped-family acceptance at fixed reference `A`, arbitrary decorator type/name, and actual initialization/order/context/root/index/child/profile refusals. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingScopedEndpoint.lean` | Populated checked scoped-source returns for original fixed C/A and positive/zero-cost callers, sharing all Returned invariants and existing ordered target observations; zero case proves no allocator witness. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingScopedEndpointControls.lean` | Concrete scoped-return instances, restored result/counter/older-frame observations, frame refusal and zero-cost return without allocator ownership. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingScopedTransport.lean` | Actual scoped-checker success yields frozen success/bare-revert claims for every original Entry, caller, frame and runtime cursor at fixed C/A; no approved-profile or selector claim. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingScopedTransportControls.lean` | Checked scoped-call argument-underflow transport preserves complete ordered bare-revert/non-success/panic/exhaustion distinctions without failed-State/world claims. |
