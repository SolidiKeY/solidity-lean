| `Source/CalldataLayout.lean` | ABI head dimensions for the owned calldata aggregate subset (`cdStaticWords`, `cdHeadBytes`, `STy.cdStride`), taken from v14 781938cf. |
| `Source/CalldataAggregates.lean` | S02/G18.04 nested calldata reads, string and static-reference slices, and typed read-only locations, taken from v14 781938cf. |
| `Source/CalldataStaticCopyControls.lean` | G18.05 controls of `cdToMem` copying statically encoded elements (`uint256[2][]`, `uint256[2]`) at the head stride, with validation and the `stuck` dynamic-element case; the nested arm is called directly; its typed-source reachability is in `CalldataNestedCopyControls`. |
| `Source/CalldataNestedCopyControls.lean` | G18.05 nested copy from typed source: `STy.implicit` compares array elements at the target's location, so `uint256[2][] calldata` converts to `uint256[2][] memory`; refusals, the typed declaration, `convRV_cd_static_ok` (the conversion runs `cdToMem` and keeps `MemOK`) and an elaborated, deployed control. |
| `Source/FailureMachine.lean` | Explicit-plan Source frame operations (H16 execution leaf) These operations run in the actual Source EM and use its existing event emitter. |
| `Source/FailureMachineControls.lean` | Independent expected actual-EM controls. |
| `Source/FailurePrimitives.lean` | Shared actual-EM failure primitives below Eval. |
| `Source/Monetary.lean` | Balances are exact naturals, including values outside the EVM word range. |
| `Source/FailureEventControls.lean` | Independently fixed complete states for actual Source.emitEvent, with nonempty caller journal/event prefix and byte-memory alias. |
| `Source/FailureEventLaws.lean` | Full-state law for the actual Source event emitter. |
| `Source/FailureRuntimeControls.lean` | Actual explicit-plan Source execution through existing registered code. |

| `Source/MonetaryLaws.lean` | H19 primitive credit-produced and debit-preserved range facts; constructive out-of-range successful debit control. No Account/ledger migration or execution reachability claim. |

| `Source/FailureRequest.lean` | Actual EM request-budget scope: dropped/scheduled requests, exact Nat balance argument, zero-cut and active-owner refusal, halt/local retention and sequential ordinal controls. Session funding, rollback and consistency not claimed. |

| `Source/Funds.lean` | Actual request-boundary funds validation, invalid whole-state identity, exact valid execution, stable completed horizons and both session-driver drop laws. |
| `Source/FundsControls.lean` | Actual Source payable requests in both pipelines: stress-state drop, following valid request, timeout/revert distinction, prior debit/credit controls. |

| `Source/FailureConstructorControls.lean` | H16 actual initializer/body CALL event cuts, rollback and seeded parent/request owner propagation; default-None horizon proofs retained. Root/session indexing and full adequacy remain open. |

| `Source/FailureTransactionControls.lean` | H16 actual root dispatch plan, own-frame reverts versus outer-stop/timeout propagation, transient/journal finalization and complete state controls; request fate/funding/P8 adequacy remain open. |

| `Source/FailureFrameHorizon.lean` | H16 actual frame/check/event Grow and frame Approx transport; explicit real body relations and rethrow-timeout continuation, not full planned evaluator consistency. |
| `Source/FailureFrameHorizonControls.lean` | Inhabited event-prefix/heap/caller full-state frames, timeout/outer-cut controls and counterexample to blanket attempt approximation. |

| `Source/FailureRequestAdmission.lean` | Exact post-fee Nat value admission around unchanged requestScope; current effective-fate normalization, other-request/frame preservation, arbitrary-body drop/admitted laws, complete state/byte/cut/timeout/ordinal controls; no balance installation/session/P8 claim. |

| `Source/FailureNoCuts.lean` | Structural CutFree over the actual typed cursor; no-stop, NoFail entry, cleanup/tick preservation and full-state check identity. No full evaluator coherence/NoFail claim. |
| `Source/FailureNoCutsEffects.lean` | Actual enabled emitter: complete event append, exact live-budget tick, retained remaining locals/state under CutFree. |
| `Source/FailureNoCutsControls.lean` | Constructed nested request/frame no-cut budgets, full-state events/heap bytes and counterexample to NoFail-plan-alone reasoning on arbitrary cursors. |

| `Source/MonetaryWorld.lean` | Explicit current-account and saved-journal monetary range, actual natural/Word transfer preservation and saved-wide rollback counterexample; no full reachability claim. |

| `Source/MonetaryAuthority.lean` | H25 exact-money authority representation, actual journal/request-scope adapters, lossless Word-request funding saturation and checked balance conversion; G01 settlement/session review pending. |

| `Source/MonetaryAuthoritySource.lean` | H25 authority journal write/undo and exact post-fee request-scope adapters; depends on owner-held H16/H19 core changes, not G01 settlement/session wiring. |

| `Source/MonetaryExecution.lean` | Exact actual credit/debit execution, explicit current-and-saved range preservation and wide-money refusal/success controls; not whole-program reachability. |

| `Source/MonetaryRollback.lean` | Actual mark/captured-credit/rollback full-state execution and explicit saved-account range transport; no generic heap rollback or transaction-finalization claim. |
| `Source/MonetaryRollbackControls.lean` | Inhabited heap/log/journal prefix, wrong-mark, capture-only and zero-credit controls with actual full-byte continuation readback. |

| `Source/MonetaryStorage.lean` | Actual persistent/transient mutable storage and typed-write preservation of explicit current-and-saved balance bounds, with static refusal unchanged. |
| `Source/MonetaryStorageControls.lean` | Inhabited typed direct-storage controls: full caller state/prefixes, balance17, changed cells, static/type refusals and actual journal undo; not dispatched execution. |

| `Source/FailureRequestHorizon.lean` | Actual requestScope event growth and fixed-plan horizon approximation with per-balance body premises; timeout cleanup rethrows without events. |
| `Source/FailureRequestHorizonControls.lean` | Inhabited request horizon/full-state/wide-input/byte controls, cut/drop distinctions, caught-cut refusal and changed-plan counterexample. |

| `Source/FailureEvaluatorGrow.lean` | Closed fixed-plan event-growth induction through the shared eighteen-operation HorizonAt schema, covering both calldata modes; the existing seventeen-field GrowAt API remains unchanged. |
| `Source/FailureEvaluatorGrowControls.lean` | Actual entered-frame induction use, all-horizon prefix transport and changed-plan/event-erasure counterexamples; transitive standard axiom pins. |
| `Source/FailureTransactionGrowth.lean` | Actual runTxWithPlan event growth from the closed induction and real root operations; no session/Approx/P8 claim. |

| `Source/FailureScopeStability.lean` | Actual frame/request Below transport with genuine timeout rethrow; no blanket attempt transport. |
| `Source/FailureEvaluatorStability.lean` | Closed fixed-plan equality-or-timeout induction through the shared eighteen-operation HorizonAt schema, covering both calldata modes and projecting to the unchanged legacy BelowAt API. |
| `Source/FailureTransactionStability.lean` | Actual planned root Below and complete result/state stability after non-timeout completion at all larger fixed-plan horizons. |
| `Source/FailureStabilityControls.lean` | Full frozen Source revert/panic/stuck/request-stop transport and timeout/attempt counterexamples; standard transitive axiom pins. |

| `Source/FailureEvaluatorApprox.lean` | Closed fixed-plan event-prefix approximation through the shared eighteen-operation HorizonAt schema, with full completed-state equality and the unchanged legacy ApproxAt API. |
| `Source/FailureTransactionApprox.lean` | Actual planned root approximation and event-prefix inclusion at every larger horizon, including timeouts; no session/deployment/P8 assertion. |
| `Source/FailureApproxControls.lean` | Actual timeout-prefix/completed-cut controls and changed-plan/captured-timeout counterexamples; exact standard axiom pins. |

| `Source/FailureDeploymentHorizon.lean` | Fixed-plan actual initializer/base-argument/modifier-body growth/approximation, deployment event-prefix monotonicity and exact full-result stability after non-timeout completion; no session fate or P8 claim. |
| `Source/FailureDeploymentReceipt.lean` | Actual enabled-plan deployRun receipt growth, approximation and arbitrary-horizon prefix; terminal receipt remains outside body-event budget. |
| `Source/FailureDeploymentControls.lean` | Inhabited registered initializer/nonempty-constructor-body/ancestor-stop transport, changed-plan counterexample and22 exact standard axiom pins. |

| `Source/FailureRequestAdmissionLaws.lean` | Existing requestValueScope nonconstant-plan arbitrary-cursor admission equations, unchanged funded-plan identity and exact dependent frame/counter retention on rejection. |
| `Source/FailureRequestAdmissionHorizon.lean` | Existing exact-Nat admission API Grow/Below/Approx transport with explicit actual body relations; no second runtime admission operation. |
| `Source/FailureRequestAdmissionHorizonControls.lean` | Nonconstant fate at ordinal37/frame counter11, exact wide balance and typed caller alias readback, timeout/cut/wrong-index/full-byte controls and17 exact axiom pins. |
