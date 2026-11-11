# Read-only calls and world-call consumers (G22, G42)

| Module | Purpose |
|---|---|
| `Backend/Passes/SourceTypedCall.lean` | Typed factorisation of the resolved source external call into capture (`CapturedAt`), encoding/code check and resume ([G22](../feature-work/g22-readonly-calls.md)). |
| `Backend/Passes/SourceCallBoundary.lean` | Source call-boundary equations: horizon/depth/static-value refusal, static journal refusal, declared-return revert/short failures ([G22](../feature-work/g22-readonly-calls.md)). |
| `Backend/Passes/SourceCallFrame.lean` | Child `dispatch` success/revert/halt transport through `enterInstance`; live mark ([G22](../feature-work/g22-readonly-calls.md)). |
| `Backend/Passes/SourceCallControls.lean` | Unknown nonself, reentry, rollback, return-shape and argument-checkpoint source call controls ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/CapturePhases.lean`, `Lowering/Readonly/CaptureFailures.lean` | Capture run from per-phase equations; five capture-failure equations (no callee started) ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/CallerResume.lean`, `Lowering/Readonly/ReceiverCapture.lean` | Raw `callAddr` run to caller `extReturn` transport; injective address-to-`uint` receiver literal ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/FullCaptureControls.lean`, `Lowering/Readonly/CaptureFailureControls.lean`, `Lowering/Readonly/ReceiverControls.lean`, `Lowering/Readonly/ResumeControls.lean` | Capture, failure, receiver and resume controls on typed source fixtures ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/EnvironmentSteps.lean`, `Lowering/Readonly/EnvironmentCredit.lean` | `envLoop` step equations: answer, refusal, child outcome/halt, missing instance and credit cases ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/EnvironmentHistory.lean` | `CallbackHistories` P1 input; horizon induction `loop` giving `StaticJournal.History` and static storage equality ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/EnvironmentControls.lean`, `Lowering/Readonly/EnvironmentCreditControls.lean`, `Lowering/Readonly/EnvironmentHistoryControls.lean` | Read-only callback, static credit (balance changes, storage fixed), overflow and bounded-history controls ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/StaticJournal.lean` | Guarded journal `History` (balance, ordinary write, child, rollback) and its static storage-preservation induction ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/JournalLeaves.lean` | `History` leaves for debit/operation/cell writes and composition through bind and subframes ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/InvocationFrame.lean` | `Invocation`, `RawAt`, `RuntimeFrames`, `StorageRepresentation`; caller storage frame and typed transport ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/Controls.lean` | Static-world frame controls: balance change with storage kept, reentry, spoofed declaration and wrong-raw refusals ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/PrimitiveValues.lean`, `Lowering/Readonly/PrimitiveLocals.lean` | Intrinsic/source uint-int-bool value bijections and typed local-context correspondence ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/PrimitiveFields.lean` | Fieldwise primitive storage relation `Rel`, ownership-checked `CallLayout`, exit-relation construction ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/PrimitiveReads.lean`, `Lowering/Readonly/ReadStatement.lean` | Source/intrinsic primitive root-read simulation and lowered read statement with arbitrary tail ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/CapturedArguments.lean`, `Lowering/Readonly/PrimitiveInitialization.lean`, `Lowering/Readonly/PrimitiveCallable.lean` | Intrinsic `Args` from captured values; primitive return-slot initialization; source callable composition ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/Readonly/LoweringControls.lean`, `Lowering/Readonly/RootControls.lean`, `Lowering/Readonly/ArgumentControls.lean`, `Lowering/Readonly/CallableControls.lean` | Primitive lowering controls: field relation, non-head root, argument non-reevaluation, callable success/revert ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/V08/SourceCallPhase.lean` | Same-invocation raw `callAddr` phase before caller decoding; `extCall` phase equation ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/V08/SourceCallPhaseControls.lean`, `Lowering/V08/SourceExternalPhaseControls.lean` | Answer-driven unknown-call raw phase and typed external expression controls (signed word, short, revert, no code) ([G22](../feature-work/g22-readonly-calls.md)). |
| `Lowering/V08/SourceClockTransactions.lean` | Actual Source.runTx and typed-world request-clock execution with raw/end/reset observations; handwritten RBody/entry, not canonical compilation. |
| `Backend/WorldCalls/Premises.lean` | Conditional compiler world-call interfaces: `Identity`, `Code`, `ReturnedFrame`, `Premises`, `FetchedCall`, `FetchedPremises` ([G42](../feature-work/g42-world-call-consumers.md)). |
| `Backend/WorldCalls/Callbacks.lean`, `Backend/WorldCalls/ExternalCalls.lean`, `Backend/WorldCalls/SelfCalls.lean`, `Backend/WorldCalls/P1Consumers.lean` | Conditional callback, external, self-call and frozen P1 V3 consumers projecting producer premises ([G42](../feature-work/g42-world-call-consumers.md)). |
| `Backend/WorldCalls/SourceBridge.lean`, `Backend/WorldCalls/UnknownSourceCall.lean` | P3 bridge from `RawAt` to the source raw phase; zero-value unknown-call transport and joint `RawAt`/`RuntimeFrames` ([G42](../feature-work/g42-world-call-consumers.md)). |
| `Backend/WorldCalls/PaymentControl.lean`, `Backend/WorldCalls/ExternalControls.lean`, `Backend/WorldCalls/SelfControls.lean`, `Backend/WorldCalls/SourceBridgeControls.lean`, `Backend/WorldCalls/UnknownSourceControls.lean` | Restricted paired payment-CALL fixture and source controls for the world-call consumers ([G42](../feature-work/g42-world-call-consumers.md)). |
| `Lowering/Readonly/HistoryRollback.lean` | Algebraic history ancestry and actual live Source checkpoint rewind. |
| `Lowering/Readonly/CallbackFrame.lean` | Child success/revert/halt history step from smaller actual Source dispatch; zero bound. |
| `Lowering/Readonly/HistoryRollbackControls.lean` | Actual ordinary/static child dispatch, live/stale checkpoint and both-pipeline controls. |
| `Lowering/Readonly/SourceHistory.lean`, `SourceHistoryBase.lean` | Generated typed 17-way Source induction predicate and exhausted base only; positive bound remains open. |
| `Backend/WorldCalls/UnknownRevertControls.lean` | Actual computed unknown-call credit/revert frame at a supplied prior-effect state; no general target correspondence. |
| `Backend/WorldCalls/SourceCallHistory.lean`, `Backend/WorldCalls/SourceCallHistoryControls.lean` | Actual known-call and unknown zero-value histories/static storage projection;27 nonself/reentry/rollback/code-identity controls, no native adequacy. |
| `Backend/WorldCalls/ClosedSourceControls.lean` | 18 all-value/reentry/rollback/refusal controls and inhabited closed Source clients. |
| `Backend/WorldCalls/ClosedSourceFrame.lean` | Same-invocation post-capture Source raw history/frame/storage facts; no target/Core adequacy. |
| `Backend/WorldCalls/ClosedSourceConsumers.lean` | Compiler consumer adapter deriving Source P2 from exact raw-phase execution, with target/correspondence and representation premises retained. |
| `Backend/WorldCalls/ClosedConsumerControls.lean` | Inhabited restricted target client, raw-byte mismatch refusal, actual Source reentry and generic typed projection. |
| `Backend/WorldCalls/SourceExpressionConsumer.lean` | Exact resolved external-expression capture/resume link and closed call/declared-decoder static storage law at post-capture state. |
| `Backend/WorldCalls/SourceExpressionControls.lean` |13 actual Source expression assertions for argument effects, old-value calldata, caller decode failure and permitted read-only reentry. |
| `Backend/WorldCalls/SourceExpressionIssuer.lean` | Actual successful resolved-expression run produces typed capture/invocation binding and post-argument static caller storage law. |
| `Backend/WorldCalls/SourceIssuerControls.lean` | Inhabited local issuance, forged view-registration rejection and missing-code capture refusal. |
| `Backend/WorldCalls/SourceExpressionFailure.lean` | Exact capture-error versus resumed-error classification and static storage from the successful post-argument checkpoint only. |
| `Backend/WorldCalls/SourceFailureControls.lean` | Eight Source assertions retaining dirty argument failure, no call event, caller-decoder failure and ordered callee revert data. |
| `Backend/WorldCalls/SourceSelfDispatch.lean` | Actual guarded Source external-self funding/entry/dispatch transport for success, revert and non-revert halt. |
| `Backend/WorldCalls/SourceSelfDispatchControls.lean` | Nine actual self-dispatch API/outcome/guard assertions; no target CALL or callInternal substitution. |
| `Lowering/Readonly/EffectRules.lean` | Source journal-effect composition: live bind, subframes, caught halt and inherited mode; no arbitrary state overwrite. |
| `Lowering/Readonly/MachineEffects.lean`, `Lowering/Readonly/MachineEffectControls.lean` | Actual allocation/replacement journal effects, type-refusal/caught-halt memory controls and ordinary-write negative. |
| `Lowering/Readonly/ReadEffects.lean` | Actual read/reference/guarded-write journal producers, retaining refusal branches. |
| `Lowering/Readonly/DeleteEffects.lean`, `Lowering/Readonly/DeleteControls.lean` | Closed all-horizon mutual storage deletion histories; populated ordinary/static/exhaustion/read controls. |
| `Lowering/Readonly/ZeroEffects.lean`, `Lowering/Readonly/ZeroControls.lean` | Closed all-horizon/mode mutual Source zero-initialization histories and actual allocation/exhaustion/default-refusal controls. |
| `Lowering/Readonly/LoadEffects.lean`, `Lowering/Readonly/StoreEffects.lean` | Closed Source loading/copying journal histories; actual static guards and all failure/no-op/exhaustion branches. |
| `Lowering/Readonly/CopyControls.lean` | Typed populated source/destination copy controls: post-seeding checkpoint, allocating load, shrink/tail clearing, static refusal, no-op and ordinary-change negative. |
| `Lowering/Readonly/EvalEffectsBase.lean`, `Lowering/Readonly/LocationEffects.lean` | Actual evaluator/location histories: permitted local/memory mutation, guarded storage writes, read/type/bounds/calldata refusals. |
| `Lowering/Readonly/LocationControls.lean` | Populated static local/memory mutation and storage/refusal controls with inhabited effect clients. |
| `Lowering/Readonly/LocalInitializationEffects.lean`, `Lowering/Readonly/LocalInitializationControls.lean` | Closed value-list/return-slot initialization effects with separate contexts, actual allocation/refusal/exhaustion/empty-work controls. |
| `Lowering/Readonly/CallSupportEffects.lean` | Actual instance/event/mark/outcome journal effects; no unconditional rollback or static LOG permission. |
| `Lowering/Readonly/CollectionEffects.lean` | Map/mapM and lifted value/index effects, preserving partial-failure state. |
| `Lowering/Readonly/ReferenceEffects.lean` | Existing byte/reference/implicit/explicit conversion journal effects, without ABI correctness or admission claims. |
| `Lowering/Readonly/TupleCopyEffects.lean` | Typed tuple pushing with separate contexts and storage copying under the real static flag. |
| `Lowering/Readonly/HelperControls.lean` | Populated lookup/events/conversion/tuple allocation, refusal, timeout and partial-failure controls. |
| `Lowering/Readonly/SourceSequenceEffects.lean`, `Lowering/Readonly/SourceSequenceControls.lean` | Strictly smaller-bound operand/argument sequencing steps and inhabited ordering/local-mutation/empty/exhaustion controls. |
| `Lowering/Readonly/KeyStepEffects.lean` | Journal effects of actual mapping-key conversion, including refused keys and bounded reference reads. |
| `Lowering/Readonly/SourceLvalueCallEffects.lean`, `Lowering/Readonly/SourceLvalueCallControls.lean` | Lvalue/payment successor histories with inherited static mode; actual key/location and caller-halt/child-revert controls. |
| `Lowering/Readonly/SourcePayloadEffects.lean`, `Lowering/Readonly/SourcePayloadDecodeEffects.lean`, `Lowering/Readonly/SourcePayloadControls.lean` | Journal-only effects of existing payload algorithms and populated allocation/refusal/return-phase controls; no ABI correctness or admission claim. |
| `Lowering/Readonly/SourceAggregateReadEffects.lean` | Actual digest-shape, typed-field and bounded-path read histories, retaining refusals without getter/ABI correctness claims. |
| `Lowering/Readonly/SourceBuiltinEffects.lean` | Strictly smaller-bound actual builtin sequencing/history step, including refusals and opaque precompile handling. |
| `Lowering/Readonly/SourceExpressionParts/*.lean`, `Lowering/Readonly/SourceExpressionEffects.lean` | Generated exact constructor cuts and exhaustive actual expression successor history; full evaluator induction remains separate. |
| `Lowering/Readonly/SourceReadBuiltinControls.lean` | Typed seeded path/construction/builtin observations, an actual At0 expression client and named gas-refusal negative. |
| `Lowering/Readonly/SourceBodyEffects.lean`, `Lowering/Readonly/SourceBodyControls.lean` | Actual internal-body, typed item and modifier successor journal effects; inhabited static modifier observations. Full history induction remains open. |
| `Lowering/Readonly/SourceLoopEffects.lean`, `Lowering/Readonly/SourceLoopControls.lean` | Actual loop successor journal effects and15 populated-state exit/refusal/exhaustion controls; smaller-bound premise retained. |
| `Lowering/Readonly/SourceDispatchEffects.lean`, `Lowering/Readonly/SourceDispatchControls.lean` | Exact selector leaves and exhaustive dispatch successor journal effect;13 finite observations and inhabited client, not full call/native adequacy. |
| `Lowering/Readonly/SourceStatementParts/*.lean`, `Lowering/Readonly/SourceStatementEffects.lean` | Generated21 intrinsically typed actual statement cuts and exhaustive successor journal effect; smaller-bound At retained. |
| `Lowering/Readonly/SourceTryEffects.lean` | Exact typed try computation factoring, kernel equality to execS and real payload/finish effects, without native/frame oracle. |
| `Lowering/Readonly/SourceStatementControls.lean` |20 actual populated-state statement/try controls and inhabited successful At0 client; no native adequacy claim. |
| `Lowering/Readonly/SourceEnvironmentEffects.lean`, `Lowering/Readonly/SourceEnvironmentControls.lean` | Actual environment successor history from smaller-bound child/loop execution;23 reentry/refusal/credit/rollback/raw-data/exhaustion controls. |
| `Lowering/Readonly/SourceCallPrefix.lean` | Exact known-instance Source prefix and guarded callAddr run equality, with balance-only and live-child histories. |
| `Lowering/Readonly/SourceCallUnknown.lean` | Exact all-value unknown Source call branch, debit refusal and live rollback histories. |
| `Lowering/Readonly/SourceCallAddressEffects.lean` | Complete actual callAddr successor history, known/unknown instances and original guards. |
| `Lowering/Readonly/SourceAllHistories.lean` | Closed seventeen-component bounded Source induction, actual callbacks and static storage law. |
| `Semantics/CallResume.lean` | Bounded readonly-external checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/Readonly/SourceKnownHistory.lean`, `SourceKnownExpressionEffects.lean`, `SourceKnownTryEffects.lean`, `SourceKnownStatementEffects.lean` | One journal-history interface for available and unavailable delegated calldata, exact contract try factoring and exhaustive typed expression/statement proofs. |
| `Lowering/Readonly/LibraryFrameEffects.lean`, `SourceKnownLibraryEffects.lean`, `SourceKnownAllHistories.lean` | Actual live-mark library rollback and independent 18-component journal induction; projects to the unchanged ordinary `At` interface. |
