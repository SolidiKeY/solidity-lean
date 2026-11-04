# V08 independent adapters

| Module | Purpose |
|---|---|
| `Lowering/V08/Callable.lean` | Typed result observation extension; paid frame and exact halt preserved. |
| `Lowering/V08/AbiObservations.lean` | Independent source/intrinsic word, panic and reason byte agreement. |
| `Lowering/V08/Transactions.lean` | Snapshot, atomic status, observation and repeated reset laws. |
| `Lowering/V08/LibraryCreation.lean` | Linked caller-context and creation-continuation observations. |
| `Lowering/V08/LiteralFailureLowering.lean`, `Lowering/V08/LiteralFailureControls.lean` | G21: `literalInput` compiler for closed assert/require/revert/panic literals; source and terminal-byte agreement ([G21](../feature-work/g21-failure-lowering.md)). |
| `Lowering/V08/BoolErrorLowering.lean`, `Lowering/V08/BoolErrorControls.lean` | G21: closed boolean custom errors; ABI payload, source run and constant-payload emitter. |
| `Lowering/V08/SliceFailureLowering.lean`, `Lowering/V08/SliceFailureControls.lean` | G21: Source calldata-slice equations; the revert paired with an empty terminal (not a lowered bounds check). |
| `Lowering/V08/WorldImage.lean`, `Lowering/V08/WorldReset.lean`, `Lowering/V08/WorldResetControls.lean` | Account/session image and reset transport relative to `ResetInputs`; one-slot controls ([V08](../feature-work/roadmap-v08-world-lowering.md)). |
| `Lowering/V08/WorldCatalogue.lean`, `Lowering/V08/WorldCatalogueTransport.lean`, `Lowering/V08/WorldImageAccess.lean` (+`Controls`) | Initial world assembly from installed code; `assembled_image`; typed store lookup. |
| `Lowering/V08/LibraryFrameTransport.lean`, `Lowering/V08/LibraryIntegerTransport.lean`, `Lowering/V08/WorldContextComposition.lean` | Library call frames for fixed observer entries; repeated/failing transactions. |
| `Lowering/V08/ConstructorScalarTransport.lean`, `Lowering/V08/ConstructorContinuations.lean` | Scalar `Cell` constructor fixture; `tryCreate` continuations. |
| `Lowering/V08/CreationPremises.lean`, `Lowering/V08/LibraryPremises.lean` | Producer-premise consumers (vacuous until P8-SPEC-LAW1). |
| `Lowering/V08/{Integer,PureArgument,Tuple}Callable.lean`, `Lowering/V08/{Local,Scalar}CallableTransport.lean`, `Lowering/V08/Source{Session,SessionCredit,Deployment,DeploymentSession,PayableDeployment,FailedDeployment,Transaction,ConstructorArguments}Controls.lean` | Callable transports and source session/deployment controls. |
| `Lowering/V08/Controls.lean` | Funded, failure-byte, rollback, reset and caught constructor controls. |
| `Lowering/V08/AbiControls.lean` | Exact catch positives and malformed/wrong-code negatives. |
| `Lowering/V08/LibraryControls.lean` | Delegated owner isolation and nonempty constructor installation. |
| `Lowering/V08/Audit.lean` | Headline axiom output pinned by lane-specific controls. |
| `Lowering/V08/CallbackControls.lean` | Paid invariant/havoc callback, actual settlement and atomic rollback witnesses; no source reentrancy claim. |
| `Lowering/V08/CallableMetadata.lean` | Source resolved argument/conversion metadata and checked target frame labels; no source evaluator |
| `Lowering/V08/MetadataControls.lean` | Nonempty source function/error metadata, typed target binding and wrong-order/signature controls |
| `Lowering/V08/EnvironmentProjection.lean` | Total source/intrinsic word/address, request/environment and account/session-ledger observation adapters; no source execution certificate |
| `Lowering/V08/ProjectionControls.lean` | Populated independent instance journals and actual target nested paid frames, reset/payload negatives and external-ledger selection controls |
| `Lowering/V08/SelectorObservations.lean` | Independent canonical signature/custom-selector bytes, prefix splitting and ordered ABI word observation extension |
| `Lowering/V08/SelectorControls.lean` | Kernel UTF-8/selector/argument-order controls; no collision axiom or native trust shortcut |
| `Lowering/V08/EmitControls.lean` | Actual erased-emit typed effects/read/failure/payment regressions with matching source event/argument-tree fixtures; no source execution theorem |
| `Lowering/V08/CryptoObservations.lean` | Published Keccak output-word bound and fixed source/intrinsic word/ABI-byte observation transport; no hash/precompile implementation |
| `Lowering/V08/CryptoControls.lean` | Inhabited real Keccak pin, actual standard vector and wrong-byte/word kernel controls |
| `Lowering/V08/PayableMetadata.lean` | Source ordinary-entry payable/receive/fallback metadata and actual numeric frame payment guards; no exposure/body/readonly certificate |
| `Lowering/V08/PayableControls.lean` | Source receive membership and payment flags, malformed/noncallable/constructor refusals, actual paid/zero-call controls |
| `Lowering/V08/DeclarationRoles.lean` | Source contract/library role metadata on supplied typed catalogue, preserved storage/other keys and actual ordinary-call/create refusals |
| `Lowering/V08/RoleControls.lean` | Source library membership and real typed empty-library installation/refusal/catalogue controls |
| `Lowering/V08/InheritedMetadata.lean` | Published mutOK/FnOverrideOK payment-tag transport and actual entry-header guards; source body/dispatch remains separate |
| `Lowering/V08/InheritedControls.lean` | Nonempty two-contract source chain, proved baseFns/override certificate, funded header and exact wrong-header/mutability controls |
| `Lowering/V08/NestedControls.lean` | Two populated atomic rollback boundaries with real creation-continuation failure and complete observation controls. |
| `Lowering/V08/HandlerControls.lean` | Completed constructor failure, paid catch-handler failure, exact payload and ancestor rollback controls. |
| `Lowering/V08/LibraryHandlerControls.lean` | Real caller-context library work inside failed creation-handler rollback and exact context/payload controls. |
| `Lowering/V08/CreationSuccessControls.lean` | Successful creation, caller-library continuation, exact failure and rollback controls |
| `Lowering/V08/TransactionPrefixes.lean` | Arbitrary finite prefixes of actual transactions with ordered exact histories |
| `Lowering/V08/PrefixControls.lean` | Funded commit, real post-commit failures and reads with complete boundary observations |
| `Lowering/V08/SourceEnvironment.lean` | Actual independent resolved environment execution and intrinsic observation transport; explicit positive/zero horizons. |
| `Lowering/V08/SourceEnvironmentControls.lean` | Populated source state, both pipelines and actual paid target context controls. |
| `Lowering/V08/SourceFailures.lean` | Actual resolved literal-reason failure execution and exact intrinsic payload transport. |
| `Lowering/V08/SourceFailureControls.lean` | Binary, empty and unaligned reasons, horizon distinctions and real paid rollback. |
| `Lowering/V08/SourceKeccak.lean` | Actual resolved literal Keccak execution, exact heap allocation and explicitly pinned intrinsic byte/word observation. |
| `Lowering/V08/SourceKeccakControls.lean` | Populated binary, empty and 33-byte executions, both pipelines, complete machine and actual wrong-output controls. |
| `Lowering/V08/SourceEmit.lean` | Actual emit argument/encoding/static/failure boundaries, log-only erasure and exact intrinsic word encoding observations. |
| `Lowering/V08/SourceEmitControls.lean` | Declared event, populated source machine, allocation/local argument order, panic/static/timeout and malformed encoding controls. |
| `Lowering/V08/SourceCallable.lean` | Actual source callable initialization, selected body, checked frame, return extraction and caller-local/failure boundaries. |
| `Lowering/V08/SourceCallableControls.lean` | Populated two-argument/one-result source calls, declaration discrimination, exact contexts, order/local retention and failure controls. |
| `Lowering/V08/SourceDispatch.lean` | Published source free/outside-linearization selection and body lookup laws. |
| `Lowering/V08/SourceDispatchControls.lean` | Actual free/internal-library ambient context calls, real competing body, repeated reached calls, full state and independent intrinsic observations. |
| `Lowering/V08/SourceCustomErrors.lean` | Actual custom-error execution and selector transport with explicit independent signature input-byte equality. |
| `Lowering/V08/SourceCustomErrorControls.lean` | Populated exact custom-error payload/order/static/panic/timeout controls and concrete UTF-8 signature checks. |
| `Lowering/V08/SourceCustomErrorFailures.lean` | Actual custom-error argument/encoding failure boundaries. |
| `Lowering/V08/SourceCustomErrorFailureControls.lean` | Populated source panic, rethrow and aggregate-encoding-gap controls. |
| `Lowering/V08/SourceAbi.lean` | Actual source ABI expression allocation and existing byte observations. |
| `Lowering/V08/SourceAbiControls.lean` | Populated binary/dynamic/static ABI argument and allocation controls. |
| `Lowering/V08/SourceTransient.lean` | Actual typed source transient write/static/read/endTx/undo observations and selected intrinsic reset; canonical layout/frame relation remains open. |
| `Lowering/V08/SourceAbiEntryControls.lean` | Actual Source ABI allocation bytes and published eager/lazy entry decoding controls; no general calldata/body adequacy. |
| `Lowering/V08/SourceRethrow.lean` | Actual packed-literal allocation, reached-reference canonical rethrow and independent intrinsic byte observation. |
| `Lowering/V08/SourceRethrowControls.lean` | Populated complete-machine, neighboring-object, caller-local and horizon controls. |
| `Lowering/V08/SourceStandardRethrow.lean` | Actual standard ABI allocation/rethrow and distinct source timeout boundaries. |
| `Lowering/V08/SourceStandardRethrowControls.lean` | Full populated standard/reversed execution,320-byte payload, offset words and negative controls. |
| `Lowering/V08/SourcePrefixedRethrowControls.lean` | Actual selector/signature and string-reference allocation/rethrow, complete heap/state controls. |
| `Lowering/V08/SourceTransientRethrowControls.lean` | Actual transient statement / ABI declaration / canonical rethrow sequence; explicit rollback/reset controls. |
| `Lowering/V08/SourceTransientMixedRethrowControls.lean` | Actual mixed effecting ABI arguments after a transient-writing statement prefix, exact rethrow and explicit rollback. |
| `Lowering/V08/SourceTransientEmitControls.lean` | Actual effecting emit after a reached transient/caller prefix; exact log erasure, static order and explicit journal rollback/end. |
| `Lowering/V08/SourceTransientEmitPanicControls.lean` | Actual event argument panic after transient/hash prefixes; precise bytes, existing decoder observation and explicit rollback/end. |
| `Lowering/V08/SourceTransientBytesEmitControls.lean` | Valid dynamic-memory RawBytes event at reached transient/caller prefix; exact allocation, payload and boundary controls. |
| `Lowering/V08/H1Audit.lean` | V08 exact axiom inventory including finite-prefix and source-boundary controls. |
| `Lowering/V08/SourceTransientReentry.lean` | Explicit event execution, end and fresh transient reentry. |
| `Lowering/V08/SourceTransientOwnerRollback.lean` | Owner-isolated reached writes and explicit nested rollback. |
| `Lowering/V08/SourceTransientOwnerCommit.lean` | Reached inner commit, later write and outer rollback. |
| `Lowering/V08/SourceTransientInnerRollbackOuterCommit.lean` | Inner rollback, later owner write and outer commit. |
| `Lowering/V08/SourceTransientErrorCallerRollback.lean` | Exact raw errors followed by explicit caller rollback and end. |
| `Lowering/V08/SourceTransientReachedPayment.lean` | Actual funded Source transfer at the reached event/transient state. |
| `Lowering/V08/SourceTransientRejectedPayment.lean` | Actual unaffordable second transfer preserves its paid input. |
| `Lowering/V08/SourceTransientSameOwnerPayment.lean` | Same-owner identity and affordability versus distinct-owner draining transfer. |
| `Lowering/V08/SourceTransientZeroPayment.lean` | Zero distinct-owner transfer retains world but adds two journal entries. |
| `Lowering/V08/CallableReflection.lean` | Exact typed callable success reflection under injective observation, with funded and lossy counterexamples. |

## VA2 checked call-family consumer (AU04)

| Module | Purpose |
|---|---|
| `Calculus/CallFunctionAffine.lean` | Checked affine power coefficients, early-overflow preservation and exact shared-leaf cases |
| `Tools/CallFunctionShare.lean` | Stable explicit API aliases and original-walk versus whole-leaf measurements |
| `Examples/Tactics/CallFunctionAffine.lean` | Inhabited order, zero, word-edge, overflow and false-result controls |
| `Examples/Tactics/CallFunctionShare.lean` | Actual parsed non-offset call-family source proofs and old/new leaf pins |
| `Examples/Tactics/CallFunctionShareControls.lean` | Parsed countermodels and transactional profile/no-shrink refusal controls |
| `Calculus/CloseCallSharing.lean` | Bounded default leaf consumer; synchronous internal profile certificates and disjoint plain/joined routes |
| `Examples/Tactics/CallSharingDefault.lean` | Closer-only import, default source proofs, named leaf and joined-call controls |

## V15 P10 fetched execution step (Bridge)

| Module | Purpose |
|---|---|
| `Bridge/SolidityBridge/RoadmapV15/P10/Interface.lean` | `Site`: a state built with encoded Backend code and PC at an opcode; decoder and fetched-step facts. |
| `Bridge/SolidityBridge/RoadmapV15/P10/Controls.lean` | Inhabited nonzero prefix/immediate/context and actual decoder/fuel controls; fourteen scoped axiom reports. |
| `Bridge/SolidityBridge/RoadmapV15/P10/Execution.lean` | Exact charged fetched CALL/return-data/jump operations and X continuation; no assumed execution result. |
| `Bridge/SolidityBridge/RoadmapV15/P10/ExecutionControls.lean` | Funded/underfunded/static account execution, complete 18-field outcomes, copy opacity and jump/resource negatives. |
| `Bridge/SolidityBridge/RoadmapV15/P10/Modular.lean` | Full-precision ADDMOD/MULMOD scalar representation, actual fetched charged State and X continuation with explicit gas/stack bounds. |
| `Bridge/SolidityBridge/RoadmapV15/P10/ModularControls.lean` | Complete-State overflow-sensitive modular, zero/max modulus, 1024-stack and fetched combination controls; actual error-order negatives. |
| `Bridge/SolidityBridge/RoadmapV15/P10/ExponentConsumer.lean` | Scalar/reference EXP representation, actual fetched charged execution and proved 1610 local gas bound. |
| `Bridge/SolidityBridge/RoadmapV15/P10/PowerControls.lean` | Whole-State nonzero, wrap, maximal-exponent, stack, charge and actual EXP→ADDMOD controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StackFamilyConsumer.lean` | All legal typed DUP/SWAP indices against actual emitted decoding, charged checks and fetched State/X. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StackFamilyControls.lean` | Populated every-index clients, exact capacity boundaries, actual gas/arity/fuel/index/order negatives and fetched combination. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedDivisionConsumer.lean` | Bounded signed word transport and actual emitted/charged/fetched SDIV/SMOD State/X with explicit gas/stack bounds. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedDivisionControls.lean` | All sign combinations, raw zero/minimum wrap, narrow cleanup, full stack, ordered errors and complete fetched negative sequence. |
| `Bridge/SolidityBridge/RoadmapV15/P10/ArithmeticShiftConsumer.lean` | Actual SAR/BitVec/Scalar word transport, emitted decoding and charged fetched State/X, including saturation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/ArithmeticShiftControls.lean` | Full-State signed/count/boundary/resource negatives and actual fetched SAR→SMOD; no huge saturated powers. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StorageReadConsumer.lean` | Actual charged/fetched SLOAD/TLOAD, exact warm/cold resource bounds and existing finite typed source-observation transport. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StorageReadControls.lean` | Populated root/transient/source witnesses, exact two-insertion warming states and gas/fuel/permission/coverage negatives. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BalanceEnvironmentConsumer.lean` | Charged fetched BALANCE; the frame `funds` field is defined from the EVM account map (G31 ledger observation). |
| `Bridge/SolidityBridge/RoadmapV15/P10/BalanceWarmTransport.lean` | Actual BALANCE warmth, low160 probe aliases, ledger preservation and charged fetched transport. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BalanceWarmControls.lean` | Populated complete post-read state, distinct account probes and gas/fuel/order refusals. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BalanceEnvironmentControls.lean` | Populated complete-state balance, alias, warm/cold, ordered failure and ledger-origin controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/DecoderAgreement.lean` | All 117 non-immediate Backend/reference decoder targets and fetched dispatch, exposing CLZ→INVALID. |
| `Bridge/SolidityBridge/RoadmapV15/P10/DecoderAgreementControls.lean` | Populated family, ordered byte/state and real fallback/PC/opcode decoder controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/PushDecoderAgreement.lean` | Every intrinsic PUSH0..32 payload versus actual reference extraction/reader/fetched dispatch, with explicit bounds and modulo. |
| `Bridge/SolidityBridge/RoadmapV15/P10/PushDecoderControls.lean` | All-width nonuniform payloads, endian/length/truncation controls and arbitrary-seed whole-State PUSH client. |
| `Bridge/SolidityBridge/RoadmapV15/P10/FrozenInterface.lean` | Frozen V1 interface: 18 decode/charged-step/continuation statements (see `docs/feature-work/roadmap-v15-p10.md`). |
| `Bridge/SolidityBridge/RoadmapV15/P10/FrozenWitness.lean` | `FrozenV1.api` from existing P10 theorems; no new fact. |
| `Bridge/SolidityBridge/RoadmapV15/P10/ReturnCopyBounds.lean` | RETURNDATACOPY gate order and in-range gate, the gas-only charged state, and the out-of-range refusal lifted through `FrozenV1.api`. |
| `Bridge/SolidityBridge/RoadmapV15/P10/ReturnCopyBoundsControls.lean` | Populated gas, arity, range, endpoint, capacity and fuel controls; the gate does not depend on the static flag. |
| `Bridge/SolidityBridge/RoadmapV15/P10/MachineObservation.lean` | Actual fetched PC/GAS/MSIZE whole-State and X agreement with explicit gas/capacity bounds. |
| `Bridge/SolidityBridge/RoadmapV15/P10/MachineObservationControls.lean` | Populated machine observations, raw-word/stack/gas/fuel negatives and ordered three-opcode regression. |
| `Bridge/SolidityBridge/RoadmapV15/P10/CodeExtent.lean` | Native fetched CODESIZE whole-State and X agreement with explicit gas/capacity bounds. |
| `Bridge/SolidityBridge/RoadmapV15/P10/CodeExtentControls.lean` | Complete code-buffer observations, populated states and gas/fuel/stack/extent negatives. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionConsumer.lean` | Native fetched SIGNEXTEND and proved Scalar/reference out-of-range byte-index transport. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionControls.lean` | Populated signed/narrow/boundary values, complete code and ordered fuel/gas/stack refusals. |
| `Bridge/SolidityBridge/RoadmapV15/P10/ExternalCodeExtent.lean` | Actual fetched EXTCODESIZE account-code lookup, warm/cold charge and whole-State transport. |
| `Bridge/SolidityBridge/RoadmapV15/P10/ExternalCodeExtentControls.lean` | Populated distinct account code, low160 alias, warm/static/resource and source-refusal controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/ByteObservation.lean` | Fetched BYTE, exact big-endian arithmetic and intrinsic typed word-byte image transport. |
| `Bridge/SolidityBridge/RoadmapV15/P10/ByteObservationControls.lean` | Complete ordered bytes, typed-image client, endian/index and stack/gas/fuel refusal controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/CalldataExtent.lean` | Arbitrary fetched CALLDATASIZE site and explicit Source.Calldata.input byte installation transport. |
| `Bridge/SolidityBridge/RoadmapV15/P10/CalldataExtentControls.lean` | Nonzero-PC/source-input clients, decoded-object separation and exact size/resource observations. |
| `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentTasksV1.lean` | Generated unproved environment producer statements and separate routine cost/arity/expansion/refusal claims. |
| `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentObservationProducer.lean` | Actual fetched ORIGIN/GASPRICE/CHAINID whole-State and X clauses from explicit finite local facts. |
| `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentObservationWitness.lean` | Concrete local-fact witnesses and populated producer clients with native resource/origin negatives. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionPositive.lean` | Mask/sign-bit arithmetic; positive, residue and all-index SIGNEXTEND word/Scalar/fetched agreement. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionPositiveWitness.lean` | Nonzero 8/16/256-bit clients, strict-bound and byte-index negatives, complete State/code observations. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionResidueWitness.lean` | High-bit and negative-fullword truncation clients, clear-sign-residue and ordered State controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionAllWitness.lean` | Unified all-index/sign SIGNEXTEND clients, full-width/large-index boundaries and wrong-unsigned/wrap controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UnsignedDivisionConsumer.lean` | Arbitrary emitted-site DIV/MOD word/Scalar/charged fetched-State and X transport, plus actual output-capacity refusal. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UnsignedDivisionControls.lean` | Populated unsigned high-word, zero, maximum, stack-capacity and ordered refusal/observation controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StorageWarmTransport.lean` | SLOAD warm cost after the vendor update, distinct-key cost isolation, TLOAD separation, fetched SLOAD resource frame. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StorageWarmControls.lean`, `Bridge/SolidityBridge/RoadmapV15/P10/StorageIsolationControls.lean` | Populated warm/cold, owner/key, transient and equal-pair controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StorageOwnerFixtures.lean` | Populated same-slot/different-owner post-SLOAD cost-probe data. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StorageOwnerControls.lean` | Direct distinct-owner client, cold/prewarmed cost separation and complete ordered observations. |
| `Bridge/SolidityBridge/RoadmapV15/WordByteTransport.lean` | Reused pure backend immediate/word/byte transport; unchanged original owned proof package. |
| `Bridge/SolidityBridge/RoadmapV15/EncodingUniqueness.lean` | Reused exact length/value byte-encoding uniqueness; no allocator or hash interpretation. |
| `Bridge/SolidityBridge/RoadmapV15/ReferenceReader.lean` | Reused actual pinned reader versus backend big-endian decoding. |
| `Bridge/SolidityBridge/RoadmapV15/P10/WordPushConsumer.lean` | Exact Scalar.pushWord payload, decode, charged fetched State/X and legal full-stack overflow. |
| `Bridge/SolidityBridge/RoadmapV15/P10/WordPushFixtures.lean` | Typed populated account/memory/code fixture data; no new machine relation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/WordPushControls.lean` | Complete-State word/zero/signed/wrap controls, legal capacity bounds, gas/fuel and endian/length negatives. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedCleanupSites.lean` | Actual signedCode tail site and emitted byte-index/native cleanup word transport. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedCleanupTail.lean` | Exact signedCode image and complete charged fetched SIGNEXTEND tail paired with intrinsic signed cleanup. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedCleanupFixtures.lean` | Populated explicit tail-entry fixtures; no preceding PUSH execution witness. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedCleanupControls.lean` | Universal producer client, complete-State signed execution, gas/fuel and truncation/width/index/order controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedCleanupAlignment.lean` | Actual gas subtraction, modulo-PC addition and complete PUSH-output/tail-entry State equality. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedCleanupComposition.lean` | Both emitted signedCode instructions: intrinsic result, counted fetched execution and X continuation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedCompositionFixtures.lean` | Exact-gas populated initial/final state data for both instructions. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedCompositionControls.lean` | Direct producer client, signed/truncating/full-width complete-State controls, gas/fuel and wrap/order negatives. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BitwiseWords.lean` | Actual pinned AND/OR/XOR modulo versus intrinsic bounded words. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BitwiseConsumer.lean` | Arbitrary emitted-Site/adequate-gas AND/OR/XOR Scalar, checked driver and complete-State X correspondence. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BitwiseFixtures.lean` | Populated static/writable bitwise code, gas and expected State data. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BitwiseControls.lean` | Distinct per-operation State/X clients, legal stack boundary, resource/refusal and ordered observations. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UnsignedCleanupLayout.lean` | Actual unsigned mask/result, adequate native gas debit, emitted code image and complete PUSH/tail State alignment. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UnsignedCleanupExecution.lean` | Both actual emitted unsignedCode instructions with exact local gas6 and full-State X continuation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UnsignedCleanupFixtures.lean` | Populated exact-gas initial/final States and actual emitted PC-fit witness. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UnsignedCleanupControls.lean` | Truncating/full-width direct clients, legal peak-stack success/refusal, gas/fuel and ordered encoding/buffer controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BooleanNotWords.lean` | Universal ISZERO word transport and actual canonical Boolean-not instruction selection. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BooleanNotConsumer.lean` | Arbitrary-site charged fetched ISZERO and selected typed Boolean-not complete-State/X consumers. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BooleanNotFixtures.lean` | Populated static/writable clients and a nonempty supplied jump-array parameter probe. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BooleanNotControls.lean` | Canonical/raw separation, full legal unary capacity, ordered observations and gas/arity/fuel negatives. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UintNotWords.lean` | Existing word complement transport and actual unsigned-not certificate selection. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UintNotConsumer.lean` | Arbitrary-site charged fetched NOT, complete-State/X and optional intrinsic uint evaluation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UintNotFixtures.lean` | Populated static/writable unsigned-not client data and supplied-array probe. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UintNotControls.lean` | Inhabited typed258, word boundaries, full legal unary capacity, ordered observations and refusal controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/WrappingArithmeticWords.lean` | Existing ADD/SUB/MUL word representation and actual wrapping certificate selection. |
| `Bridge/SolidityBridge/RoadmapV15/P10/WrappingArithmeticConsumer.lean` | Arbitrary-site charged ADD/SUB/MUL, selected optional intrinsic uint evaluation and complete State/X. |
| `Bridge/SolidityBridge/RoadmapV15/P10/WrappingArithmeticFixtures.lean` | Populated original Op/Site/State data with explicit per-opcode observation cost. |
| `Bridge/SolidityBridge/RoadmapV15/P10/WrappingArithmeticControls.lean` | Inhabited typed wrapping, order/high-bit/boundary clients, legal capacity and distinct gas/fuel/checked-operation negatives. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LogicalShiftWords.lean` | Existing full-word SHL/SHR saturation and word-representation transport. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LogicalShiftConsumer.lean` | Actual charged fetched count/value SHL/SHR steps and complete State/X. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LogicalShiftLayout.lean` | Selected SWAP1-plus-shift bytes, one-byte prefix/PC transport and full intermediate-State alignment. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LogicalShiftExecution.lean` | Both emitted selected unsigned shift instructions, derived intermediate resources and actual typed optional evaluation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LogicalShiftFixtures.lean` | Populated source-order shift inputs, post-SWAP PC-fit witness and exact two-instruction output data. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LogicalShiftControls.lean` | Typed nonzero clients, full-count saturation, legal capacity, two-stage gas/fuel failures and complete ordered observations. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedLeWord.lean` | Existing signed-word SGT bridge consumed through exact representation equality. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedLePrimitive.lean` | Actual charged fetched SGT on arbitrary represented sites, retaining complete State/X. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedLeLayout.lean` | Selected intLe SGT/ISZERO code, prefix extent and complete intermediate-State alignment. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedLeExecution.lean` | Both selected signed-le instructions with derived predicate/resources and optional intrinsic source evaluation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedLeFixtures.lean` | Populated typed signed comparison inputs and actual code-position witness. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedLeControls.lean` | Negative/equal/signed-boundary clients, legal capacity, staged refusals and complete ordered observations. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StorageChaseLayout.lean` | Actual two-SLOAD bytes, value-directed intermediate State, PC alignment and computed charge bounds. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StorageChaseExecution.lean` | Both fetched reads with exact computed adequacy/debit, full State/X and persistent/transient observation preservation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StorageChaseCost.lean` | Exhaustive numeric equal/distinct next-key charge classification from published warmth/isolation facts. |
| `Bridge/SolidityBridge/RoadmapV15/P10/PopConsumer.lean` | Arbitrary-site charged POP, exact Scalar tail, complete native State and X continuation with explicit legal input/resources. |
| `Bridge/SolidityBridge/RoadmapV15/P10/PopControls.lean` | Populated static/writable, zero/max, legal stack boundaries, ordered state and gas/arity/fuel refusals. |
| `Bridge/SolidityBridge/RoadmapV15/P10/JumpZeroConsumer.lean` | Universal zero-condition JUMPI: actual destination-check bypass, charged fetched fallthrough/full State/X under legal input and gas bounds. |
| `Bridge/SolidityBridge/RoadmapV15/P10/JumpZeroControls.lean` | Maximum destination, arbitrary-array, static/writable, legal stack boundaries and nonzero/refusal contrasts with ordered observations. |
| `Bridge/SolidityBridge/RoadmapV15/P10/JumpMemberConsumer.lean` | Supplied-membership JUMPI charged State/X transport and nonzero missing-target driver/X refusal derived from actual checks. |
| `Bridge/SolidityBridge/RoadmapV15/P10/JumpMemberControls.lean` | Taken/zero/max condition clients, legal stack boundaries, missing-target priority and complete ordered byte/state controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedJumpConsumer.lean` | Published linked-reference certificate supplies membership, nonwrapping and target decode for code-aligned Backend JUMPI State/X transport. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedJumpFixtures.lean` | Actual Backend encoding and populated entry for the published linked-loop image; no prefix/frame-origin assertion. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedJumpControls.lean` | Certified exit72/fallthrough37 clients from PC36, exact entire image, legal boundaries and STOP73 target refusal. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedCompletionLayout.lean` | Arbitrary native caller-state entry/output records and actual JUMPDEST/STOP resource gates. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedCompletion.lean` | Modular linked JUMPI/JUMPDEST/STOP X completion with eleven-gas adequacy and exact natural debit. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedCompletionControls.lean` | Exact/excess gas, legal stack boundaries, fuel/gas refusals and full ordered terminal State including STOP returnData clearing. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StorageChaseFixtures.lean` | Populated value-not-key chain, alias and owner-specific warmth data with coherent memory. |
| `Bridge/SolidityBridge/RoadmapV15/P10/StorageChaseControls.lean` | Full-state nonalias/alias clients, direct charge-law consumers, exact gas/fuel/stack and ordered observation controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedResourceBounds.lean` | Universal legal-tail ten-gas and three-fuel refusals through the actual linked fetched suffix. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedResourceControls.lean` | Both permissions, full legal stack and populated ordered buffer observations at resource boundaries. |
| `Bridge/SolidityBridge/RoadmapV15/P10/NonbranchTables.lean` | Actual nonbranch charged-gate table independence and all-outcome/fetched-State/X PUSH32 transport for arbitrary destination arrays. |
| `Bridge/SolidityBridge/RoadmapV15/P10/NonbranchTableControls.lean` | Populated arbitrary/duplicate tables, both permissions, gas/stack/fuel order, JUMPI counterexample and complete ordered caller observations. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedEntry.lean` | Actual two-JUMPDEST entry prefix, two-gas debit and native frame transport at PC2 for arbitrary legal stacks and supplied tables. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedEntryControls.lean` | Both permissions, empty/full capacity, prefix-versus-whole-run resource negatives and complete ordered linked-image observations. |
| `Bridge/SolidityBridge/RoadmapV15/P10/CountedAppend.lean` | Exact composition of existing counted driver prefixes; no terminal-X continuation claim. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedZero.lean` | Actual three-instruction linked entry through ISZERO, arbitrary scalar operand, derived alignment and five-gas/native-frame transport. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedZeroControls.lean` | Zero/signed/full-capacity callers, original independent State observation, following-PUSH refusal and gas-before-arity controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedProgram.lean` | Actual four-step PUSH prefix and zero-operand seven-instruction reference exit, exact nineteen-gas debit and native terminal frame. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedProgramControls.lean` | Both permissions, legal capacity, exact gas/fuel and wrong-table refusals, nonzero prefix and complete ordered terminal State. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedFallthrough.lean` | Derived nonzero ISZERO flag and actual five/six-step fallthrough prefixes to PC37/38, exact resource and native-frame transport. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedFallthroughControls.lean` | Arbitrary tables, both permissions, nonzero/signed capacity clients, zero counterexample and ordered resource failures/state. |
| `Bridge/SolidityBridge/RoadmapV15/P10/InvocationEnvironment.lean` | H7-checked charged fetched ADDRESS, CALLER and CALLVALUE, whole native State/X continuation and explicit resource bounds. |
| `Bridge/SolidityBridge/RoadmapV15/P10/InvocationEnvironmentControls.lean` | H7-checked populated invocation controls: complete expected States, distinct identities, legal capacity and gas/fuel/overflow ordering. |
| `Bridge/SolidityBridge/RoadmapV15/P10/HeaderEnvironment.lean` | Charged fetched TIMESTAMP and SELFBALANCE at arbitrary emitted sites, exact costs2/5 and whole-State/X observations. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SelfBalanceTransport.lean` | Canonical code-owner ledger view and G31 SELFBALANCE slice/fetched correspondence. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SelfBalanceControls.lean` | Direct source/fetched API client, distinct owner/stack/candidate views and maximum-address boundary. |
| `Bridge/SolidityBridge/RoadmapV15/P10/HeaderEnvironmentControls.lean` | Populated owner-ledger/time controls, raw word wrapping and absent-account behavior, capacity/resource order and complete ordered States. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BlockMetadata.lean` | Charged native COINBASE/NUMBER/PREVRANDAO/GASLIMIT/BASEFEE reads for arbitrary supplied arrays, paired with unchanged six-opcode environment-slice refusals. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BlockMetadataControls.lean` | Distinct populated header values, raw number wrapping, complete ordered States and gas/fuel/capacity/refusal controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedBackedgePush.lean` | Charged final PUSH32 continuation of the nonzero linked prefix; explicit gas, stack and fuel bounds. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedBackedgePushControls.lean` | Complete populated state and ordered-byte controls, boundary capacity and resource refusals. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedCycle.lean` | One charged nonzero fetched cycle to byte zero, consuming the existing linked reference certificate. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedCycleControls.lean` | Populated finite-cycle states, exact gas/fuel boundaries and missing-target refusal. |
| `Bridge/SolidityBridge/RoadmapV15/P10/NegationBody.lean` | Actual selected G25 signed-negation body to two fetched steps, exact resources and frame; checked guard/panic execution remains open. |
| `Bridge/SolidityBridge/RoadmapV15/P10/NegationBodyControls.lean` | Complete signed/zero/boundary States, peak capacity, gas/fuel refusals and minimum-wrap versus Scalar-guard controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/NegationSourceConsumer.lean` | Derives non-minimum source range/result and relates its encoding to the actual fetched negation body; minimum failure separate. |
| `Bridge/SolidityBridge/RoadmapV15/P10/NegationSourceControls.lean` | Typed signed/zero/max clients, ordered native output and simultaneous minimum source-failure/body-success control. |
| `Bridge/SolidityBridge/RoadmapV15/P10/EqualityConsumer.lean` | General fetched EQ word/typed-certificate agreement with actual decoder, charged gate, full State and continuation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/EqualityControls.lean` | Populated typed/same/high-bit-distinct/boundary clients, gas/fuel/arity refusals and complete ordered State observations. |
| `Bridge/SolidityBridge/RoadmapV15/P10/NegationTest.lean` | Three actual fetched DUP1/PUSH32-minimum/EQ steps to the existing Scalar overflow flag, exact resources/frame and legal-entry peak overflow refusal. |
| `Bridge/SolidityBridge/RoadmapV15/P10/NegationTestControls.lean` | Complete ordinary/minimum States, legal peak1024 and refused peak1025, gas/fuel negatives and ordered code/buffer/account observations. |
| `Bridge/SolidityBridge/RoadmapV15/P10/InequalityConsumer.lean` | Actual fetched EQ/ISZERO composition with typed scalarNe certificate, exact resource premises and full State continuation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/InequalityControls.lean` | Direct all-primitive clients, complete expected States, high-bit/signed/capacity/resource and ordered-observation controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UnsignedOrderConsumer.lean` | General fetched LT/GT word and typed-certificate agreement with actual decoder, charged gate and full State continuation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UnsignedOrderControls.lean` | Direct typed clients, unsigned-versus-signed/reversed order, boundary/capacity/resource negatives and complete ordered States. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UnsignedNonStrictConsumer.lean` | Actual fetched GT/ISZERO and LT/ISZERO typed LE/GE transport, exact resource premises and full State continuation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/UnsignedNonStrictControls.lean` | Direct typed clients, equality-versus-strict/directional negatives, complete States and capacity/resource/ordered-observation controls. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedGeConsumer.lean` | General actual signed SLT and SLT/ISZERO typed intGe transport with reserved word bridge, explicit resources and complete State continuation. |
| `Bridge/SolidityBridge/RoadmapV15/P10/SignedGeControls.lean` | Direct typed signed LT/GE clients, unsigned contrast/min/max/equality, complete States and capacity/resource/order negatives. |
| `Bridge/SolidityBridge/RoadmapV15/P10/MetadataPushConsumer.lean` | Published bounded metadata emitter to actual fetched PUSH0–PUSH32 with precise width/value, charged gas, full State/X and full-stack refusal. |
| `Bridge/SolidityBridge/RoadmapV15/P10/MetadataPushControls.lean` | Complete zero/byte/selector/ABI/full-width States, cost/capacity/resource and endian/length/order controls; no allocator premise. |
| `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentSelection.lean` | Canonical five-key G31 view, typed source representation and charged fetched transport. |
| `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentSelectionControls.lean` | Inhabited all-key source/native clients, wrapped timestamp and ordered negative observations. |
| `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentGuards.lean` | Exact all-key gas/stack checks, counted-prefix result and actual X fuel/refusal order. |
| `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentGuardControls.lean` | Both-permission legal stack boundaries, populated full States and ordered fuel/resource negatives. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BinaryGuards.lean` | Twenty-op numeric charged-gate correspondence, legal capacity, fetched refusals and exact short-fuel order. |
| `Bridge/SolidityBridge/RoadmapV15/P10/BinaryGuardControls.lean` | Populated result/cost rows, complete ordered States and distinct legal/raw-overlimit resource controls. |

## P1 runtime frames (producer checkpoint; [runtime-frame-p1.md](../feature-work/runtime-frame-p1.md))

| Module | Purpose |
|---|---|
| `Backend/InternalFlow/RuntimeFrameSemantics.lean` | `callRec` replaced by its finite thunk body, with an equal execution. |
| `Backend/InternalFlow/RuntimeFrameTarget.lean` | Published `Calls` certificates transported along that equation. |
| `Backend/InternalFlow/RuntimeFrameTransport.lean` | Argument, entry/body extension and result export at the checked target endpoint. |
| `Backend/InternalFlow/RuntimeFrameStack.lean` | Runtime-pointer word push/pop on the existing machine. |
| `Backend/InternalFlow/RuntimeFrameSaved.lean` | Reserved frame words preserve `StateRepr`; scalar/reference saves. |
| `Backend/InternalFlow/RuntimeFrameFootprint.lean` | Word intervals preserved by allocation, rebinding and array-write leaves. |
| `Backend/InternalFlow/RuntimeFrameComposition.lean` | Checked certificates paired with constructor-derived scratch-safety proofs. |
| `Backend/InternalFlow/RuntimeFrameRestore.lean` | Restoring a saved word into the original caller cell. |
| `Backend/InternalFlow/RuntimeFrameContext.lean` | Whole caller-context capture/restore around a checked body. |
| `Backend/InternalFlow/RuntimeFrameInterfaceV1.lean` | Frozen v1 signatures: `Emission`, `Entry`, `Returned` and the unproved `Pending*` premise structures. |
| `Backend/InternalFlow/RuntimeFrameInterfaceV2.lean` | Frozen v2 `Pending*` structures: each needs an entry whose source run succeeds (`SuccessfulEntry`) or bare-reverts (`RevertingEntry`); v1 relations unchanged. |
| `Backend/InternalFlow/RuntimeFrameInterfaceV3.lean` | Frozen v3: explicit external admission domain, exact-input/index `EntryCoverage`, `AdmissionAgreement` duty and independently witnessed admitted success and bare revert in every `Pending*` structure. |
| `Backend/InternalFlow/RuntimeFrameRestoredRepresentation.lean` | Implements the v1 full restored representation from the source-tail equation and alias-flag transport. |
| `Backend/InternalFlow/RuntimeFrameCapturedProgram.lean` | Capture, checked body and restore with full representation; captured bare-revert absorption. |
| `Backend/InternalFlow/RuntimeFrameReference.lean`, `Backend/InternalFlow/RuntimeFrameResult.lean` | Reached memory-reference and primitive-result export into caller bindings with the full reached representation. |
| `Backend/InternalFlow/RuntimeFrameCapturedReference.lean` | Capture/body/restore followed by typed reference export and caller use; older-frame and allocator transport. |
| `Backend/InternalFlow/RuntimeFrameCallAgreement.lean` | Inversion of an actual typed call into arguments, body frame and exported caller result (void and memory returns). |
| `Backend/InternalFlow/RuntimeFrameNoneProducer.lean` | v2 void-call, fixed-thunk and failure producers built from checked certificates and real entry witnesses. |
| `Backend/InternalFlow/RuntimeFrameV3RecursiveProducer.lean`, `Backend/InternalFlow/RuntimeFrameV3RecursiveUnwind.lean` | Runtime descent prefixes at every horizon and LIFO return loop with captured caller recovery (target side only). |
| `Backend/InternalFlow/RuntimeFrameV3RecursiveSource.lean` | Actual `callRec` countdown family: all-horizon execution and `RecursiveReturnCoherence`; no v3 recursive instance. |
| `Backend/InternalFlow/RuntimeFrameV3CallProducer.lean`, `Backend/InternalFlow/RuntimeFrameV3CallProducerControls.lean` | v3 `PendingCallProducer` for primitive value-returning calls (`coverage`, `returns`, `bare_revert`, `make`) and an applied control with real success and revert runs. |
| `Backend/InternalFlow/RuntimeFrameV3CallProducerRef.lean` | v3 `PendingCallProducer` for typed memory-return and tuple call forms (`coverage`, `returns`, `bare_revert`, `make`); success/revert witnesses and profile agreement stay explicit inputs. |
| `Backend/InternalFlow/RuntimeFrameV3BareRevertProducer.lean` | P1-REVERT: `bare_revert` for any statement; `directProducer`/`callProducer` inhabit `PendingBareRevertProducer` on one fixture with real reverting runs. |
| `Backend/InternalFlow/RuntimeFrameV3FixedThunkProducer.lean` | P1-THUNK: `PendingFixedCallRecProducer` for one array-writing thunk with real success and out-of-bounds revert runs. |
| `Backend/InternalFlow/RuntimeFrameV3CountdownWitness.lean` | Populated core-only countdown endpoint; actual prefixes/arguments, full caller reconstruction and ordered observations. No general recursive producer claim. |
| `Backend/InternalFlow/RuntimeFrameV3BarePrefix.lean` | Derived reached entry/allocation input and exact bare-revert execution after a successful checked prefix; no rollback/profile closure. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatorReturn.lean` | Recursive return allocator transport and inhabited callee-only ownership client; zero source allocation, with initial ownership explicit. |
| `Backend/InternalFlow/RuntimeFrameV3RecursiveResult.lean` | Actual allocator-backed native body/runtime `GrowingResult` client; retains shallow exhaustion mismatch. |
| `Backend/InternalFlow/RuntimeFrameV3ParentRestore.lean` | Actual first-parent typed restore and allocator transport from reached child/saved words, with inhabited countdown client. |
| `Backend/InternalFlow/RuntimeFrameV3ParentPrefixes.lean` | Typed actual running unwind prefixes, remaining payload transport and inhabited ordered-observation controls. |
| `Backend/InternalFlow/RuntimeFrameV3ParentStop.lean` | Final false guard, typed completed unwind and stable later horizons, with populated and empty-history controls. |
| `Backend/InternalFlow/RuntimeFrameV3NativeParents.lean` | Actual indexed native child-call/return clauses and represented parent poststate linkage; exhaustion and child-export controls. |
| `Backend/InternalFlow/RuntimeFrameBytes.lean` | P6-backed numeric caller-cell restoration: byte-image save/clobber/restore runs on the existing machines; no dynamic loads or source/world rollback. |
| `Backend/StructuredFlow/BranchSelector.lean`, `Backend/StructuredFlow/ExitSelector.lean`, `Backend/StructuredFlow/CoreScopes.lean`, `Backend/StructuredFlow/CoreSequence.lean` | G36.01 target branch/exit selectors and core-compiler scope adapters ([G36](../feature-work/roadmap-g36-structured-flow.md)). |
| `Backend/StructuredFlow/{Branch,Exit,CoreScope,CoreSequence}Controls.lean` | Concrete selector, exit and scope controls. |
| `Backend/InternalFlow/RuntimeFrameV3RecursiveActivation.lean`, `RuntimeFrameV3RecursiveDescent.lean`, `RuntimeFrameV3RecursiveHistory.lean` | Countdown family: checked activation bridge, descent at every reached horizon, saved parent history and nearest-parent pop. |
| `Backend/InternalFlow/RuntimeFrameV3PairedUnwind.lean`, `RuntimeFrameV3RecursiveReturn.lean` | Countdown family: paired all-parent unwind and the descent-plus-unwind endpoint in the original `StateRepr` (hand-written image). |
| `Backend/InternalFlow/RuntimeFrameMutation.lean`, `RuntimeFrameNested.lean`, `RuntimeFrameReferenceProgram.lean`, `RuntimeFrameCodeEquality.lean` | One-level and nested call compilers (`compileCall`), reference-returning programs, Boolean instruction-list equality. |
| `Backend/InternalFlow/RuntimeFrameV3ArrayProbe.lean` | Public checked array-probe adapter, exact success identity and bare-failure suffix transport with represented/owned controls. |
| `Backend/InternalFlow/RuntimeFrameV3GuardedRecursion.lean` | Actual scoped recursive probe, native child-call transport, initialized bare-failure coupling and witnessed same-image success/revert with exhaustion controls. |
| `Backend/InternalFlow/RuntimeFrameV3GuardedPrefixes.lean` | Arbitrary-counter source horizons, actual guarded/unprobed same-state target prefixes and returning endpoint with witnessed read domain/capacity. |
| `Backend/InternalFlow/RuntimeFrameV3GuardedCaller.lean` | Native guarded call enter/leave at all horizons and full target caller-tail reconstruction, with populated success/failure and complete observations. |
| `Backend/InternalFlow/RuntimeFrameV3CallerPrefixes.lean` | Actual saved history and full active-parameter/protected-tail representation at running recursive horizons, with populated snapshots and stopped stability. |
| `Backend/InternalFlow/RuntimeFrameV3HeapDomain.lean` | Derive exact guarded read success/failure and local recursive read domain from selected typed heap length; witnessed same-program prefix and failure transport. |
| `Backend/InternalFlow/RuntimeFrameV3DomainTransport.lean` | Exact old read/domain transport through real typed allocation, scoped source/target client and actual mutation counterexample to heap preservation. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingActivation.lean` | Actual allocating callRec family, generic checked child entry and witnessed paired return with grown heap, exact cost and complete frame observations. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingSource.lean` | Actual allocating recursive success/exhaustion induction, exact object growth and native full-caller export with a populated two-activation source client. |
| `Backend/InternalFlow/RuntimeFrameResultAgreement.lean` | Successful-output agreement under existing typed result and execution operators, with no failed-state or termination assertion. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingCoherence.lean` | Exact allocating-family source-return coherence at all quotation pairs and a populated all-sufficient-index caller control. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingPrefixes.lean` | Actual allocating fixed-image running prefixes, reached active parameter frames and exact allocator growth, with populated horizon/stop/countercontrols. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingResume.lean` | Proved residual source continuation for allocating target prefixes and exact completed-source/reached-heap coupling, with native caller identity controls. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingHistory.lean` | Actual allocating descent saved-parent payload history and protected low-frame exterior. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingReturn.lean` | Matched completed-source and target allocating unwind endpoint with exact growth and populated controls. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingFailure.lean` | Actual allocation-before-read-failure source/native-call and target image transport, with represented intermediate and halt controls. |
| `Backend/InternalFlow/RuntimeFrameV3CallerReframe.lean` | Caller-local reconstruction over reached heap/globals, with an inhabited base-one allocating recursive call endpoint. |
| `Backend/InternalFlow/RuntimeFrameV3ScalarArgument.lean` | Actual nonidentity scalar argument entry, stack-held caller save and allocating recursive return restoration. |
| `Backend/InternalFlow/RuntimeFrameV3MemoryArgument.lean` | Distinct memory argument entry, real two-word caller stack save and typed allocating recursive return restoration. |
| `Backend/InternalFlow/RuntimeFrameV3ArgumentEntry.lean` | General exact typed argument output and checked entry/caller frames, with public compiler success/failure clients and derived scratch safety. |
| `Backend/InternalFlow/RuntimeFrameV3ArgumentCall.lean` | Actual public compiled argument prefix composed with a source-coupled allocating recursive return and retained caller frame. |
| `Backend/InternalFlow/RuntimeFrameV3ArgumentCalleeFailure.lean` | Actual checked argument entry and reached capacity transport allocation-before-read bare revert, with a populated successful intermediate and suffix controls. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingZero.lean` | Generic zero-counter image and arbitrary-caller checked-prefix composition without unreachable allocation ownership, with a populated no-owner control. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingArguments.lean` | Arbitrary-context positive allocating argument/call composition with real reached capacity, caller export and complete inhabited endpoint. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingQuotations.lean` | All sufficient source quotations share the actual allocating argument/call target endpoint, with exact shallow exhaustion and mismatch controls. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingOutcome.lean` | Uniform zero, allocating return and first-read failure with source-reached demand, adequate quotation and returning-path-only frame obligations. |
| `Backend/InternalFlow/RuntimeFrameV3RecursiveIngress.lean` | Emitted cursor-to-bottom setup preserves frozen Entry/capacity and couples actual recursive return without an initial bottom sentinel premise. |
| `Backend/InternalFlow/RuntimeFrameV3AllocatingEmission.lean` | One state-budgeted allocating recursive image with universal Entry return/bare-revert proofs, real V2 producer and explicit remaining V3 domain duties. |
| `Backend/InternalFlow/RuntimeFrameV3EmissionPrefixes.lean` | Actual emission Entry to native/target allocating descent horizons, saved parents, exact growth and stable stopped child before unwind. |
| `Backend/InternalFlow/RuntimeFrameV3EmissionUnwind.lean` | Actual allocating emission Entry to represented paired-unwind parent horizons, exact growth, full populated observations and stable final guard. |
| `Backend/InternalDispatch.lean`, `Backend/InternalDispatch/Typed.lean`, `Backend/InternalDispatch/Agreement.lean`, `Backend/InternalDispatch/Chain.lean` | G37.03/P4 typed dispatch tables, full-signature checks and the typed equality-guard chain (not emitted bytecode). |
| `Backend/InternalDispatch/FrozenV1.lean`, `Backend/InternalDispatch/FrozenV2.lean`, `Backend/InternalDispatch/FrozenV3.lean` | Dispatch consumers of the frozen P1 v1–v3 `Pending*` families; v3 transports an approved input through profile agreement and coverage. |
| `Backend/InternalDispatch/Controls.lean`, `Backend/InternalDispatch/FrozenV1Controls.lean`, `Backend/InternalDispatch/FrozenV2Controls.lean`, `Backend/InternalDispatch/FrozenV3Controls.lean` | Source-backed selector controls and refusals; empty-domain refusal for v3. |

## P9 checked call graphs and Source preservation/progress

See [p9-checked-callgraphs.md](../feature-work/p9-checked-callgraphs.md), [source-preservation-allocations.md](../feature-work/source-preservation-allocations.md) and [source-progress-checked.md](../feature-work/source-progress-checked.md).

| Module | Purpose |
|---|---|
| `Lowering/P9/ElaboratedCalls.lean` | `CallsOK` for one declaration of an actual elaborated program. |
| `Lowering/P9/ElaborationAdmission.lean` | Elaborator/body-certificate transport for call admission. |
| `Lowering/P9/InferenceCuts.lean` | Reusable exact cuts through the elaborator. |
| `Lowering/P9/DeclarationIdentity.lean` | Decidable equality of intrinsic source declarations. |
| `Lowering/P9/FragmentDecidable.lean` | Decision procedures for the existing call-closed value fragment. |
| `Lowering/P9/ProgramAdmission.lean` | `WholeProgram.check` and `check_sound`: a closed allowlist checked against the elaborated program derives `CallsOK`. |
| `Lowering/P9/FunctionCatalog.lean` | `functions`/`checkFunctions`: the complete function catalogue of a unit. |
| `Lowering/P9/CallControls.lean`, `Lowering/P9/AdmissionControls.lean`, `Lowering/P9/ProgramControls.lean`, `Lowering/P9/GraphControls.lean`, `Lowering/P9/RecursiveControls.lean`, `Lowering/P9/ReturnControls.lean`, `Lowering/P9/CatalogControls.lean` | Inhabited admission, two-function and recursive graphs, horizon timeouts, and refusals (no body, wrong return, missing leaf). |
| `Lowering/P9/OverrideControls.lean` | An elaborated inherited override: dispatch of the base declaration selects the derived body, and an abstract bodyless base dispatched to a concrete override. |
| `Source/Preservation/Frames.lean`, `Source/Preservation/LocalFrames.lean`, `Source/Preservation/StatementFrames.lean`, `Source/Preservation/CallFrames.lean` | `MemOK` across `EM.sub`, scope and call frames; caller locals restored. |
| `Source/Preservation/Reads.lean`, `Source/Preservation/ValueConversions.lean`, `Source/Preservation/ResultValidity.lean` | Reads, implicit conversions and result references preserve the invariant. |
| `Source/Preservation/AllocationSites.lean`, `Source/Preservation/MemberPacking.lean`, `Source/Preservation/Encoding.lean`, `Source/Preservation/ArrayLiterals.lean` | Allocating string, struct, `abi.encode` and inline-array arms. |
| `Source/Preservation/Combinators.lean`, `Source/Preservation/Expressions.lean`, `Source/Preservation/Statements.lean`, `Source/Preservation/Fragment.lean` | Joint all-horizon memory preservation (`fragMemAt`) for the existing call value fragment under `CallsOK`. |
| `Source/Preservation/EncodingVariants.lean` | Preservation for every `abi.encode*` kind (`evalE_abiKind_mem`). |
| `Source/Preservation/Controls.lean` and its `*Controls.lean` | Allocation, frame, caller-reference, storage-copy, array-literal and fragment controls. |
| `Source/Progress/CheckedPrograms.lean` | Progress and memory preservation for elaborated programs with a checked complete catalogue. |
| `Source/Progress/Controls.lean` | Contract-backed admission, memory-prefix consumer and refusal controls. |
| `Source/Progress/BuiltinAdmission.lean`, `Source/Progress/ArithmeticBuiltins.lean`, `Source/Progress/RecoveryBuiltin.lean`, `Source/Progress/LiteralBuiltins.lean` | `BuiltinFragment` and progress of the nine implemented builtins on scalar and literal arguments (`checked_builtin`). |
| `Source/Progress/EmitBuiltins.lean`, `Source/Progress/BuiltinStatements.lean` | Progress of direct `emit` nodes and builtin expression statements. |
| `Source/Progress/BuiltinControls.lean`, `Source/Progress/ScalarBuiltinControls.lean`, `Source/Progress/LiteralBuiltinControls.lean` | Builtin and event executions, argument order, zero modulus, hashes, messages, refusals and `checked_event`/`checked_call_statement` adapters. |


## P8 admission helper checkpoint

| Module | Role |
|---|---|
| `Lowering/P8/FrozenInterface.lean` | Frozen P8a producer obligations (`FailureProjection`, `SourceRealization`, `Producer`); no inhabitant. |
| `Frontend/Admission/Profile.lean` | Exact classification of extracted uses; features and failures kept. |
| `Frontend/Admission/RootObservations.lean` | Typed traversal of local observation sites over supplied roots; no callee closure. |
| `Frontend/Admission/Controls.lean` | Root, refusal, combination and `NoFail` controls. |
| `Frontend/Admission/ProgramObservations.lean` | Container scan of a `Program` (`program_observation_iff`), modifier declarations and written base names. |
| `Frontend/Admission/ProgramObservationControls.lean` | Seven-site container and omission controls; function host and modifier declaration/carried frame parameter checks. |
| `Lowering/P8/CheckedSyntax.lean` | Byte/piece/layout parse certificates with settings and main; raw-input checks; units-only settings obstruction. |
| `Lowering/V07/Scalar.lean`, `Lowering/V07/DeclarationGraph.lean` | Integer value transport; `DeclarationGraph` between Source types and schemas. |
| `Lowering/P8/ScalarSchema.lean`, `Lowering/P8/ShapeSchema.lean`, `Lowering/P8/GraphSchema.lean` | Singleton struct schemas built from actual declaration fields. |
| `Lowering/P8/ScalarSchemaControls.lean`, `Lowering/P8/ShapeSchemaControls.lean`, `Lowering/P8/GraphSchemaControls.lean` | Schema positives and refusals. |
| `Lowering/P8/FieldAdmission.lean` | Field lookup and distinctness through `GraphFieldsRel`. |
| `Lowering/P8/DispatchCoverage.lean` | Finite dispatch-target check; selected-body observation coverage. |
| `Lowering/P8/DispatchCoverageControls.lean` | P9 function reuse, recursion, a real modifier, missing-target refusals. |
| `Lowering/P8/SourceResolutions.lean` | Per-unit `Source.Resolves'` packet checker (`check_iff`, `unique`); raw/parse composition. |
| `Lowering/P8/SourceResolutionControls.lean` | One- and two-unit chains, pragma coder, corruption and link refusals. |
| `Lowering/P8/SourceMetadata.lean` | All-unit strict/inheritance metadata and `UnitsOK` (`metadata_iff`). |
| `Lowering/P8/SourceMetadataControls.lean` | Composed positives; constant, import, duplicate and main refusals. |
| `Lowering/P8/SourceMetadataObligations.lean` | Checked valid-override, strict-before-refusal and missing-virtual refusal controls; `checked_controls`. |
| `Lowering/P8/SourceAllSettings.lean` | Component chain accepted under every admitted settings value (`input_settings`). |
| `Lowering/P8/ProducerAssembly.lean` | Conditional `assemble`, component pipeline closure and `checked_glue`; actual `AdmissionHalf` and concrete source Producer remain open. |
| `Lowering/P8/ResourceBoundary.lean` | `FailureResource`; unchanged Source language cannot carry failure choices. |
| `Source/FailureResources.lean` | G06 failure-point bound algebra; `no_horizon_retraction`; not wired into execution. |
| `Lowering/P8b/Frozen.lean`, `Lowering/P8b/P8aInterface.lean` | Frozen P8b consumer signatures over G01 `Lowering` and P8a `Producer`; no inhabitant. |
| `Lowering/P8b/Domain.lean` | Structural pass/dom/agrees for a given emitter; `assemble`; wrong-emitter refutation. |
| `Lowering/P8b/Controls.lean` | Toy identity certificate, wrong-emitter refusal, loop divergence. |
| `Lowering/P8/ResourceContractLaw1.lean` | `nat_encodable_resource_impossible`: the frozen V1 failure projection has no inhabitant over a `Nat`-encodable resource (P8-SPEC-LAW1). |
| `Lowering/P8/FailureContractV2.lean` | V2 rebundling: `Projection` and `FullPlanCoverage` separated, `toV1`/`ofV1` roundtrips; still uninhabited over `Nat`. |
| `Frontend/Admission/SyntaxOccurrences.lean`, `SyntaxOccurrenceLaws.lean`, `SyntaxOccurrenceControls.lean` | Typed syntax subtree inventory, `syntaxOccurrences_iff` against `Source.Syn.Sub`, order/multiplicity controls; not semantic-root extraction. |
| `Frontend/Admission/ProgramRoots.lean`, `ProgramRootControls.lean` | Typed carried-field inventory and exact observation flattening; independent finite-roster lookup relation and refusal controls. |
| `Frontend/Admission/NameResolutionRoots.lean`, `NameResolutionControls.lean` | Initial target registration from actual source lookup/Resolves/function selection, with local-shadowing and refusal controls; not full runtime-root closure. |
| `Frontend/Admission/ModifierRoots.lean`, `ModifierRootControls.lean` | Initial modifier selection registration through actual typed paths and parameter forms, with qualified/wrong-kind/deep-path controls; not runtime closure. |
| `Frontend/Admission/TypedObservationPolicy.lean` | Local observation allowance from actual typing; whole expression, arguments, conversion, lvalue, statement and Program closure are proved in the typed policy modules. |
| `Frontend/Admission/TypedExpressionPolicy.lean` | General intrinsic expression visitor and container policy closure via mutual constructor induction. |
| `Frontend/Admission/TypedStatementPolicy.lean` | Unconditional statement/item and carried-Program observation closure; actual container proofs discharge retained builder interfaces. |
| `Lowering/P8/SourcePrograms.lean`, `SourceProgramControls.lean` | Checked original-byte frontend stages to actual all-unit Source elaboration and failure propagation; nonempty contract component proofs are in the acceptance modules. |
| `Lowering/P8/SourceProgramAcceptance.lean`, `SourceProgramAcceptanceControls.lean` | Exact actual elaborator success-bit laws and the full original kernel contract-control conjunction; ordered expectations unchanged. |
| `Lowering/P8/EntryRoots.lean`, `EntryRootControls.lean` | Actual function/receive/fallback selector registration and supplied-Program controls; selected and special-entry root coverage, not executed-entry or full admission adequacy. |
| `Lowering/P8/SourceObservationAdmission.lean`, `SourceObservationControls.lean` | All-output actual source elaboration followed by an observation guard proved redundant (`accept_eq_upstream`); composed independent ProgramSite soundness, not full feature/profile adequacy. |
| `Lowering/P8/DeclarationGraphAdmission.lean` | Bounded memory-storage-copy checkpoint; scope and retained premises are stated in the module. |
| `Lowering/P8/DeclarationGraphCheck.lean` | Bounded memory-storage-copy checkpoint; scope and retained premises are stated in the module. |
| `Lowering/P8/DeclarationGraphControls.lean` | Bounded memory-storage-copy checkpoint; scope and retained premises are stated in the module. |
| `Backend/FunctionValues/RuntimeConstruction.lean` | Bounded memory-reference-structs checkpoint; scope and retained premises are stated in the module. |
| `Backend/FailurePaths/TransientCallback.lean` | Bounded memory-internal-calls checkpoint; scope and retained premises are stated in the module. |
| `Backend/FailurePaths/TransientSharing.lean` | Bounded memory-internal-calls checkpoint; scope and retained premises are stated in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/NegationBody.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/NegationBodyControls.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/NegationSourceConsumer.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/NegationSourceControls.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained premises are in the module. |
| `Backend/Executable/ConstructorArgumentObservations.lean` | Bounded v14-payments-bytecode checkpoint; typed scope and retained premises are in the module. |
| `Backend/Executable/ConstructorLocalArguments.lean` | Bounded v14-payments-bytecode checkpoint; typed scope and retained premises are in the module. |
| `Backend/StructuredFlow/MappedCondition.lean` | Bounded v17-validation-release checkpoint; typed scope and retained premises are in the module. |
| `Backend/StructuredFlow/MappedConditionControls.lean` | Bounded v17-validation-release checkpoint; typed scope and retained premises are in the module. |
| `Lowering/G19/AssignmentReturnFlag.lean` | Bounded v17-validation-release checkpoint; typed scope and retained premises are in the module. |
| `Lowering/V08/SourceMemoryKeccak.lean` | Bounded v08-world-lowering checkpoint; typed scope and retained premises are in the module. |
| `Calculus/StaticInvocation.lean` | Bounded readonly-external checkpoint; typed scope and retained premises are in the module. |
| `Semantics/StaticInvocation.lean` | Bounded readonly-external checkpoint; typed scope and retained premises are in the module. |
| `Lowering/V08/LiteralFailureDynamicReturn.lean` | Bounded v13-abi-world checkpoint; typed scope and retained premises are in the module. |
| `Lowering/V08/LiteralFailureDynamicReturnControls.lean` | Bounded v13-abi-world checkpoint; typed scope and retained premises are in the module. |
| `Lowering/V08/LiteralFailureReturnSlots.lean` | Bounded v13-abi-world checkpoint; typed scope and retained premises are in the module. |
| `Lowering/V08/LiteralFailureReturnSlotsControls.lean` | Bounded v13-abi-world checkpoint; typed scope and retained premises are in the module. |
| `Lowering/V08/LiteralFailureTupleAbort.lean` | Bounded v13-abi-world checkpoint; typed scope and retained premises are in the module. |
| `Lowering/V08/LiteralFailureTupleAbortControls.lean` | Bounded v13-abi-world checkpoint; typed scope and retained premises are in the module. |
| `Roadmap/V16/H24Input.lean` | Explicit V16 input boundary for the published H24 companion; no admission inhabitant. |
| `Backend/Executable/CreationPatchOrder.lean` | Bounded v14-payments-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/Executable/CreationPatchOrderControls.lean` | Bounded v14-payments-bytecode checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/G19/WhileReturn.lean` | Bounded v17-validation-release checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/G19/WhileReturnControls.lean` | Bounded v17-validation-release checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V08/ConditionalCallable.lean` | Bounded v08-world-lowering checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/FailurePaths/ReasonCodec.lean` | Bounded memory-internal-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/FailurePaths/ReasonCodecControls.lean` | Bounded memory-internal-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedBackedgePush.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/RoadmapV15/P10/LinkedBackedgePushControls.lean` | Bounded v15-evm-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/InternalFlow/RuntimeFrameV3MutatingActivation.lean` | Bounded v12-flow-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Backend/InternalFlow/RuntimeFrameV3NativeUnwind.lean` | Bounded v12-flow-calls checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V08/LiteralFailureMemoryReason.lean` | Bounded v13-abi-world checkpoint; typed scope and retained obligations are stated in the module. |
| `Lowering/V08/LiteralFailureMemoryReasonControls.lean` | Bounded v13-abi-world checkpoint; typed scope and retained obligations are stated in the module. |

See [P8 admission](../feature-work/p8-admission.md).

