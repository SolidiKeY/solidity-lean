# G42: compiler-side world-call consumers

Owning modules: `Backend/WorldCalls/` (lane compiler10/readonly-external). Every
consumer is a projection of producer-chosen typed inputs: P1 runtime frames
(`Backend/InternalFlow/RuntimeFrameInterfaceV3.lean`), P2 `StaticJournal.History`,
P3 `InvocationFrame.Invocation.RawAt`, P10 fetched CALL/RETURNDATA. No world CALL
is implemented; the core `Evm.Machine` CALL only pays (no calldata, no recipient
code). Source side: [G22](g22-readonly-calls.md).

## Interfaces (`Backend/WorldCalls/Premises.lean`)

- `Identity`/`identity i`: profile, declaration, types, receiver, sender, value,
  input, mode, depth + 1 and horizon of an `Invocation`.
- `Code` (push/body/pop). `ReturnedFrame`: a control-only view trace with actual
  push/body/pop runs, not the P1 physical-frame contract.
- `Premises i`: producer-chosen `Step`/`Observed` with fields `bound`,
  `execution` (actual `Evm.run code.full`), `observed`, `sourceRaw : i.RawAt`
  and `p2History`. `Step` is not tied to the source state, so `Step := False`
  inhabits the structure vacuously.
- `FetchedCall` is an actually reached CALL (pc, prefix run,
  `Evm.Instr.step .call`). `FetchedPremises` is the P10 input. Its `Returndata`
  is an unconstrained `Prop` and is never inhabited here.

## Consumers

- `Callbacks`: `returned`, `deterministic`, `target_unique` (the returned
  machine is unique for the emitted code), `suffix` (a continuation keeps its
  writes and halts), `restore` (view equality from `ReturnedFrame`),
  `restoration`. `static_storage` is P2 typed storage via
  `InvocationFrame.typed_storage`; it needs `i.mode = true` and entry/exit
  representation proofs. `source_environment` is `EnvironmentHistory.loop`
  under explicit `CallbackHistories`. `compiled_return`: a V3
  `PendingCallProducer`, an `Entry`, the intrinsic `Stmt.call` run and
  `p.code.full = producer.plan.code` give the frozen `Returned`, the target run
  and `RawAt`. It does not prove the intrinsic call represents the source
  invocation.
- `ExternalCalls` (given `FetchedPremises`): `fetched`, `call_halt`, `decoded`,
  `target_return`, `continuation`; `declared_return`: the full `extCall` equals
  `extReturn` on the outcome at post-argument locals and callee final state.
- `SelfCalls`: `SelfPremises` adds receiver = self and the actual code lookup to
  `Premises`. Also `calleeFrame`, `self_identity`, `sender_and_mode`,
  `returned_execution`, `payment_self_zero`, `callee_exhaustion`.
  `callee_body` is `callInternal` at the child frame (via
  `SourceCallable.complete`), the internal path, not the
  `callAddr`/`enterInstance`/`dispatch` path of an external self-call.
  `SelfPremises` is never inhabited.
- `P1Consumers` takes V3 `Pending*` structures as parameters and builds no
  instance. Projections: `ordinary_return`, `fixed_return`, `recursive_return`,
  the `*_bare_revert` claims, `recursive_code`, `recursive_coherence`, the
  `*_successful_entry` witnesses, `bare_reverting_entry`.
  `ordinary_return_witness`: a successful entry plus `required_return` at the
  same caller gives a full `Returned`; admission is dropped from the
  conclusion, so it is not an admitted-return witness. `rejects_exhausted`: a
  statement that always exhausts has no `SuccessfulEntry`. Recursive success
  holds at some index, not necessarily the recursion depth.

### V1 entry quarantine

`InterfaceV1.RealizableEntry` only says that some `Entry` exists; it does not
make `ReturnClaim` non-vacuous (budgets may admit only failing callers). No module
here uses V1 `required_entry` or a V1 call producer: entry evidence is V3
`SuccessfulEntry` (tied to a successful run) or `RevertingEntry`. V1 `Entry`,
`Returned` and `ReturnClaim` remain relations; V1 `PendingRestoration` is still
the input of `restoration`.

## P3 bridge and unknown calls

- `SourceBridge`: `point`/`request` come from the post-argument state, receiver,
  value, input, frame, horizon and requested mode. `raw_iff`: `RawAt` iff the
  `SourceCallPhase.raw` run, for every outcome and halt; `evaluated`,
  `evaluated_raw`, `evaluated_phase` give the actual deterministic result.
  `premises` takes `sourceRaw` from a supplied per-`Step` raw-phase equation
  (P2 history still supplied); also `captured`, `static_storage`.
- `UnknownSourceCall`: `transport` is the exact `callAddr` equation for a
  zero-value unknown receiver below the depth limit. Halts stay halts, success
  keeps its state, and a revert keeps its bytes and runs `rollbackTo` the live
  checkpoint. `success_history` uses
  `EnvironmentHistory.loop` with `CallbackHistories` as a premise.
  `invocation_success` gives `RawAt` and `RuntimeFrames` together, only for a
  successful, zero-value, static, unknown-receiver call. `history` also covers
  revert and every halt, using actual journal ancestry to rewind a completed
  revert. `evaluated_frame` gives the actual computed `RawAt` and static frame
  for all outcomes, with zero value, depth, unknown-instance and bounded Source
  callback-history premises retained. No desired endpoint frame is assumed.

## Controls

- `PaymentControl.premises` is one paired fixture: a source `origin` (unknown
  receiver, empty answer, mode false, `p2History := .start`) plus the payment
  CALL between marker push/pop (`inhabited`, `restored`, `spoofed_mode_refused`,
  `unrelated_raw_refused`). `fetched_call` is a reached CALL, not a full
  `FetchedPremises`.
- `SourceBridgeControls`: `R.nonself_raw`, `wrong_bytes_refused`, `reentry_raw`,
  `reentry_frame`. `P.boundary` is the same payment fixture through
  `SourceBridge.premises`; `P.consumer` uses it.
- `ExternalControls`: `reached_call`, `canonical_uint`, `malformed_one_byte`.
  `SelfControls`: `ordinary_self_mutation`, `inherited_static_write_refused`,
  `unknown_receiver_not_self`. `UnknownSourceControls`: `joint`, `reentry`,
  `false_bytes`, `value_refusal`, `environment_timeout`, and `raw_revert`
  (no writes happen before the revert).
- These two are the only `Premises` instances; `Callbacks.static_storage` and
  `compiled_return` are never applied.

## Open

- `Step`/`Observed` producers tied to the source state, including actual target execution and source/target correspondence.
  Source P2 histories are closed by SourceAllHistories; target correspondence is not.
- A P10 `Returndata` adapter from
  `Bridge/SolidityBridge/RoadmapV15/P10/FrozenInterface.lean` (reference EVM,
  7-argument CALL) to `FetchedPremises`; see [P10](roadmap-v15-p10.md).
- V3 producers ([p1-call-producer.md](p1-call-producer.md)) at world call sites,
  an admission-preserving return witness, and proof that the intrinsic call
  represents the source invocation (self-call ABI, dispatch, G37 frame).
- Native and compiler adequacy.

Pending-producer-consuming wrappers expose a separate external `hprof`
(`AdmissionAgreement`, or family agreement for recursion). No identity-domain
proof is substituted. Source `CallbackHistories` is an O1 Source obligation,
distinct from P1 runtime frames; see [Source histories](g22-source-history-producer.md).

`UnknownRevertControls` exercises an actual credit followed by ordered revert
bytes, retaining a supplied prior caller write, undoing the credit balance and
keeping its observable event. Its nil arguments do not execute the prior write.
The concrete strategy's callback-history premise is proved from its moves, not
from mutability metadata. General bounded Source callback histories are now proved by
SourceAllHistories; Source/target adequacy remains open.

Actual Source histories in SourceCallHistory now cover guarded known-instance
calls and unknown zero-value calls from smaller-bound SourceHistory.At, across
success, revert and halt. Static projection preserves typed storage, not balances
or the whole world. The27 controls and exact Source equalities do not discharge
compiler target steps, frontend capture provenance or Source-to-Core representation.

ClosedSourceFrame.history_of_raw derives P2 directly from the exact invocation's
Source RawAt run, for arbitrary values, outcomes and halts. frames_of_raw,
evaluated_frame and caller_storage remove the independent Source-history
premise for static invocations while retaining local capture and post-capture
state. This does not supply original-site provenance, Source/Core representation
or a target/native execution producer. No checked-emitter ReturnClaim or external
function-value producer is implemented here; those remain separate consumers.

ClosedSourceConsumers.premises is the closed-P2 adapter: it accepts the existing
same-invocation raw-phase, identity, target execution and observation inputs,
then derives p2History from the proved Source run instead of asking for a
separate history. Empty Step remains possible and is not promoted to target
coverage. typed_storage retains the explicit functional representation and
both endpoint representation facts; source_environment has no callback-history
premise. No original-site provenance or target call implementation is supplied.

ClosedConsumerControls applies this adapter to the inhabited restricted payment
fixture, rejects unrelated bytes, exercises actual read-only Source reentry,
and proves any explicitly represented typed output equals the entry projection.
The final touched controls and nine-declaration standard-axiom audit passed
in15.08s, peak aggregate186613760 bytes, hard12GiB/swap0, CPU1/Lean-j1,
unchanged300s deadline and4GiB host reserve. Independent finder and skeptic
found no defect; no original full or native gate was retried or relabeled.

SourceExpressionConsumer.after_capture connects the actual resolved extCall
expression at horizon+1 to its capture execution and remaining resume run.
resume_history includes real callAddr plus the declared-return decoder, without
assuming callee success or successful decoding. expression_history and storage
protect persistent caller storage relative to the post-capture checkpoint when
the declaration-requested or inherited mode is static. Argument effects before
that checkpoint are retained. This proves the local resolved-expression link,
not whole-body/original-source-site embedding or compiler/Core correspondence.

SourceExpressionControls has13 kernel assertions: an ordinary nonself call's
argument3→4 and old3 calldata, declared int failure on one-byte successful
callee data, and actual inherited-static read-only reentry through the expression.
The argument-effect fixture is ordinary; it does not independently witness a
combined view-call/postincrement fixture. The generic law retains the actual
Invocation declaration/signature/capture and effective mode. No new source,
fixture, admission, expected observation, native observation or target behavior
is introduced. Per-file controls passed in7.45s;17-declaration axiom audit passed
in10.27s, peak184778752 bytes, only standard axioms. Both used unchanged hard12GiB/
swap0 CPU1/Lean-j1/300s limits and4GiB host reserve. The initial ambiguous caller
context check failed; explicitly indexing the existing caller context fixed it.
Independent finder and skeptic cleared the statements and boundary.

SourceExpressionIssuer.capture_of_success derives actual CapturedAt and resumed
execution from a successful resolved extCall expression; it no longer asks for
a separately supplied capture witness at that boundary. bind retains exact
environment declaration membership, typed signature, expressions, horizon,
states and captured values. storage_of_success uses that derived checkpoint
and the closed Source law to preserve static caller storage without a frame
premise. It covers successful expressions only; earlier all-outcome Source laws
remain unchanged. This is not whole-body/source-text provenance, nor proof that
unknown receiver bytecode implements the selected declaration.

SourceIssuerControls includes inhabited argument-effect and inherited-static
reentry issuance, a view-labelled declaration rejected by actual registration,
and missing-code refusal before capture can succeed. Ten declaration/definition
axiom reports passed with only standard axioms; final controls/audit took5.73s,
peak210087936 bytes under unchanged hard12GiB/swap0 CPU1/Lean-j1/300s limits
and4GiB host reserve. Independent finder and skeptic cleared final proofs.
Initial contradiction/type/lookup-normalization attempts remain failed receipts.
No original full or native gate was repeated or relabeled.

SourceExpressionFailure.classify separates an actual failing resolved external
expression into an exact capture failure or an actual successful capture followed
by resume failure. capture_failure propagates the former's halt and reached state
unchanged. storage retains that alternative and proves static storage preservation
only from a successful post-argument capture checkpoint in the latter. This does
not freeze argument evaluation, turn capture errors into callee reverts, or assume
successful decoding. Earlier success/all-outcome Source laws are unchanged.

SourceFailureControls adds eight kernel assertions: missing-code failure after
postincrement keeps3→4 and emits no call event; malformed successful return data
fails after a successful capture; a real static callee revert retains ordered
bytes7,9 and protects caller storage. These are expression-level Source facts,
not transaction rollback or target/native observations. Controls passed in2.92s;
the15-declaration/definition standard-axiom audit passed in4.72s, peak189632512
bytes, under unchanged hard12GiB/swap0 CPU1/Lean-j1/300s limits and4GiB reserve.
Independent finder/skeptic review found no defect. Two initial typed error-carrier/
dependent-elimination proof failures remain failed receipts. Whole-body/source-text,
Source/Core and target/native correspondence and original final gates remain open.

SourceSelfDispatch now follows the actual external-self Source path rather than
substituting callInternal. funded_self retains the live balance check without
transfer/credit. enter equates guarded callAddr to enterInstance at the live
checkpoint, using actual self-code lookup, depth, static-value and funding
premises. success/reverted/halted transport the actual smaller-bound dispatch:
success restores caller heap, revert rolls back the live child checkpoint and
retains raw bytes, and non-revert halt keeps reached state while restoring heap.
Arbitrary admitted values remain guarded; no payment or halt policy changes.

SourceSelfDispatchControls has nine assertions, including applications of all
three dispatch outcome laws to real Source runs, ordinary mutation, static
refusal/storage preservation, timeout, insufficient value and depth refusal.
The corrected controls passed in7.63s;19-declaration/definition standard-axiom
audit passed in3.73s, peak169558016 bytes, hard12GiB/swap0 CPU1/Lean-j1/300s
and4GiB reserve. Independent finder and skeptic cleared final proofs.
The initial control used core Heap.empty instead of Source.Heap.empty and hit
unchanged200000-heartbeat isDefEq failures after that type error; the failed
attempt remains failed. Explicit Source heap typing fixed the input, without
raising budgets. This supplies no target self-call/ABI-frame instance, native
adequacy, whole-body binding or unknown-receiver-to-self substitution.
