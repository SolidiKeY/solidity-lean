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
  checkpoint (not shown to undo mutations). `success_history` uses
  `EnvironmentHistory.loop` with `CallbackHistories` as a premise.
  `invocation_success` gives `RawAt` and `RuntimeFrames` together, only for a
  successful, zero-value, static, unknown-receiver call.

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

- `Step`/`Observed` producers tied to the source state, and P2 histories for
  reverting, value-bearing and reentrant calls.
- A P10 `Returndata` adapter from
  `Bridge/SolidityBridge/RoadmapV15/P10/FrozenInterface.lean` (reference EVM,
  7-argument CALL) to `FetchedPremises`; see [P10](roadmap-v15-p10.md).
- V3 producers ([p1-call-producer.md](p1-call-producer.md)) at world call sites,
  an admission-preserving return witness, and proof that the intrinsic call
  represents the source invocation (self-call ABI, dispatch, G37 frame).
- Native and compiler adequacy.
