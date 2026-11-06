# G42.02 reached-call/frame producer

`Backend/Passes/SourceCallProducer.lean` (namespace
`Solidity.Backend.Passes.SourceCallProducer`) instantiates the conditional
G42.02 interface `Backend/WorldCalls/Premises.lean` for **every** typed source
invocation `i : InvocationFrame.Invocation E Γ dn ps rs`.

## What is produced

| Piece | Declaration | Source of the proof |
| --- | --- | --- |
| P3 raw outcome | `raw i`, `final i`, `rawAt` | the actual `callAddr` run (`SourceBridge.evaluated_raw`) |
| P2 history | `history` | `ClosedSourceFrame.history_of_raw`, through the H69 V2 induction `SourceDispatchV2.all_at` |
| Emitted code | `code i` | `push receiver; push value; CALL` then `POP` |
| Reached CALL | `fetchedCall i m` | a `FetchedCall` for every initial machine `m` |
| Frame return | `restored`, `returns` | for every `m` the code returns with stack, storage, memory and `self` restored; only balances may move |
| `Premises i` | `premises i` | all five duties proved; `step_total` inhabits `Step` on every machine; `step_unique` pins identity, raw outcome and final state |
| `FetchedPremises i (premises i)` | `fetchedPremises i duty` | everything except `ReturndataDuty i` |

`ReturndataDuty i` is the single remaining premise: a relation between each
fetched CALL of this emission, its target run and the produced source outcome,
and its proof for every machine. It is V15's CALL/RETURNDATA correspondence.
It is not instantiated here, and nothing is fabricated from payment status or
decoder success (`ExternalControls` keeps that rule).

## Controls

`SourceCallProducerControls` instantiates the producer on the actual payment
invocation `WorldCalls.PaymentControl.origin`: the produced raw outcome and
final state equal the independently computed control (`produced_raw`), the
step is inhabited on the control machine, the CALL is reached, and the frame
is restored. Negative controls refuse a spoofed static identity, an unrelated
raw outcome and an unrelated target result (`.revert`).

## Limits

- The core `Evm.Instr.call` is payment-only: it takes value and receiver, not
  selector or argument bytes, and runs no callee code. So the emission does
  not transport `i.captured.input`, and returndata cannot be related to the
  source `Outcome` inside the core. That is the `ReturndataDuty` wait (V15).
- `Observed` is structural (identity, a fetched CALL, the actual run); it is
  not a returndata observation.
- The physical P1 frame contract (`InterfaceV3.Pending*`) is not instantiated.
  `restored` is the frame fact of this fixed emission only. V12's P1 closure
  (`cloud/move5-20261106/v12-p1`, general V3 boundary) had not landed on
  master on 2026-11-06; once it does, a consumer can pair `premises i` with
  its `Pending*` instances. Waiting on that lane.
- Whole-body embedding of the invocation, Source/Core representation and
  compiler adequacy remain separate obligations.
