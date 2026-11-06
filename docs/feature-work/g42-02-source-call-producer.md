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

`Step` is defined as the graph of (`raw i`, `final i`, the actual target run),
so the five `Premises` duties hold by construction; their content is the
reused `rawAt` and `history`, plus `step_total` (non-vacuity on every machine).
`Observed` adds nothing beyond `Step`: the fetched CALL exists on every machine.
The target returns `.ok` whatever `raw i` is (revert, timeout or success): the
source outcome is not related to the target run.

`ReturndataDuty i` is a placeholder for V15's CALL/RETURNDATA correspondence.
Its relation is chosen by the supplier and unconstrained, inherited from
`FetchedPremises.Returndata` (`Premises.lean`, outside this lane's write
scope), so the trivial relation meets it (`Controls.trivial_duty`), and
`fetchedPremises` then carries no RETURNDATA content. It gains content only
once the interface pins the relation to a validated correspondence; that
interface change is V15's / the interface owner's. Nothing here is fabricated
from payment status or decoder success.

## Controls

`SourceCallProducerControls` instantiates the producer on the actual payment
invocation `WorldCalls.PaymentControl.origin`: the produced raw outcome and
final state equal the independently computed control (`produced_raw`), the
step is inhabited on the control machine, the CALL is reached, and the frame
is restored. `produced_raw` is the substantive control: it cross-checks the
produced outcome against an independently computed one. The negative controls
(spoofed static identity, unrelated raw outcome, unrelated target `.revert`)
only re-read `Step`'s own conjuncts and the determinism of `Evm.run`.
`trivial_duty` is a disclosure that `ReturndataDuty` is trivially met.

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

## Reviews (2026-11-06)

Read-only finder and skeptic reviews, neither using the Lean server, covered
this producer and the H69 V2 interface. They confirmed that V1 is frozen, that
the V2 partition and joint-satisfiability witnesses are about the right
hypotheses, and that there is no `sorry`, axiom, heartbeat or layering change.
Confirmed findings and their fixes:

- `ReturndataDuty` is trivially satisfiable (inherited from
  `FetchedPremises.Returndata`). This is now disclosed (`trivial_duty`), and
  the docs call it a placeholder rather than V15's correspondence.
- `Step` is the graph of the produced outcome and the target run, `Observed`
  is content-free and the negative controls only re-read `Step`. All three
  are now stated above.
- 25 bare `#print axioms` in `SourceDispatchInterfaceV2Controls` were pinned
  with `#guard_msgs` and recorded.
- The V2 module-map rows moved from the language-area fragment to this lane's
  `readonly-calls.d/ro-v2.md`.
