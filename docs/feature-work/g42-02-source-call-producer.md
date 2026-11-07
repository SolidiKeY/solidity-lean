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

## Version 2: on `Evm.MachineV2` (H106)

`Backend/Passes/SourceCallProducerV2.lean` addresses the two gaps above on the
versioned machine `Evm/MachineV2.lean` (master `d3597eca2`; H57 pair of the
frozen `Evm.Machine`, which stays unchanged). The frozen-machine producer
above stays as it is.

| Piece | Declaration |
| --- | --- |
| Input placement | `SourceCallBytes`: `chunks` pads the captured input to 32-byte cells, `stores` emits one `PUSH`/`MSTORE` per cell, `wordBytes_bytesWord` is the byte round trip and `readBytes_stores` reads exactly the input back from the window |
| Emission | `code i o`: the stores from cell `o`, then `CALLIN(value, receiver, o, length)`, then `POP` |
| Input transport | `callIn_input`: `CALLIN` runs `callInStep` on exactly `i.captured.input` |
| Every machine | `call_run`: returns with the caller's stack and storage. An entered call leaves `reply receiver value input` in the buffer and journals the captured input; an unentered one empties the buffer. |
| Pinned relation | `Returndata i m out result`: a fixed definition. When `result` has a payload `(ok, d)` and the oracles agree (`OracleAgrees`: `reply` answers `d`, `accepts` is `ok`, the value is funded), `out` is `.ok` with buffer `d`, the caller's stack, and the journal extended by `⟨receiver, value, input, ok, d⟩` |
| Proof | `returndata_holds`: the relation holds for every invocation and machine at `raw i`; `returndata_any`: it holds for every source result, since the payload hypothesis is not used in the proof |
| Joint satisfiability | `oracle_agrees`: every payload has agreeing oracles (the witness answers `d` only on the captured input and funds only the caller); `transported`: the conclusion is then reached |

What this proves: input transport plus `CALLIN`'s buffer law. `OracleAgrees`
names the source payload `d` and asks the reply oracle to answer `d`; it does
not refer to the source world's callee, so the buffer equality is
`callIn_returndata` plus that premise. Tying the oracle to the source world's
callee answer (so that `raw i` does work in the proof) is the remaining
G42.02 step and needs V15's callee model.

`Controls.wrong_buffer_refused` shows that the relation is not identically
true in the target outcome: under agreeing oracles it refutes a hand-built
outcome (not a run) with another buffer. `two_cells_read` checks, by kernel
computation on explicit cells, that a 40-byte input spans two cells and reads
back exactly. The other controls
use the payment invocation (`ping()`, value 0, source `success []`):
`transported_control`, `journaled_input` (the journal holds the `ping()`
selector bytes), `liar_disagrees` and `liar_observed` (an oracle answering
`[1]` is not agreeing, and its answer is what the buffer holds).

Limits (from `MachineV2` and this emission):
- The callee's code is not run. Its answer is the `reply`/`accepts` oracle,
  and the source link holds under `OracleAgrees`, an explicit premise.
  Relating the oracle to actual callee execution (V15) remains open.
- There is no gas and no call depth. Memory is word-addressed.
- Source halts (timeout, depth limit, static refusal) have no payload, so the
  relation says nothing about them.
- `small`: the input length is below `2^256`.
- The caller must be able to pay the value (`OracleAgrees.funded`). When it
  cannot, MachineV2 empties the buffer and journals nothing, and the relation
  says nothing.
- The `CALLIN` status word is popped. The success/revert flag reaches only the
  ghost journal (`accepts = ok`) and is not compared with a source flag on
  the stack.
- The stores overwrite memory cells `o … o + ⌈len/32⌉ - 1`. `call_run`
  restores stack and storage only, not memory.
- Controls cover a success payload, an empty reply and a one-cell input on
  the run. Revert payloads and multi-cell inputs are covered by the general
  theorems (and `two_cells_read` for the window).
- The emission is a `MachineV2` program (`List InstrV2`). It does not
  instantiate the frozen-machine `WorldCalls.Premises`. `callIn_forget`
  relates its `CALLIN` to the frozen `CALL`.
- P1 `InterfaceV3.Pending*` is still not instantiated.

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

### Reviews of version 2 (2026-11-07)

Read-only finder and skeptic reviews (no Lean server) confirmed the input
transport (`readBytes_stores`, `callIn_input`), the pins and the imports.
Confirmed findings, fixed here:

- The payload hypothesis was unused, and `OracleAgrees` restates the
  conclusion's buffer value. Disclosed with `returndata_any` and the "What
  this proves" paragraph; the wording "as the source world does" was removed.
- The oracle witness answered every input and funded every account. It now
  answers only the captured input and funds only the caller.
- `wrong_buffer_refused` refutes a hand-built outcome. Its wording is
  corrected.
- Undisclosed limits added: the unpaid case, the popped status word and
  memory clobbering. A multi-cell control (`two_cells_read`) was added.
