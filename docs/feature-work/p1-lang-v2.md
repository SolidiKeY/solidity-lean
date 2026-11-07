# Canonical P1 languages, version 2 (H115 item 3)

Lane `core-p1` (batch p1core-20261107). The versioned pair of V12's coarse
`RuntimeFrame.P1Lang` (branch `cloud/move5-20261106/v12-p1`), built on the
version-2 EVM machine of [evm-machine-v2.md](evm-machine-v2.md). All modules
are in `Solidity/Backend/InternalFlow/`.

## Languages (`RuntimeFrameP1LangV2`)

| Declaration | Meaning |
|---|---|
| `Input C Γ` | `L frame caller base machine start`, with `machine : MachineV2`. |
| `Admission C Γ` | A predicate over `Input C Γ`. |
| `sourcePrefix` | Source `Stmt.run` observation: `ok` → `success []`; `revertWith d` → `revert d`; bare `revert` → `revert []`; code-less `panic` (failing `assert`) → `revert (encodePanic 1)`, solc's `Panic(0x01)` and the source's own reading (`TRun.catchBytes`, `selfPanicCode` default); `exhausted`/`diverge` unfinished; no events. |
| `targetPrefix self k` | Version-2 run observation: calls journaled after the first `k`, except calls of `self` (internal to the system, per `Event`), become `Event.call callee value input false` + `Event.answer outcome none`; `ok _ 0` → `success []`, `ret _ d` → `success d`, `revert cs d` → `revert d` (events kept); pending jump / fault unfinished. |
| `SourceClass`, `sourceClass`, `TargetClass`, `targetClass` | Frame-boundary classes that `Outcome` merges (bare revert / panic / revert with data; stop / return; pending / fault). `sourcePrefix_final`, `targetPrefix_final`: the final outcome is a function of the class. |
| `sourceLang`, `targetLang`, `targetSem` | The canonical `Lang Event Outcome` pair; source resource is the depth `n`, target resource `Unit`; same environment, so `beta = id`. |

Source events are `[]` (`sourcePrefix_events`): the typed source run has no
journal of external calls. A successful source frame shows no data (its
typed results are not bytes), and outside self-calls the source keeps some
data-less reverts that solc gives data (`require(c, "m")`,
[solc-alignment.md](../solc-alignment.md)). So the source language is
canonical only for families without external calls or payments, without
return data, and whose reverts carry their data in the source. A target
fault carries no journal, so its events are dropped.

## Migration to V12's coarse languages (`RuntimeFrameP1LangV2Migration`)

V12's `P1Lang`, `P1Bridge` and the V4 family are merged into this branch
from `cloud/move5-20261106/v12-p1` unchanged. `coarse` forgets events and
data and keeps the final class; `source_coarse`: the V2 source observation
coarsens to V12's; `target_coarse`: the V2 target observation of any outcome
coarsens to V12's observation of its frozen projection `OutV2.forget`;
`lift_coarse`/`lift_coarse_ofV1`: lifted frozen code observed on a V12 input
(`Input.ofV1`) coarsens to V12's target observation; `coarse_forgets_data`
is the loss.

## Bridge (`RuntimeFrameP1BridgeV2`)

Family: frame `Γ = [bool]`, `guard C = if (ok) {} else { revert(data) }`
with `data = [0x08, 0xc3, 0x79, 0xa0]`, constant in the depth. Image
`image cell`: `MLOAD cell; JUMPI +5; PUSH dataWord; MSTORE cell; PUSH 4;
PUSH cell; REVERT` (hand-written, not compiler output). Domain `admitted C
cell`: `cell < W` and the cell represents the flag (`ReprV .bool`).

- `source_true`/`source_false`, `target_true`/`target_false`: actual runs on
  every admitted input; `agree`: equal prefixes.
- `pass`: the full `PassCorrect` between `Behaviour.ofLang` of both
  languages (`envAbs = id`, `need = fun _ _ => ()`).
- `Local C cell`: for every admitted input, either the flag is true, the
  source class is `success` and the target stops with the journal unchanged,
  or the flag is false, the source class is `revertWith data` and the target
  is exactly `.revert e.machine.calls data`. `local_holds` proves it.
- `p1_frame_bridge C cell : BridgeGoal (A C cell) (B C cell) () () id
  (fun _ _ => ()) (Local C cell)`.

Controls (`RuntimeFrameP1BridgeV2Controls`), for every contract `C`:
`admitted_true`/`admitted_false` (both classes inhabited by admitted inputs,
cell 3), `revert_witness`, `success_witness`, `success_witness`, `not_bare` (the payload is
observed, not `revert []`), `source_distinguishes`, `refused_mismatch`,
`other_payload_disagrees` (an image with payload `0xdeadbeef` breaks the
agreement on an admitted input), `events_observed` (a journaled `CALLIN`
before a revert shows `call` and `answer` events), `offset_drops_old` (a
call journaled before the run is not an event), `self_call_internal` (a call
of the contract itself is no event), `panic_data`, `satisfiable`. The axioms
of `p1_frame_bridge` are pinned.

## Limits

- One fixed family with a hand-written image; no compiler emits version-2
  code, and the domain is a single-cell representation premise, not the full
  `StateRepr`/`InterfaceV3` admission. Approved-profile provenance is not
  addressed.
- The family makes no external call, so its events are `[]` on both sides;
  target events are exercised only by `events_observed`.
- The domain fixes one absolute cell per context; `L`, `frame`, `base` and
  `start` do not occur in it, and for `cell ≥ W` it is empty (the bridge is
  then vacuous; the controls use cell 3). The depth is unused, the success
  payload is `[]` and `need` is `()`, so the bound `nu` carries no content.
- The migration is at the observation level: no `Lang`, admission or
  `BridgeGoal` is migrated, and this family's image (it uses `REVERT` with
  data) is not lifted frozen code.
- The environment `Input` is the P1 one, so the bridge folds only as a
  singleton (as V12's).

## Reviews (item 3)

Read-only finder and skeptic reviews (no Lean server). Confirmed: no frozen
statement changed by the V12 merge or this commit; the admission is a
representation premise, not the conclusion; `agree` is exact equality and
the outcome and payload vary over admitted inputs. Fixed findings: a source
`panic` was observed as a bare revert, against solc and the source's own
`catchBytes` → `revert (encodePanic 1)` (`panic_data`); calls of the contract
itself were events → filtered by `self` (`self_call_internal`); the journal
offset was untested → `offset_drops_old`; the bridge docstring claimed
inhabitation inside `Local` → corrected; dropped fault events, absolute
cell, vacuous `cell ≥ W`, trivial resources, return-data exclusion and
observation-level migration → listed under Limits.
