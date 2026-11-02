# V15 P10: fetched-byte execution steps against EvmYul

Partial checkpoint of roadmap item V15 (EVM agreement), producer P10: single
fetched EVM steps over Backend-emitted code, checked against the pinned
EvmYul reference (`Bridge/vendor/EvmYul`). All modules live in
`Bridge/SolidityBridge/RoadmapV15/P10/`; nothing in the core changed. Every
theorem is proved; there is no `sorry`, no new axiom, and the printed axiom
sets are subsets of `propext`, `Classical.choice`, `Quot.sound`.

## Sites

`Site op` (`Interface.lean`) packages a seed `EVM.State`, a Backend program
prefix and suffix, and a bound that the prefix length fits a word. `Site.state`
overwrites the seed's code with `Backend.encode (before ++ op :: after)` and
its PC with the prefix length. So a `Site` is a state built to hold `op` at
the PC; it is not a reachable state of a compiled contract. Applying a site
fact to a given state needs `Site.recover` (`RoadmapV15/P10/Execution.lean`), i.e. literal
equality of that state's code with an encoded Backend program. That equality
is the compiler/source-origin fact P10 does not supply.

## Frozen interface (consumers V13, V14, V16, VY3, VY4)

`FrozenInterface.lean`, namespace `SolidityBridge.RoadmapV15.P10.FrozenV1`,
fixes 18 statements in three `Prop` structures, for CALL, RETURNDATASIZE,
RETURNDATACOPY, JUMP, JUMPI and JUMPDEST sites:

| Structure | Fields | Content |
|---|---|---|
| `Decode` | 6 | `EVM.decode` at the site PC returns the opcode with no immediate. |
| `ChargedStep` | 6 | `Assembly.driverSteps 1` equals the opcode's dispatch after `Assembly.driverGate`: CALL through `EVM.call` (unevaluated), return-data size/copy, jump targets and fall-through. |
| `Continuation` | 6 | `EVM.X (fuel+2)` is one driver step followed by `EVM.X (fuel+1)`. |

`API` bundles the three. `FrozenWitness.lean` proves `FrozenV1.api : API`
from the theorems of `Interface.lean` and `RoadmapV15/P10/Execution.lean`; it adds no new
fact, so a hypothesis `(h : API)` is always dischargeable and is not evidence
beyond those theorems. The decode fields are byte-table lookups (also covered
by `DecoderAgreement.decode_all`); the step and continuation fields are
unfoldings of `EVM.step` and `EVM.X`, with `driverGate` left folded and the
`EVM.call` result not evaluated. The signatures are frozen as version 1;
changes go to a new version.

## Consumer laws

Each consumer pairs a typed scalar or Backend reading with the fetched,
charged step and its `X` continuation, with explicit gas and stack bounds.
Each has a controls module (`…Controls.lean`) with populated states, boundary
and error-order negatives.

| Modules | Opcodes | Content |
|---|---|---|
| `Execution`, `ExecutionControls` | CALL, RETURNDATASIZE/COPY, JUMP/JUMPI/JUMPDEST | Charged steps and continuations above; funded, underfunded and static CALL controls. |
| `Modular`, `ModularControls` | ADDMOD, MULMOD | Full-precision scalar agreement. |
| `ExponentConsumer`, `PowerControls` | EXP | Reference modular power; local gas bound 1610. |
| `StackFamilyConsumer`, `StackFamilyControls` | DUP1–16, SWAP1–16 | Every legal depth. |
| `SignedDivisionConsumer`, `SignedDivisionControls` | SDIV, SMOD | Bounded signed transport; raw zero and minimum-wrap behaviour kept as EVM semantics. |
| `ArithmeticShiftConsumer`, `ArithmeticShiftControls` | SAR | `BitVec` agreement including saturation. |
| `StorageReadConsumer`, `StorageReadControls` | SLOAD, TLOAD | SLOAD 100 warm / 2100 cold, TLOAD 100; existing typed slot observations. |
| `BalanceEnvironmentConsumer`, `BalanceEnvironmentControls` | BALANCE | Charged read; the frame's `funds` field is defined from the EVM account map, so the funds agreement holds by construction. |
| `DecoderAgreement`, `DecoderAgreementControls` | 117 non-immediate opcodes | Backend bytes against the reference decoder and fetched dispatch. |
| `PushDecoderAgreement`, `PushDecoderControls` | PUSH0–32 | Payload extraction against the reference reader. |
| `ReturnCopyBounds`, `ReturnCopyBoundsControls` | RETURNDATACOPY | The order of the gas, arity, natural source-endpoint and capacity checks. The charged state changes only gas. The gate classification unfolds `driverGate` directly. The out-of-range refusal (`InvalidMemoryAccess`) is lifted to `driverSteps` and `EVM.X` through `FrozenV1.api`. The physical copy, padding and read values are not proved, and errors carry no final state. |

## Known differences and open items

- The pinned EvmYul has no CLZ: byte `0x1e` decodes to INVALID
  (`clz_invalid`). This is recorded, not excluded or approved.
- The reference accepts the truncated raw PUSH2 `[0x61, 0x01]` (value 1),
  which `Backend.decode` refuses; the PUSH laws cover complete emitted payloads.
- `valid` (the jump-destination array) is an input, not a scanner certificate.
- RETURNDATACOPY uses the reference byte-memory operation; no physical
  padding (`PaddingCorrect`) witness is supplied.
- Open: compiler/source origin of sites, G45.03 execution meaning, Osaka
  agreement, resource abstraction, and source/ABI/world/account/transaction/
  trace closure; the full per-opcode rows remain open.

## Master integration review

Merged from producer head 515ac91d over master eba99fe7. Read-only finder and
skeptic reviews confirmed: no `sorry`/axiom/heartbeat changes, all imports and
module-map paths exist, core untouched. Fixed on merge: the producer's ten
per-step notes (VM paths, run logs, coordinator text) were replaced by this
page; the frozen-interface docstring now says its fields are discharged by
`FrozenV1.api` from existing theorems; `api` is a `theorem`; module-map rows
for `Site`, BALANCE and the frozen modules were made precise. Left out: the
producer's VM job-runner script, its test and its runtime-completion note. Noted, not changed: per-opcode `opcode_at`
lemmas are duplicated across modules, and most `#print axioms` are unguarded,
as elsewhere in `Bridge/`.
