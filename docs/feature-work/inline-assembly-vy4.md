# Inline assembly VY4: Yul world interface

`Yul/World/**`, from the vy4-world lane. It builds on master's Source world
(`Source/Observe`, `Source/World`) and backend byte constants.

- `Raw`: RETURNDATACOPY windows, call output prefix, CREATE/CREATE2 addresses
  (`overwrite` ignores its old argument, so `overwrite_last` is definitional).
- `Observations`: logs, observations and rollback of traces;
  `ObservationAgreement` has only the identity instance.
- `Frames`, `Adapters`, `ByteMemory`: frame completion, `callAdapter`,
  `logAdapter`, `copyReturndata`, a `BytePort` over backend memory.
  `WorldPort`/`FrameAnswer` are interfaces: on success they accept arbitrary
  operations (including caller-storage writes under STATICCALL); the only
  producer here is a scripted one in the checks.
- `AdapterRules`, `ReturnSize`, `CreationFrames`, `CreationRules`,
  `CreationAddressing`: step rules; each takes the adapter equation that
  defines its `Step`, so they are determinism lemmas.
- `Lifecycle`, `LifecycleAdapter`: the EIP-6780 SELFDESTRUCT lifecycle.
- `*Checks`: controls.

Logs (G01): log entries are observations recorded with the frame and rolled
back with it.

Open: real port producers (physical completion, caller frames, effectful emit
rollback, static environment invocation), the P7 transient target (TLOAD/TSTORE
consumers), port laws for the step rules.

## Returndata bridge and target-call output (sched 2026-11-03)

- `SolidityBridge.YulWorld.Returndata` (Bridge) consumes the frozen P10 API and
  `ReturnCopyBounds`: successful gate/operand facts give the copy-source bounds,
  the `Raw.returnWindow` bytes and the charged native successor; rejected
  windows fail only after both gas checks. No byte readback, padding or
  source/compiler origin. `ReturndataControls` holds the populated controls.
- The six equation-premised port lemmas are renamed `copy_step_eq`,
  `call_step_eq`, `log_step_eq`, `size_step_eq`, `initcode_step_eq`,
  `addressed_step_eq` (statements unchanged): determinism from an adapter
  equation, not source reachability or Yul/G51 soundness. The in-module
  `#print axioms` lines were dropped.
- `TargetCallMemory.call_output_exact` / `call_output_readback` /
  `call_output_frame`: input loading plus a supplied producer invocation, the
  target output store, the copied prefix and every byte outside it, for success
  and revert. `TargetCallRules.call_output_box` derives the normal-return `Box`
  from preflight, output extent, input loading and the invocation equation (not
  from the desired `CallStep`). No control on master instantiates the
  `call_output_*` lemmas or `call_output_box` yet.

Open: actual callee/initcode execution, the full-slot carrier (needs
`OwnedBoolFrame` and its storage closure, not in the published Views), common
source emit/G01, compiler returndata noninterference, the scripted `WorldPort`
static-write weakness.

