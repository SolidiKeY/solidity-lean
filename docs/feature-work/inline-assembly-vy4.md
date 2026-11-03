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

## Native returndata bridge checkpoint

`SolidityBridge.YulWorld.Returndata` consumes the actual P10 frozen API and
`ReturnCopyBounds`. Successful native gate and operand facts yield natural
copy-source bounds, exact `Raw.returnWindow` bytes and the full charged native
successor. Complete native world, returndata and `H_return` are preserved;
memory equals the reference `ByteArray.write` expression. This does not prove
byte readback, untouched destination tails, padding or source/compiler origin.
Rejected windows produce native range exceptions only after the two actual gas
checks, preserving resource-error priority and strict zero-length bounds.

`ReturndataControls` contains populated persistent/transient accounts, code,
ordered logs, static copy, distinct buffers and exact-end/out-of-source zero
controls. Six headline proofs have standard-only axiom sets. Targeted joint
imports passed on master `27edf590`; this is optional Bridge evidence, not
source-world/Osaka/transaction/G01/calculus or final lane adequacy.

The published memory Views/Adapters and `FrameHeap` are now available. The
older private full-slot adapter additionally needs `OwnedBoolFrame` and its
represented-slot/encoding-journal dependencies, absent from this published
Views tree. Routine step projections/continuation are listed in TERRA-TODO.md.
The integrated preparation-rule determinism and scripted-port limitations
above remain open; no admission row is reopened.

## Equation-premised port lemmas

The six equation-premised lemmas are named `copy_step_eq`, `call_step_eq`,
`log_step_eq`, `size_step_eq`, `initcode_step_eq` and `addressed_step_eq`.
Their propositions and proof bodies are unchanged. They establish determinism
from an adapter equation, not source reachability or Yul/G51 calculus soundness.
The independent static-refusal laws retain their names.

Kernel audit commands live in `tests/yul-world/PortEquationAxioms.lean`, rather
than production imports. All 37 scoped axiom sets match the published baseline
after renaming; six are empty and the remainder use only standard axioms.
Fresh isolated per-file compilation checks the ten affected modules. Earlier
stale-cache successes did not certify the rename; the resulting unknown-name
audit failure is retained separately from the passing fresh audit.

Original Y07.01/Y07.02/Y09.03 and both backfill queues remain partial. Actual
callee/initcode execution, physical carrier closure, common source emit/G01,
compiler returndata noninterference, resources and final calculus/joint gates
remain open. The scripted WorldPort static-write weakness is unchanged.
