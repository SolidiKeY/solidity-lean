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
