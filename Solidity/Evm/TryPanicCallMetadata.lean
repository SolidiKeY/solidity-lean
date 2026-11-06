import Solidity.Evm.TryPanicSourceControl

/-! H22 metadata on the actual intrinsic call consumed by the H8 caller.
No static restrictions are implemented: the current semantics ignores mode
and invocation. This module proves that fact rather than selecting a reply. -/
namespace Solidity.Evm.TryPanicCallMetadata
open TryPanicSourceControl TryPanicCarrier TryPanicProducer
variable {C : Contract}

def sourceCall (mode : CallMode) (invocation : InvocationId) : ExtCall C Caller :=
  { selfCall with mode := mode, invocation := invocation }

def caller (call : ExtCall C Caller) (body : Prog C Input Input) : Stmt C Caller Caller :=
  .tryCall call .nil reject reject (.some (.user "c")) panicBody reject args36 body true

theorem mode (m : CallMode) (i : InvocationId) :
    (sourceCall (C := C) m i).mode = m := rfl

theorem invocation (m : CallMode) (i : InvocationId) :
    (sourceCall (C := C) m i).invocation = i := rfl

/-- Metadata changes do not grant static behavior in the unchanged evaluator. -/
theorem source_runR (m : CallMode) (i : InvocationId) (body : Prog C Input Input) :
    (caller (sourceCall m i) body).runR = (TryPanicSourceControl.caller body).runR := rfl

/-- Opposite metadata still has the same oracle key, not an identity proof. -/
theorem key (σ : State C Caller) (m : CallMode) (i : InvocationId) :
    (sourceCall m i).keyT σ = selfCall.keyT σ :=
  ExtCall.keyT_mode_invocation σ selfCall m i

/-- H22 sites are recorded but do not yet distinguish oracle answers. -/
theorem key_same_at_distinct_sites (σ : State C Caller) :
    (sourceCall .static (.site 79)).keyT σ =
      (sourceCall .static (.site 80)).keyT σ := rfl

end Solidity.Evm.TryPanicCallMetadata
