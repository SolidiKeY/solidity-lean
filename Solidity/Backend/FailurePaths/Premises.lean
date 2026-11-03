import Solidity.Backend.FailurePaths.Interface
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV1
import Solidity.Backend.Transient.Frames
import Solidity.Backend.MemoryOps.PhysicalByteJournal

/-!
# Explicit G38 producer boundaries

These are signatures, not assumed instances. General ABI error encoding belongs
to G41 (v13-abi-world); internal frame transport belongs to v12-flow-calls;
resource/exhaustion classification belongs to VY5 H16; physical transient
rollback belongs to VY4 P7. The authorized P7 relay is consumed by
TransientUnwind for its supported empty-failure case; general payload transport
still requires a producer. Unavailable ABI and frame implementations are not imported.
-/
namespace Solidity.Backend.FailurePaths.Premises
open Source

/-- G41 must relate its bytes to the actual upstream encoder, including all
source state effects. This signature does not supply selector correspondence. -/
def EncodingAt {E : Source.Env} {types : List STy} (frame : Fr) (fuel : Nat)
    (values : RVals E.layout types) (initial reached : St E) (payload : Roadmap.Bytes) : Prop :=
  (encodeVals frame fuel false values : EM E [] _).run (Source.L0 E, initial) =
    (.ok payload, (Source.L0 E, reached))

/-- Existing P1 interface, with its original representation and allocation
premises. No new frame transport implementation is supplied by G38. -/
abbrev InternalBareRevert {C : Contract} {Γ Δ : Ctx} (base : Nat)
    (fragment : Evm.Frag Γ) (statement : Stmt C Γ Δ)
    (plan : InternalFlow.RuntimeFrame.InterfaceV1.Emission C Γ Δ) :=
  InternalFlow.RuntimeFrame.InterfaceV1.BareRevertClaim base fragment statement plan

/-- H16's incomplete source computation must retain timeout, not become a
completed REVERT merely because the eventual statement is a failure. -/
def IncompleteAt {E : Source.Env} {Γ : RCtx} {α : Type}
    (computation : EM E Γ α) (initial reached : Locals E.layout Γ × St E) : Prop :=
  computation.run initial = (.error .timeout, reached)

/-- Residual source projection only. The supported empty case is discharged by
TransientUnwind using actual P7 execution. This predicate is not assumed by that
proof and does not supply the remaining nonempty-payload target transport. -/
def TransientRestored {D : Layout} {L T : Roadmap.Address → Source.SPath → STy}
    (saved restored : ExecState D L T) : Prop :=
  restored.transient = saved.transient

/-- Residual joint payload/frame obligation over the actual published evaluators
and an explicit word/byte representation. There is NO assumed instance. In
particular, TransientControls refutes the current nonempty-emitter adapter case:
P7 refuses MSTORE8/nonempty REVERT and retains dirty state. A future producer
must supply genuine execution evidence, not reinterpret unsupported as revert.
The finite word frame is not a universal source/world representation. -/
def TransientPayloadAt (frame : Fr) (code : Backend.Program)
    (entry : Transient.State) (bytes : Failure.Slice.Machine)
    (cells : List Nat) (offset : Nat) (payload : Roadmap.Bytes) : Prop :=
  MemoryOps.Physical.WordFrame entry.machine bytes.memory (fun cell => cell ∈ cells) ∧
  Failure.Slice.checkedRun code bytes =
    some ({bytes with memory := Failure.Slice.putBytes bytes.memory offset payload},
      some (.revert payload)) ∧
  Transient.callbackInFrame frame code entry = .error .reverted entry

end Solidity.Backend.FailurePaths.Premises
