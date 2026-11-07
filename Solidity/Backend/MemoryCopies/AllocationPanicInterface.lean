import Solidity.Backend.MemoryCopies.Premises
import Solidity.Lowering.V08.LiteralFailureLowering

/-! Allocation-panic emission at the existing explicit S03 boundary. The
allocation-size selector and finalize/cursor semantics remain producer duties. -/
namespace Solidity.Backend.MemoryCopies
open Solidity.Backend

/-- Reuse the published actual instruction emitter; no encoder is added. -/
def panic41Code (offset : Nat) : Program :=
  Failure.emit offset (Solidity.Lowering.V08.LiteralFailureLowering.panicInput .alloc)

/-- Complete actual Source failure state and byte-exact terminal target slice.
The opcode slice has architectural stack/address bounds and no gas/world model.
This does not claim successful allocation or a compiled size selector. -/
structure Panic41EmissionCertificate {E : Source.Env} {Γ : Source.RCtx} {α : Type}
    (operation : Source.EM E Γ α) (before reached : Source.EMState E Γ)
    (offset : Nat) (machine : Failure.Slice.Machine) : Prop where
  source : operation.run before = (Source.panic .alloc, reached)
  target : ∀ suffix : Program,
    Failure.Slice.checkedRun (panic41Code offset ++ suffix) machine =
      some ({machine with memory := Failure.Slice.putBytes machine.memory offset (Source.panicData .alloc)},
        some (Source.revertOutcome (Source.panicData .alloc)))

end Solidity.Backend.MemoryCopies
