import Solidity.Backend.FailurePaths.Premises
import Solidity.Backend.FailurePaths.WorldUnwind

/-!
# Payload return after the actual source encoder

The encoding equation is an explicit G41 premise for general values. Boolean
values below discharge it with the existing upstream encoder theorem. This is
a payload-boundary theorem, not compilation of arbitrary return statements.
-/
namespace Solidity.Backend.FailurePaths
open Source

/-- Return commits the reached source-store projections and emitted byte memory;
it does not take the failure checkpoint branch even when bytes are identical. -/
theorem encoded_return {E : Source.Env} {types : List STy}
    (frame : Fr) (fuel offset : Nat) (values : RVals E.layout types)
    (initial reached caller : St E) (payload : Roadmap.Bytes)
    (encoded : Premises.EncodingAt frame fuel values initial reached payload)
    (saved live : Failure.Slice.Machine)
    (fits : Failure.Fits offset payload) (stack : live.stack.length + 2 ≤ 1024) :
    Premises.EncodingAt frame fuel values initial reached payload ∧
    Emits (Failure.emit offset (.returned payload)) offset (.returned payload) ∧
    Failure.Local.execute
      (Failure.Local.save (MemoryOps.Physical.worldJournal caller.ex saved)) offset (.returned payload)
      (MemoryOps.Physical.worldJournal reached.ex live) =
      some (MemoryOps.Physical.worldJournal reached.ex
        {live with memory := Failure.Slice.putBytes live.memory offset payload}, .success payload) :=
  ⟨encoded, Failure.checkedRun_emit_suffix offset (.returned payload),
    Failure.Local.execute_return _ offset payload _ fits stack⟩

/-- An inhabited encoder family, with arbitrary initial source state, horizon
and Boolean list. No general G41 encoding oracle is used for this instance. -/
theorem boolean_encoding {E : Source.Env} (frame : Fr) (fuel : Nat)
    (bits : List Bool) (state : St E) :
    Premises.EncodingAt frame fuel
      (Lowering.V08.BoolErrorLowering.values (E := E) bits).toR state state
      (Lowering.V08.BoolErrorLowering.encoded bits) :=
  Lowering.V08.BoolErrorLowering.encoding_run frame fuel bits (Source.L0 E) state

#print axioms encoded_return
#print axioms boolean_encoding
end Solidity.Backend.FailurePaths
