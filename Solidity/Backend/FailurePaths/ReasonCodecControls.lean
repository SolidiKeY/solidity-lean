import Solidity.Backend.FailurePaths.ReasonCodec
import Solidity.Backend.FailurePaths.ParametricControls

/-! Inhabited G41 consumer: actual reference-signature source statements,
constant-packet execution, complete readback and malformed-selector refusal. -/
namespace Solidity.Backend.FailurePaths.ReasonCodecControls
open Source Lowering.V08.SourceCustomErrorControls

theorem client (pipeline : Roadmap.Pipeline) (reason : Roadmap.Bytes) (small : reason.length ≤ 33) :
    Parametric.compile (global pipeline) 5
      (ReasonCodec.statement (E := E) (R := [.bytes .memory]) (Γ := [.bytes .memory]) reason) =
      some (Failure.emit 5 (.custom (Source.errorData reason))) ∧
    Parametric.Reverts (global pipeline) frame 7 0
      (ReasonCodec.statement (R := [.bytes .memory]) reason) ParametricControls.locals populated (Source.errorData reason) ∧
    Failure.Slice.checkedRun (Failure.emit 5 (.custom (Source.errorData reason)) ++ Controls.tail) Controls.machine =
      some ({Controls.machine with memory := Failure.Slice.putBytes Controls.machine.memory 5 (Source.errorData reason)},
        some (.revert (Source.errorData reason))) ∧
    Semantics.decodeError (Failure.Slice.getBytes
      (Failure.Slice.putBytes Controls.machine.memory 5 (Source.errorData reason)) 5 (Source.errorData reason).length) = some reason :=
  ReasonCodec.compiled_readback (global pipeline) frame 0 0 5 reason ParametricControls.locals populated
    Controls.tail Controls.machine (Lowering.V08.LiteralFailureControls.reason_fits reason small) (by decide +kernel)

theorem malformed_selector : Semantics.decodeError [0,0,0,0] = none := rfl

def boundaryReason : Roadmap.Bytes := List.replicate 31 0 ++ [255, 1]
#eval Semantics.decodeError (Source.errorData boundaryReason)
#eval Semantics.decodeError (Failure.Slice.getBytes
  (Failure.Slice.putBytes Controls.machine.memory 5 (Source.errorData boundaryReason)) 5
  (Source.errorData boundaryReason).length)
#check client
#print axioms client
end Solidity.Backend.FailurePaths.ReasonCodecControls
