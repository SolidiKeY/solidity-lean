import Solidity.Backend.FailurePaths.Parametric
import Solidity.Backend.AbiWorld.ErrorRoundtrip

/-! Source Error(string) failures, checked emission and published G41 readback.
Only the published codec laws are discharged here; general encodeVals and
internal-frame transport remain separate obligations. -/
namespace Solidity.Backend.FailurePaths.ReasonCodec
open Source

def statement {E : Source.Env} {R : List STy} {Γ : RCtx} (reason : Roadmap.Bytes) :
    RStmt E R false .body Γ Γ :=
  .expr (Lowering.V08.LiteralFailureLowering.revertReason reason)

/-- Exact Source packet fields, derived from the published G41 codec. -/
theorem layout (reason : Roadmap.Bytes) :
    ((Source.errorData reason).drop 4).take 32 = Semantics.wordBytes 32 ∧
    ((Source.errorData reason).drop 36).take 32 = Semantics.wordBytes reason.length ∧
    ((Source.errorData reason).drop 68).take reason.length = reason := by
  rw [Lowering.V08.errorData_transport_total]
  exact ⟨AbiWorld.error_offset reason, AbiWorld.error_length_word reason, AbiWorld.error_payload reason⟩

/-- The existing span premise implies the codec's genuine word-length bound. -/
theorem roundtrip (reason : Roadmap.Bytes) (offset : Nat)
    (fits : Failure.Fits offset (Source.errorData reason)) :
    Semantics.decodeError (Source.errorData reason) = some reason := by
  have lengthBound := fits.2.1
  rw [Lowering.V08.LiteralFailureLowering.reason_length] at lengthBound
  have representable : reason.length < 256^32 := by
    change reason.length < Failure.wordLimit
    omega
  rw [Lowering.V08.errorData_transport_total]
  exact AbiWorld.error_roundtrip reason representable

/-- Both actual executions and decoder readback from the ACTUAL emitted memory.
There is no decoder/roundtrip premise and no hypothetical successful emission. -/
theorem compiled_readback {E : Source.Env} {R : List STy} {Γ : RCtx}
    (global : Glob E) (frame : Fr) (extra parameters offset : Nat) (reason : Roadmap.Bytes)
    (locals : Locals E.layout Γ) (state : St E) (suffix : Backend.Program)
    (machine : Failure.Slice.Machine) (fits : Failure.Fits offset (Source.errorData reason))
    (stack : machine.stack.length + 2 ≤ 1024) :
    Parametric.compile global offset (statement (E := E) (R := R) (Γ := Γ) reason) =
      some (Failure.emit offset (.custom (Source.errorData reason))) ∧
    Parametric.Reverts global frame (extra + 7) parameters (statement (E := E) (R := R) (Γ := Γ) reason)
      locals state (Source.errorData reason) ∧
    Failure.Slice.checkedRun (Failure.emit offset (.custom (Source.errorData reason)) ++ suffix) machine =
      some ({machine with memory := Failure.Slice.putBytes machine.memory offset (Source.errorData reason)},
        some (.revert (Source.errorData reason))) ∧
    Semantics.decodeError (Failure.Slice.getBytes
      (Failure.Slice.putBytes machine.memory offset (Source.errorData reason)) offset
      (Source.errorData reason).length) = some reason := by
  refine ⟨rfl, ?_, Failure.checkedRun_emit_suffix offset (.custom _) suffix machine fits stack, ?_⟩
  · have actual := (literal_statement global frame extra offset
      (Lowering.V08.LiteralFailureLowering.revertReason reason) (.custom (Source.errorData reason))
      rfl locals state).2.1
    exact (Parametric.expression_tag global frame (extra + 7) parameters _ locals state).trans actual
  · rw [Failure.Slice.getBytes_putBytes]
    exact roundtrip reason offset fits

#print axioms layout
#print axioms roundtrip
#print axioms compiled_readback
end Solidity.Backend.FailurePaths.ReasonCodec
