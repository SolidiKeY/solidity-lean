import Solidity.Frontend.SolcJson.TryPanicSourceCaller
import Solidity.Evm.TryPanicCallMetadata

/-! Typed H22 call metadata from the retained whole-source resolution.
This is not source execution, code installation or invocation-frame provenance. -/
namespace Solidity.Frontend.TryPanicCallMetadata
open TryPanicSourcePlan TryPanicSourceCaller Evm.TryByteImage
variable {C : Contract}

def modeOf : SourceMutability → CallMode
  | .pureFn | .viewFn => .static
  | .nonpayable | .payable => .call

/-- This is the actual ExtCall value, not a detached invocation relation. -/
def originalCall : ExtCall C CallerCtx :=
  Evm.TryPanicCallMetadata.sourceCall (modeOf fMetadata.mutability) (.site 79)

/-- The mode reads the callee's metadata, not c's nonpayable mutability. -/
theorem resolved_mode {p : Pipeline} {input unit owner decl : Lean.Json}
    (f : ResolvedF p input unit owner decl) :
    (sourceFunction (Solidity.Frontend.J.arrD owner "nodes").toList decl .selected false).map
      (fun metadata => modeOf metadata.mutability) = .ok .static := by
  rw [f.metadata]
  rfl

theorem static_mode : (originalCall (C := C)).mode = .static := rfl

theorem call_site {p : Pipeline} {input unit owner decl caller : Lean.Json}
    {f : ResolvedF p input unit owner decl} (c : ResolvedC f caller) :
    (originalCall (C := C)).invocation = .site 79 ∧
      Solidity.Frontend.J.id? TryPanicSourceData.callNode = some 79 :=
  ⟨rfl,c.callId⟩

theorem not_default : (originalCall (C := C)).mode ≠ .call ∧
    (originalCall (C := C)).invocation ≠ .unknown := by
  change (.static : CallMode) ≠ .call ∧ (.site 79 : InvocationId) ≠ .unknown
  decide

/-- c's nonpayable declaration must not choose f's call mode. -/
theorem caller_mutability_differs :
    modeOf cMetadata.mutability = .call ∧ (originalCall (C := C)).mode = .static :=
  ⟨rfl,rfl⟩

/-- The call is node79, not argument78 or function declaration7. -/
theorem not_argument_or_declaration :
    (originalCall (C := C)).invocation ≠ .site 78 ∧
    (originalCall (C := C)).invocation ≠ .site 7 := by
  change (.site 79 : InvocationId) ≠ .site 78 ∧ (.site 79 : InvocationId) ≠ .site 7
  decide

end Solidity.Frontend.TryPanicCallMetadata
