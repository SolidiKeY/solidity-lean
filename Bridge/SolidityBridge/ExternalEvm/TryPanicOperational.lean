import SolidityBridge.ExternalEvm.TryPanicRelative
import Solidity.Backend.TryCall.PanicEmitter
import Solidity.Frontend.SolcJson.TryPanicCallMetadata

/-! Operational adapter for the H8 proof-only normalization. This does not
identify an original source/compiled site: Normalized is structural syntax
association, and RF.ReturnClaim remains checked-target transport to be supplied.
The optional imports use the published H7 padding and scanner interfaces. -/
namespace Solidity.Evm.External.TryPanicOperational
open Solidity Evm.TryByteImage Evm.TryPanicProducer
open TryPanicRelative
variable {C : Contract}

/-- No desired run, reply, target selection or resource result is a field. -/
structure Normalized (s : Site C) : Prop where
  call : s.call = Evm.TryPanicCallMetadata.sourceCall s.call.mode s.call.invocation
  body : s.body = Evm.TryPanicSourceBody.body
  return94 : s.return94 = Evm.TryPanicSourceControl.return94
  caller : s.callerBody = Evm.TryPanicCallMetadata.caller s.call Evm.TryPanicSourceBody.body

/-- Concrete proof-only artifacts. This builder does not prove source or
compiler association, installation, frame provenance or target ReturnClaim. -/
def normalize (s : Site C) : Site C :=
  { s with call := Evm.TryPanicCallMetadata.sourceCall s.call.mode s.call.invocation
           body := Evm.TryPanicSourceBody.body
           return94 := Evm.TryPanicSourceControl.return94
           callerBody := Evm.TryPanicCallMetadata.caller
             (Evm.TryPanicCallMetadata.sourceCall s.call.mode s.call.invocation)
             Evm.TryPanicSourceBody.body }

theorem normalized (s : Site C) : Normalized (normalize s) := ⟨rfl, rfl, rfl, rfl⟩

/-- The three source-operation fields are proved. Only the two named routine
primitive adapters and the independent checked compiled return are consumed. -/
theorem operational (s : Site C) (norm : Normalized s)
    (glue : Evm.TryPanicSourceBody.PutThen (C := C))
    (allocation : Evm.TryPanicSourceBody.AllocateRun (C := C))
    (target : RF.ReturnClaim s.b s.fragment s.callerBody s.emission) : Operational s := by
  constructor
  · exact norm.call
  · intro σ key K aligned large μ final bytes entry completed
    rw [norm.body]
    exact Evm.TryPanicSourceExecution.completed glue allocation
      σ key K aligned large μ final bytes entry completed
  · intro σ
    rw [norm.return94]
    exact Evm.TryPanicSourceControl.return94_run σ
  · rw [norm.caller]
    unfold callerForm
    rw [norm.body, norm.return94]
    rfl
  · exact target

/-- All owned source-operation/glue fields are now discharged. Structural
association and checked emitted code remain separate inputs for an arbitrary site. -/
theorem operational_closed (s : Site C) (norm : Normalized s)
    (target : RF.ReturnClaim s.b s.fragment s.callerBody s.emission) : Operational s :=
  operational s norm Solidity.Backend.TryCall.PanicNormalization.put_then Solidity.Backend.TryCall.PanicNormalization.allocate_run target

/-- H22 metadata erasure is proved by the unchanged evaluator, not assumed. -/
theorem normalized_runR (s : Site C) (norm : Normalized s) :
    s.callerBody.runR = (Evm.TryPanicSourceControl.caller Evm.TryPanicSourceBody.body).runR := by
  rw [norm.caller, norm.call]
  exact Evm.TryPanicCallMetadata.source_runR _ _ _

/-- The concrete normalization builder discharges its own structural fields.
This does not prove that an original compiler output is this normalization. -/
theorem operational_normalized (s : Site C)
    (target : RF.ReturnClaim s.b s.fragment (normalize s).callerBody s.emission) :
    Operational (normalize s) := operational_closed (normalize s) (normalized s) target

theorem source_return (s : Site C) (norm : Normalized s)
    (nonzero : s.caller.tx.selfAddress.val ≠ 0) :
    Stmt.run s.caller s.callerBody = .ok (callerOut s.caller) := by
  change s.callerBody.runR s.caller = _
  rw [normalized_runR s norm]
  exact Solidity.Backend.TryCall.PanicNormalization.nonzero s.caller s.key nonzero

/-- Derive the actual same-entry normal-return witness from checked target
transport; target code is not inferred from source control or syntax alone. -/
theorem return_of_checked (s : Site C) (norm : Normalized s)
    (target : RF.ReturnClaim s.b s.fragment s.callerBody s.emission)
    (entry : RF.Entry s.emission s.L s.b s.frame s.fragment s.caller s.base s.machine s.start)
    (nonzero : s.caller.tx.selfAddress.val ≠ 0) :
    ∃ out : Solidity.Out C s.caller.H Caller,
      Stmt.run s.caller s.callerBody = .ok out ∧
      RF.Returned s.emission s.L s.b s.frame s.caller s.base s.machine s.start out := by
  refine ⟨callerOut s.caller, source_return s norm nonzero, ?_⟩
  exact target s.L s.frame s.caller s.base s.machine s.start entry _ (source_return s norm nonzero)

/-- A supplied reverting target at this real represented entry cannot serve
as a normal-return emitter for the successful normalized caller. -/
theorem reject_reverting_target (s : Site C) (norm : Normalized s)
    (entry : RF.Entry s.emission s.L s.b s.frame s.fragment s.caller s.base s.machine s.start)
    (nonzero : s.caller.tx.selfAddress.val ≠ 0)
    (wrong : Evm.run s.emission.code s.machine = .revert) :
    ¬ RF.ReturnClaim s.b s.fragment s.callerBody s.emission := by
  intro target
  obtain ⟨_, _, returned⟩ := return_of_checked s norm target entry nonzero
  obtain ⟨_, _, executed, _⟩ := returned
  rw [wrong] at executed
  cases executed

/-- Structural association cannot silently substitute the fixed36 carrier
for the now-proved generic body. This is a wrong-artifact control, not source
installation or an actual compiler association witness. -/
theorem reject_constant_body (s : Site C) (wrong : s.body = Evm.TryPanicCarrier.carrier36) :
    ¬ Normalized s := by
  intro norm
  have fixed : Evm.TryPanicSourceBody.body (C := C) = Evm.TryPanicCarrier.carrier36 :=
    norm.body.symm.trans wrong
  have different :
      Evm.TryPanicSourceBody.body.runR ((callee s.caller).withEnv (zero, ())) ≠
      Evm.TryPanicCarrier.carrier36.runR ((callee s.caller).withEnv (zero, ())) :=
    Evm.TryPanicSourceExecution.differs_at_zero
        Solidity.Backend.TryCall.PanicNormalization.put_then
        Solidity.Backend.TryCall.PanicNormalization.allocate_run (callee s.caller)
  rw [fixed] at different
  exact different rfl

/-- The owned checked-emitter producer removes the independent ReturnClaim
premise for structurally matching sites. Emission equality is still an exact
association prerequisite, not original compiler/deployment provenance. -/
theorem operational_checked (s : Site C) (norm : Normalized s) (lo pointer : Nat)
    (emission : s.emission = Solidity.Backend.TryCall.PanicEmitter.plan s.b lo pointer s.fragment) :
    Operational s := by
  apply operational_closed s norm
  rw [emission]
  intro L frame caller base machine start entry out actual
  change s.callerBody.runR caller = .ok out at actual
  rw [normalized_runR s norm] at actual
  exact Solidity.Backend.TryCall.PanicEmitter.returns s.b lo pointer s.fragment
    L frame caller base machine start entry out actual

/-- A proof-only normalized call builder consuming the real H22 field producer.
This is not an original-site or invocation-frame provenance instance. -/
def taggedNormalization (s : Site C) : Site C :=
  normalize { s with call := Solidity.Frontend.TryPanicCallMetadata.originalCall }

theorem tagged_mode (s : Site C) : (taggedNormalization s).call.mode = .static := rfl

theorem tagged_invocation (s : Site C) :
    (taggedNormalization s).call.invocation = .site 79 := rfl

theorem tagged_normalized (s : Site C) : Normalized (taggedNormalization s) :=
  normalized _

/-- Static AST-site identity is not the dynamic invocation/frame counter. -/
theorem tagged_dynamic_invocation (s : Site C) :
    (taggedNormalization s).invocation = s.invocation := rfl

/-- The actual caller record, not an independent site-tag witness. -/
theorem tagged_call (s : Site C) :
    (taggedNormalization s).call = Solidity.Frontend.TryPanicCallMetadata.originalCall := rfl

/-- Consume the checked emitter at the tagged normalized caller. This is a
model client, not original invocation/frame attainment. -/
theorem tagged_operational (s : Site C) (lo pointer : Nat)
    (emission : s.emission = Solidity.Backend.TryCall.PanicEmitter.plan s.b lo pointer s.fragment) :
    Operational (taggedNormalization s) :=
  operational_checked _ (tagged_normalized s) lo pointer emission

end Solidity.Evm.External.TryPanicOperational
