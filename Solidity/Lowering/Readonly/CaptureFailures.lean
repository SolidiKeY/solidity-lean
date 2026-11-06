import Solidity.Source.Hoare
import Solidity.Lowering.Readonly.CapturePhases

/-! Failure transport for the actual source external-call capture. Exact
phase-state runs retain prior effects and prevent all later phases/callee
execution. These laws do not supply a general body/frame/raw producer. -/
namespace Solidity.Lowering.Readonly.CaptureFailures
open Solidity.Source Solidity.Backend.Passes.SourceTypedCall
open Solidity.Roadmap (Address Bytes)
open EM
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}

private theorem get_plain {τ : STy} (v : Val E.layout τ) :
    (getV (.val v) : EM E Γ _) = pure v := rfl
private theorem run_pure {α : Type} (v : α) (s : Locals E.layout Γ × St E) :
    (pure v : EM E Γ α).run s = (.ok v, s) := rfl
private theorem run_st (s : Locals E.layout Γ × St E) :
    (st : EM E Γ (St E)).run s = (.ok s.2, s) := rfl

private theorem run_halt {α : Type} (h : Halt) (s : Locals E.layout Γ × St E) :
    (halt h : EM E Γ α).run s = (.error h, s) := rfl

theorem target_failed (global : Glob E) (frame : Fr) (n : Nat) (d : Decl)
    (signature : d.fnSig E = some (ps, rs))
    (target : RExpr E Γ (.contract dn)) (value : RExpr E Γ (.int IntTy.u256))
    (arguments : RConvArgs E Γ ps)
    (s₀ s₁ : Locals E.layout Γ × St E) (halt : Halt)
    (failed : (evalE global frame n target).run s₀ = (.error halt, s₁)) :
    (evalE global frame (n + 1) (.extCall target d signature value arguments)).run s₀ =
      (.error halt, s₁) := by
  apply external_capture_failure _ _ _ _ _ _ _ _ _ _
  unfold capture
  simp only [Solidity.Source.Hoare.run_bind, failed]

theorem value_failed (global : Glob E) (frame : Fr) (n : Nat) (d : Decl)
    (signature : d.fnSig E = some (ps, rs))
    (target : RExpr E Γ (.contract dn)) (value : RExpr E Γ (.int IntTy.u256))
    (arguments : RConvArgs E Γ ps)
    (a : Address) (s₀ s₁ s₂ : Locals E.layout Γ × St E) (halt : Halt)
    (targetRun : (evalE global frame n target).run s₀ = (.ok (.val (.contract a)), s₁))
    (failed : (evalE global frame n value).run s₁ = (.error halt, s₂)) :
    (evalE global frame (n + 1) (.extCall target d signature value arguments)).run s₀ =
      (.error halt, s₂) := by
  apply external_capture_failure _ _ _ _ _ _ _ _ _ _
  unfold capture
  simp only [Solidity.Source.Hoare.run_bind, targetRun, get_plain, run_pure, failed]

theorem arguments_failed (global : Glob E) (frame : Fr) (n : Nat) (d : Decl)
    (signature : d.fnSig E = some (ps, rs))
    (target : RExpr E Γ (.contract dn)) (value : RExpr E Γ (.int IntTy.u256))
    (arguments : RConvArgs E Γ ps)
    (a : Address) (v : Int) (valid : IntTy.u256.lo ≤ v ∧ v ≤ IntTy.u256.hi)
    (s₀ s₁ s₂ s₃ : Locals E.layout Γ × St E) (halt : Halt)
    (targetRun : (evalE global frame n target).run s₀ = (.ok (.val (.contract a)), s₁))
    (valueRun : (evalE global frame n value).run s₁ = (.ok (.val (.int v valid)), s₂))
    (failed : (evalConvArgs global frame n arguments).run s₂ = (.error halt, s₃)) :
    (evalE global frame (n + 1) (.extCall target d signature value arguments)).run s₀ =
      (.error halt, s₃) := by
  apply external_capture_failure _ _ _ _ _ _ _ _ _ _
  unfold capture
  simp only [Solidity.Source.Hoare.run_bind, targetRun, get_plain, run_pure, valueRun, failed]

theorem encoding_failed (global : Glob E) (frame : Fr) (n : Nat) (d : Decl)
    (signature : d.fnSig E = some (ps, rs))
    (target : RExpr E Γ (.contract dn)) (value : RExpr E Γ (.int IntTy.u256))
    (arguments : RConvArgs E Γ ps)
    (a : Address) (v : Int) (valid : IntTy.u256.lo ≤ v ∧ v ≤ IntTy.u256.hi)
    (vs : Vals E.layout ps) (s₀ s₁ s₂ s₃ s₄ : Locals E.layout Γ × St E) (halt : Halt)
    (targetRun : (evalE global frame n target).run s₀ = (.ok (.val (.contract a)), s₁))
    (valueRun : (evalE global frame n value).run s₁ = (.ok (.val (.int v valid)), s₂))
    (argsRun : (evalConvArgs global frame n arguments).run s₂ = (.ok vs, s₃))
    (failed : (encodeVals frame n false vs.toR).run s₃ = (.error halt, s₄)) :
    (evalE global frame (n + 1) (.extCall target d signature value arguments)).run s₀ =
      (.error halt, s₄) := by
  apply external_capture_failure _ _ _ _ _ _ _ _ _ _
  unfold capture
  simp only [Solidity.Source.Hoare.run_bind, targetRun, get_plain, run_pure, valueRun, argsRun, failed]

theorem code_rejected (global : Glob E) (frame : Fr) (n : Nat) (d : Decl)
    (signature : d.fnSig E = some (ps, rs))
    (target : RExpr E Γ (.contract dn)) (value : RExpr E Γ (.int IntTy.u256))
    (arguments : RConvArgs E Γ ps)
    (a : Address) (v : Int) (valid : IntTy.u256.lo ≤ v ∧ v ≤ IntTy.u256.hi)
    (vs : Vals E.layout ps) (encoded : Bytes) (inst : Option String)
    (s₀ s₁ s₂ s₃ s₄ s₅ : Locals E.layout Γ × St E)
    (targetRun : (evalE global frame n target).run s₀ = (.ok (.val (.contract a)), s₁))
    (valueRun : (evalE global frame n value).run s₁ = (.ok (.val (.int v valid)), s₂))
    (argsRun : (evalConvArgs global frame n arguments).run s₂ = (.ok vs, s₃))
    (encodingRun : (encodeVals frame n false vs.toR).run s₃ = (.ok encoded, s₄))
    (instanceRun : (instanceAt global a).run s₄ = (.ok inst, s₅))
    (rejected : (inst.isNone && !global.hasCode s₅.2.events a) = true) :
    (evalE global frame (n + 1) (.extCall target d signature value arguments)).run s₀ =
      (.error (.revert []), s₅) := by
  apply external_capture_failure _ _ _ _ _ _ _ _ _ _
  unfold capture
  simp only [Solidity.Source.Hoare.run_bind, targetRun, get_plain, run_pure, valueRun, argsRun,
    encodingRun, instanceRun, run_st, rejected, ↓reduceIte, run_halt]

end Solidity.Lowering.Readonly.CaptureFailures
