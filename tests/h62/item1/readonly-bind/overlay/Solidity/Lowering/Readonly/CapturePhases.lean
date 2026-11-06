import Solidity.Source.Hoare
import Solidity.Backend.Passes.SourceTypedCall

/-! Source-order composition of actual external-call capture phase runs.
Every checkpoint is an actual evaluator state; no phase is reevaluated and
no raw-call/frame provenance is supplied by this lemma. -/
namespace Solidity.Lowering.Readonly.CapturePhases
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

/-- Successful phase evaluations may each have effects. The code-admission
check is an actual instance lookup at the post-encoding state, not a label. -/
theorem compose (global : Glob E) (frame : Fr) (n : Nat) (d : Decl)
    (signature : d.fnSig E = some (ps, rs))
    (target : RExpr E Γ (.contract dn)) (value : RExpr E Γ (.int IntTy.u256))
    (arguments : RConvArgs E Γ ps) (a : Address) (v : Int)
    (valid : IntTy.u256.lo ≤ v ∧ v ≤ IntTy.u256.hi) (vs : Vals E.layout ps)
    (encoded : Bytes) (inst : Option String)
    (s₀ s₁ s₂ s₃ s₄ s₅ : Locals E.layout Γ × St E)
    (targetRun : (evalE global frame n target).run s₀ = (.ok (.val (.contract a)), s₁))
    (valueRun : (evalE global frame n value).run s₁ = (.ok (.val (.int v valid)), s₂))
    (argsRun : (evalConvArgs global frame n arguments).run s₂ = (.ok vs, s₃))
    (encodingRun : (encodeVals frame n false vs.toR).run s₃ = (.ok encoded, s₄))
    (instanceRun : (instanceAt global a).run s₄ = (.ok inst, s₅))
    (admitted : (inst.isNone && !global.hasCode s₅.2.events a) = false) :
    CapturedAt global frame n target d signature value arguments s₀ s₅
      ⟨a, ⟨v.toNat % 2 ^ 256, Nat.mod_lt _ (by decide)⟩, vs,
        global.selector (sigOf E.layout d.name ps) ++ encoded⟩ := by
  unfold CapturedAt capture
  rw [signature]
  simp only [Solidity.Source.Hoare.run_bind, targetRun, get_plain, run_pure,
    valueRun, argsRun, encodingRun, instanceRun, run_st, admitted, Bool.false_eq_true,
    ↓reduceIte]

end Solidity.Lowering.Readonly.CapturePhases
