import Solidity.Backend.Scalar.Capacity
import Solidity.Backend.Scalar.CastChains
import Solidity.Backend.Scalar.WidthGuards

/-! Inhabited mixed-width/source-type regressions. Values remain the pinned
intrinsic Val and PrimTy denotations, uniform over all typed states. -/
namespace Solidity.Backend.Scalar
variable {C : Contract} {Γ : Ctx}

private def u (n : Int) (h : PrimTy.uint.inRange n = true) : Val C Γ .uint :=
  .simple (.lit n h)

/-- The existing signedAt arithmetic expansion applied to a wrapping sum.
Input literals fit uint8; the sum 257 needs uint16; the final int8 is 1. -/
def mixedWidthSource : Val C Γ .int :=
  let sum : Val C Γ .uint := .binop .addW rfl rfl (u 255 (by decide)) (u 2 (by decide))
  let biased : Val C Γ .uint := .binop .addW rfl rfl sum (u 128 (by decide))
  let low : Val C Γ .uint := .binop .mod rfl rfl biased (u 256 (by decide))
  .unop .toInt rfl rfl (.binop .subW rfl rfl low (u 128 (by decide)))

def mixedWidthCode : Program :=
  [pushWord 2, pushWord 255, .op .ADD] ++ signedCode ⟨0, by decide⟩

def mixedWidthCertificate : ClosedCertificate (mixedWidthSource (C := C) (Γ := Γ)) where
  value := ⟨1, by decide⟩
  code := mixedWidthCode
  source := by intro σ; rfl
  target := by
    intro tail
    apply run_comp (p := [pushWord 2, pushWord 255, .op .ADD])
      (q := signedCode ⟨0, by decide⟩) (t := (257:Word)::tail)
    · rw [run, step_pushWord, Option.bind_some, run, step_pushWord]
      rfl
    · rw [signed_correct]
      rfl

def mixedWidthInvocation : ClosedInvocation (mixedWidthCertificate (C := C) (Γ := Γ)) [99] where
  capacity := by
    change stackBound mixedWidthCode 1 = true
    decide +kernel

/-- Checked uint8 rejects this same sum; wrapping/casting must not inherit that guard. -/
example : guarded (unsignedWidthTest ⟨0, by decide⟩) [] overflowFailure [257,99] =
    some (.error overflowFailure) := rfl

theorem mixedWidth_source (σ : State C Γ) :
    mixedWidthSource.evalT σ = .ok (mixedWidthCertificate (C := C) (Γ := Γ)).value :=
  mixedWidthCertificate.source σ

theorem mixedWidth_target {C : Contract} {Γ : Ctx} (tail : Stack) : run mixedWidthCode tail = some (1::tail) :=
  (mixedWidthCertificate (C := C) (Γ := Γ)).target tail

#print axioms mixedWidthCertificate
#print axioms mixedWidthInvocation
#print axioms mixedWidth_source
#print axioms mixedWidth_target
end Solidity.Backend.Scalar
