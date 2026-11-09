import Solidity.Lowering.V07.UnsignedQuotRemPass

/-! The complete success/zero split for the V07 unsigned quotient/remainder
clause, expressed once for both operators, every width, checkedness mode and
pipeline. Signed quotient/remainder remain separate arithmetic obligations. -/
namespace Solidity.Lowering.G16.UnsignedQuotRem
open Solidity.Lowering.V07
open UnsignedNarrowing (ty)
open Solidity.Lowering.V07.UnsignedQuotRem (calculate sourceOp)
open UnsignedQuotRemEffects (divisor divisor_range)

/-- No nonzero-divisor premise: the zero branch retains the actual panic
payload, while the other branch derives the result range. Initial alias
agreement is the existing V07 family, with its postrelation derived below. -/
theorem transport (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (rem : Bool)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env) (i a : ι)
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx) (readI : source.1.get (si i) = .int y hy) :
    if zero : divisor G.pipeline x y = 0 then
      (Source.evalE G F (fuel+4)
        (.binary (sourceOp rem) (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
          (.error (.revert (Source.panicData .divZero)),(source.1.set (si i) (.int x hx),source.2)) ∧
      (UnsignedQuotRemPass.effectsOperand G.pipeline rem (ti i) (ti a)).run target =
        .error (THalt.ofData (Source.panicData .divZero)) ∧
      IntegerLocalFamily (ty bits valid) si ti (source.1.set (si i) (.int x hx))
        (TEnv.set (ti i) (integerValue (ty bits valid) x hx) target.env)
    else
      (Source.evalE G F (fuel+4)
        (.binary (sourceOp rem) (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
        (.ok (.val (.int (calculate rem x (divisor G.pipeline x y))
          (Solidity.Lowering.V07.UnsignedQuotRem.result_range bits valid rem x _ hx
            (divisor_range G.pipeline _ x y hx hy) zero))),
          (source.1.set (si i) (.int x hx),source.2)) ∧
      (UnsignedQuotRemPass.effectsOperand G.pipeline rem (ti i) (ti a)).run target =
        .ok (⟨target.setLocal (ti i) (integerValue (ty bits valid) x hx),List.prefix_refl _⟩,
          .prim (integerValue (ty bits valid) (calculate rem x (divisor G.pipeline x y))
            (Solidity.Lowering.V07.UnsignedQuotRem.result_range bits valid rem x _ hx
              (divisor_range G.pipeline _ x y hx hy) zero))) ∧
      IntValueRel (ty bits valid)
        (.int (calculate rem x (divisor G.pipeline x y))
          (Solidity.Lowering.V07.UnsignedQuotRem.result_range bits valid rem x _ hx
            (divisor_range G.pipeline _ x y hx hy) zero) : Source.Val E.layout (.int (ty bits valid)))
        (integerValue (ty bits valid) (calculate rem x (divisor G.pipeline x y))
          (Solidity.Lowering.V07.UnsignedQuotRem.result_range bits valid rem x _ hx
            (divisor_range G.pipeline _ x y hx hy) zero)) ∧
      IntegerLocalFamily (ty bits valid) si ti (source.1.set (si i) (.int x hx))
        (TEnv.set (ti i) (integerValue (ty bits valid) x hx) target.env) := by
  by_cases zero : divisor G.pipeline x y = 0
  · simp only [dif_pos zero]
    have actual := UnsignedQuotRemPass.transport_zero bits valid G F fuel source target rem
      si ti family i a x y hx hy zero readA readI
    exact ⟨actual.1,actual.2.1,actual.2.2.2⟩
  · simp only [dif_neg zero]
    exact UnsignedQuotRemPass.transport_success bits valid G F fuel source target rem
      si ti family i a x y hx hy zero readA readI

end Solidity.Lowering.G16.UnsignedQuotRem

/-- info: 'Solidity.Lowering.G16.UnsignedQuotRem.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.UnsignedQuotRem.transport
