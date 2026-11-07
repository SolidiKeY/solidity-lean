import Solidity.Lowering.V07.IntegerConstants

/-! Literal conversion for every existing legal integer width and sign.
No new Source representation or admission judgment is introduced. -/
namespace Solidity.Backend.PrimitivePackets.Constants
open Solidity.Lowering.V07

theorem source_success {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) :
    (Source.evalE G F (fuel+2)
      (.conv (.const (Source.Q.ofInt z)) (.inl (IntegerConstants.allowed E t z h)))).run s =
      (.ok (.val (.int z h)),s) :=
  IntegerConstants.source_run G F fuel s t z h

theorem source_refused {D : Source.Layout} (t : Source.IntTy) (z : Int)
    (outside : ¬ (t.lo ≤ z ∧ z ≤ t.hi)) :
    Source.constVal (Source.Q.ofInt z) (.int t) =
      (.error (.stuck "integer out of range") : Source.R (Source.Val D (.int t))) :=
  IntegerConstants.source_refused t z outside

theorem conversion_refused (E : Source.Env) (t : Source.IntTy) (z : Int)
    (outside : ¬ (t.lo ≤ z ∧ z ≤ t.hi)) :
    (Source.STy.rational (Source.Q.ofInt z)).implicit E.isBase E.mapFree (.int t) = false :=
  IntegerConstants.not_allowed E t z outside

end Solidity.Backend.PrimitivePackets.Constants
