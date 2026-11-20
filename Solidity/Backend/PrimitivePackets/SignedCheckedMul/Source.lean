import Solidity.Backend.PrimitivePackets.CheckedBinary

/-! Actual checked int256 Source local evaluation. No target result or desired
run is a premise. The frame and full input state are retained. -/
namespace Solidity.Backend.PrimitivePackets.SignedCheckedMul
open Solidity.Lowering.V07

abbrev U : Source.IntTy := ⟨true,256,by decide⟩

theorem source_success {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (a b : Source.Idx Γ (.int U)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : s.1.get a = .int x hx) (hb : s.1.get b = .int y hy)
    (fits : U.lo ≤ x*y ∧ x*y ≤ U.hi) :
    (Source.evalE G {F with checked := true} (fuel+3)
      (.binary .mul (.local a) (.local b))).run s =
      (.ok (.val (.int (x*y) fits)),s) :=
  CheckedBinary.source_success G F fuel s U .mul (·*·) (by decide) (by decide)
    a b x y hx hy ha hb rfl fits

theorem source_overflow {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (a b : Source.Idx Γ (.int U)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : s.1.get a = .int x hx) (hb : s.1.get b = .int y hy)
    (overflow : ¬ (U.lo ≤ x*y ∧ x*y ≤ U.hi)) :
    (Source.evalE G {F with checked := true} (fuel+3)
      (.binary .mul (.local a) (.local b))).run s =
      (.error (.revert (Source.panicData .arithmetic)),s) :=
  CheckedBinary.source_overflow G F fuel s U .mul (·*·) (by decide) (by decide)
    a b x y hx hy ha hb rfl overflow

end Solidity.Backend.PrimitivePackets.SignedCheckedMul
