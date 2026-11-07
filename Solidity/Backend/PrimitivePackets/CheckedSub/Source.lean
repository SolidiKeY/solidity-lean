import Solidity.Lowering.V07.UnsignedNarrowing

/-! Actual checked uint256 Source local evaluation. No target result or desired
run is a premise. The frame and full input state are retained. -/
namespace Solidity.Backend.PrimitivePackets.CheckedSub
open Solidity.Lowering.V07

abbrev U := Source.IntTy.u256

theorem source_success {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (a b : Source.Idx Γ (.int U)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : s.1.get a = .int x hx) (hb : s.1.get b = .int y hy)
    (fits : U.lo ≤ x-y ∧ x-y ≤ U.hi) :
    (Source.evalE G {F with checked := true} (fuel+3)
      (.binary .sub (.local a) (.local b))).run s =
      (.ok (.val (.int (x-y) fits)),s) := by
  rw [Source.evalE]
  simp only [reduceCtorEq,decide_false,Bool.false_or,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,source_local_pair G {F with checked := true} fuel s U a b x y hx hy ha hb]
  change (do
    let v ← Source.EM.lift (Source.binVal true .sub
      (.int x hx : Source.Val E.layout (.int U)) (.int y hy))
    pure (Source.RVal.val v)).run s = _
  simp only [Source.binVal,Source.intBin,Source.intRes,dif_pos fits]
  rfl

theorem source_underflow {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (a b : Source.Idx Γ (.int U)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : s.1.get a = .int x hx) (hb : s.1.get b = .int y hy)
    (underflow : ¬ (U.lo ≤ x-y ∧ x-y ≤ U.hi)) :
    (Source.evalE G {F with checked := true} (fuel+3)
      (.binary .sub (.local a) (.local b))).run s =
      (.error (.revert (Source.panicData .arithmetic)),s) := by
  rw [Source.evalE]
  simp only [reduceCtorEq,decide_false,Bool.false_or,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,source_local_pair G {F with checked := true} fuel s U a b x y hx hy ha hb]
  change (do
    let v ← Source.EM.lift (Source.binVal true .sub
      (.int x hx : Source.Val E.layout (.int U)) (.int y hy))
    pure (Source.RVal.val v)).run s = _
  simp only [Source.binVal,Source.intBin,Source.intRes,dif_neg underflow,if_true,Source.panic]
  rfl

end Solidity.Backend.PrimitivePackets.CheckedSub
