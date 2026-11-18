import Solidity.Lowering.V07.UnsignedAddition

/-! Shared checked Source evaluation of a non-logical integer operator on two
locals, for the checked add, sub and mul packets (unsigned and signed). Each
packet keeps its own statements and instantiates these at its operator. -/
namespace Solidity.Backend.PrimitivePackets.CheckedBinary
open Solidity.Lowering.V07

variable {E : Source.Env} {Γ : Source.RCtx}

theorem source_run (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (U : Source.IntTy) (op : Source.BinOp) (f : Int → Int → Int)
    (notAnd : op ≠ .and) (notOr : op ≠ .or)
    (a b : Source.Idx Γ (.int U)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : s.1.get a = .int x hx) (hb : s.1.get b = .int y hy)
    (spec : Source.intBin (D := E.layout) U true op x y = Source.intRes U true (f x y)) :
    (Source.evalE G {F with checked := true} (fuel+3)
      (.binary op (.local a) (.local b))).run s =
      (do
        let v ← Source.EM.lift (Source.intRes (D := E.layout) U true (f x y))
        pure (Source.RVal.val v)).run s := by
  rw [Source.evalE]
  simp only [notAnd,notOr,decide_false,Bool.false_or,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,source_local_pair G {F with checked := true} fuel s U a b x y hx hy ha hb]
  change (do
    let v ← Source.EM.lift (Source.binVal true op
      (.int x hx : Source.Val E.layout (.int U)) (.int y hy))
    pure (Source.RVal.val v)).run s = _
  simp only [Source.binVal,spec]

theorem source_success (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (U : Source.IntTy) (op : Source.BinOp) (f : Int → Int → Int)
    (notAnd : op ≠ .and) (notOr : op ≠ .or)
    (a b : Source.Idx Γ (.int U)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : s.1.get a = .int x hx) (hb : s.1.get b = .int y hy)
    (spec : Source.intBin (D := E.layout) U true op x y = Source.intRes U true (f x y))
    (fits : U.lo ≤ f x y ∧ f x y ≤ U.hi) :
    (Source.evalE G {F with checked := true} (fuel+3)
      (.binary op (.local a) (.local b))).run s =
      (.ok (.val (.int (f x y) fits)),s) := by
  rw [source_run G F fuel s U op f notAnd notOr a b x y hx hy ha hb spec]
  simp only [Source.intRes,dif_pos fits]
  rfl

theorem source_overflow (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (U : Source.IntTy) (op : Source.BinOp) (f : Int → Int → Int)
    (notAnd : op ≠ .and) (notOr : op ≠ .or)
    (a b : Source.Idx Γ (.int U)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : s.1.get a = .int x hx) (hb : s.1.get b = .int y hy)
    (spec : Source.intBin (D := E.layout) U true op x y = Source.intRes U true (f x y))
    (outside : ¬ (U.lo ≤ f x y ∧ f x y ≤ U.hi)) :
    (Source.evalE G {F with checked := true} (fuel+3)
      (.binary op (.local a) (.local b))).run s =
      (.error (.revert (Source.panicData .arithmetic)),s) := by
  rw [source_run G F fuel s U op f notAnd notOr a b x y hx hy ha hb spec]
  simp only [Source.intRes,dif_neg outside,if_true,Source.panic]
  rfl

end Solidity.Backend.PrimitivePackets.CheckedBinary
