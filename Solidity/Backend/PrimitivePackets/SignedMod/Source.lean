import Solidity.Lowering.V07.SourceReads
import Solidity.Evm.Signed

/-! Independent signed-256 local origins. The horizon and the complete Source
state are retained. Both pipelines and checked/unchecked frames are quantified;
only pure local operands are covered. No desired evaluation is a premise. -/
namespace Solidity.Backend.PrimitivePackets.SignedMod
open Solidity.Lowering.V07

def ty : Source.IntTy := ⟨true, 256, by decide⟩

abbrev Range (x : Int) : Prop := ty.lo ≤ x ∧ x ≤ ty.hi

def lower (x : Int) (hx : Range x) : PrimTy.int.Denote := integerValue ty x hx

/-- The result bound is derived from the original divisor range, not assumed. -/
theorem remainder_range (x y : Int) (hy : Range y) (nonzero : y ≠ 0) :
    Range (x.tmod y) := by
  have divisor : -(Evm.H : Int) ≤ y ∧ y < Evm.H := by
    change -(Evm.H : Int) ≤ y ∧ y ≤ (Evm.H : Int) - 1 at hy
    omega
  have result := Evm.tmod_range (x := x) divisor nonzero
  change -(Evm.H : Int) ≤ x.tmod y ∧ x.tmod y ≤ (Evm.H : Int) - 1
  omega

theorem source_nonzero {D : Source.Layout} (checked : Bool) (x y : Int)
    (hx : Range x) (hy : Range y) (nonzero : y ≠ 0) :
    Source.binVal checked .mod (.int x hx : Source.Val D (.int ty)) (.int y hy) =
      .ok (.int (x.tmod y) (remainder_range x y hy nonzero)) := by
  simp only [Source.binVal, Source.intBin, nonzero, if_false, Source.intRes,
    remainder_range x y hy nonzero]
  rfl

theorem source_zero {D : Source.Layout} (checked : Bool) (x : Int)
    (hx : Range x) (hz : Range 0) :
    Source.binVal checked .mod (.int x hx : Source.Val D (.int ty)) (.int 0 hz) =
      .error (.revert (Source.panicData .divZero)) := rfl

/-- Actual evalE and evalPair; neither operand execution is supplied. -/
theorem source_locals {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (state : Source.EMState E Γ)
    (a d : Source.Idx Γ (.int ty)) (x y : Int) (hx : Range x) (hy : Range y)
    (readA : state.1.get a = .int x hx) (readD : state.1.get d = .int y hy) :
    (Source.evalE G F (fuel + 3) (.binary .mod (.local a) (.local d))).run state =
      ((Source.binVal F.checked .mod (.int x hx : Source.Val E.layout (.int ty))
        (.int y hy)).map Source.RVal.val, state) := by
  rw [Source.evalE]
  simp only [reduceCtorEq, decide_false, Bool.false_or, Bool.false_eq_true, if_false]
  rw [Source.Hoare.run_bind, source_local_pair G F fuel state ty a d x y hx hy readA readD]
  change (do
    let v ← Source.EM.lift (Source.binVal F.checked .mod
      (.int x hx : Source.Val E.layout (.int ty)) (.int y hy))
    pure (Source.RVal.val v)).run state = _
  generalize Source.binVal F.checked .mod (.int x hx : Source.Val E.layout (.int ty)) (.int y hy) = result
  cases result <;> rfl

theorem source_locals_nonzero {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (state : Source.EMState E Γ)
    (a d : Source.Idx Γ (.int ty)) (x y : Int) (hx : Range x) (hy : Range y)
    (readA : state.1.get a = .int x hx) (readD : state.1.get d = .int y hy)
    (nonzero : y ≠ 0) :
    (Source.evalE G F (fuel + 3) (.binary .mod (.local a) (.local d))).run state =
      (.ok (.val (.int (x.tmod y) (remainder_range x y hy nonzero))), state) := by
  rw [source_locals G F fuel state a d x y hx hy readA readD,
    source_nonzero F.checked x y hx hy nonzero]
  rfl

theorem source_locals_zero {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (state : Source.EMState E Γ)
    (a d : Source.Idx Γ (.int ty)) (x : Int) (hx : Range x) (hz : Range 0)
    (readA : state.1.get a = .int x hx) (readD : state.1.get d = .int 0 hz) :
    (Source.evalE G F (fuel + 3) (.binary .mod (.local a) (.local d))).run state =
      (.error (.revert (Source.panicData .divZero)), state) := by
  rw [source_locals G F fuel state a d x 0 hx hz readA readD,
    source_zero F.checked x hx hz]
  rfl

/-- Signed remainder follows the dividend sign and ignores the divisor sign. -/
theorem negative_dividend (x y : Int) : (-x).tmod y = -(x.tmod y) := Int.neg_tmod x y

theorem negative_divisor (x y : Int) : x.tmod (-y) = x.tmod y := Int.tmod_neg x y

/-- Unlike signed division, min divided by -1 is ordinary successful remainder zero. -/
theorem minimum_remainder_neg_one : (-(Evm.H : Int)).tmod (-1) = 0 := by
  rw [Int.tmod_neg, Int.tmod_one]

end Solidity.Backend.PrimitivePackets.SignedMod
