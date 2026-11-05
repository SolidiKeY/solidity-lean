import Solidity.Lowering.V07.SourceReads
import Solidity.Backend.Scalar.SignedGuards

/-! Independent Source-local int256 division origin. Both pipeline orders use
actual pure local reads. Fuel, Source frame and initial state remain explicit;
no desired execution or supplied compiler certificate is an origin premise. -/
namespace Solidity.Backend.PrimitivePackets.SignedDiv
open Solidity.Lowering.V07
abbrev T : Source.IntTy := ⟨true,256,by decide⟩

theorem range (v : PrimTy.int.Denote) : T.lo≤v.val ∧ v.val≤T.hi := by
 first | (solve | simp only) | (solve | decide) | (solve | omega) | (solve | rfl) | skip
 have h := Backend.Scalar.int_range v
 change -((2^255:Nat):Int)≤v.val ∧ v.val≤((2^255:Nat):Int)-1
 omega

def sourceValue {D : Source.Layout} (v : PrimTy.int.Denote) : Source.Val D (.int T) :=
 .int v.val (range v)

theorem locals_origin {E : Source.Env} {Γ : Source.RCtx}
 (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
 (i j : Source.Idx Γ (.int T)) (a b : PrimTy.int.Denote)
 (left : s.1.get i=sourceValue a) (right : s.1.get j=sourceValue b) :
 (Source.evalE G F (fuel+3) (.binary .div (.local i) (.local j))).run s=
 ((Source.binVal F.checked .div (sourceValue a) (sourceValue b)).map Source.RVal.val,s) := by
 first | (solve | simp only) | (solve | decide) | (solve | omega) | (solve | rfl) | skip
 rw [Source.evalE]
 simp only [reduceCtorEq,decide_false,Bool.false_or,Bool.false_eq_true,if_false]
 rw [Source.Hoare.run_bind,source_local_pair G F fuel s T i j a.val b.val (range a) (range b) left right]
 change (do
   let v ← Source.EM.lift (Source.binVal F.checked .div (sourceValue a) (sourceValue b))
   pure (Source.RVal.val v)).run s=_
 cases h : Source.binVal F.checked .div (sourceValue a) (sourceValue b) <;> rfl

theorem source_zero {D : Source.Layout} (checked : Bool) (a b : PrimTy.int.Denote)
 (zero : b.val=0) : Source.binVal checked .div (sourceValue a : Source.Val D (.int T)) (sourceValue b)=
 Source.panic .divZero := by
 first | (solve | simp only [sourceValue,Source.binVal,Source.intBin,zero,if_true]) | (solve | decide) | (solve | omega) | (solve | rfl)

theorem source_overflow {D : Source.Layout} (a b : PrimTy.int.Denote)
 (minimum : a.val=-((2^255:Nat):Int)) (minusOne : b.val = -1) :
 Source.binVal true .div (sourceValue a : Source.Val D (.int T)) (sourceValue b)=Source.panic .arithmetic := by
 first | (solve | simp only [sourceValue,Source.binVal,Source.intBin,minimum,minusOne]) | (solve | decide) | (solve | omega) | (solve | rfl) | skip
 simp only [sourceValue,Source.binVal,Source.intBin,minimum,minusOne]
 first | rfl | (decide +kernel +revert)

theorem source_unchecked_overflow {D : Source.Layout} (a b : PrimTy.int.Denote)
 (minimum : a.val=-((2^255:Nat):Int)) (minusOne : b.val = -1) :
 Source.binVal false .div (sourceValue a : Source.Val D (.int T)) (sourceValue b)=
 .ok (sourceValue Backend.Scalar.minimumInt) := by
 first | (solve | simp only [sourceValue,Source.binVal,Source.intBin,minimum,minusOne]) | (solve | decide) | (solve | omega) | (solve | rfl) | skip
 simp only [sourceValue,Source.binVal,Source.intBin,minimum,minusOne]
 first | rfl | (decide +kernel +revert)

theorem quotient_range (a b : PrimTy.int.Denote) (nonzero : b.val≠0)
 (ordinary : ¬ (a.val=-((2^255:Nat):Int) ∧ b.val = -1)) :
 T.lo≤a.val.tdiv b.val ∧ a.val.tdiv b.val≤T.hi := by
 first | (solve | simp only) | (solve | decide) | (solve | omega) | (solve | rfl) | skip
 have h := (Evm.tdiv_range (Backend.Scalar.int_range a) nonzero).mpr ordinary
 unfold Evm.H at h
 change -((2^255:Nat):Int)≤a.val.tdiv b.val ∧ a.val.tdiv b.val≤((2^255:Nat):Int)-1
 omega

def quotient (a b : PrimTy.int.Denote) (nonzero : b.val≠0)
 (ordinary : ¬ (a.val=-((2^255:Nat):Int) ∧ b.val = -1)) : PrimTy.int.Denote :=
 integerValue T (a.val.tdiv b.val) (quotient_range a b nonzero ordinary)

theorem source_ordinary {D : Source.Layout} (checked : Bool) (a b : PrimTy.int.Denote)
 (nonzero : b.val≠0) (ordinary : ¬ (a.val=-((2^255:Nat):Int) ∧ b.val = -1)) :
 Source.binVal checked .div (sourceValue a : Source.Val D (.int T)) (sourceValue b)=
 .ok (sourceValue (quotient a b nonzero ordinary)) := by
 first | (solve | simp only [sourceValue,Source.binVal,Source.intBin,nonzero,if_false]) | (solve | decide) | (solve | omega) | (solve | rfl) | skip
 simp only [sourceValue,Source.binVal,Source.intBin,nonzero,if_false,Source.intRes,
  dif_pos (quotient_range a b nonzero ordinary)]
 rfl
end Solidity.Backend.PrimitivePackets.SignedDiv
