import Solidity.Lowering.StorageOps.SourceByteStorageCopy

/-! Transport actual primitive byte clearing to the checked Source scalar-range
operation. This concerns logical Source cells, not packed physical bytes. -/
namespace Solidity.Lowering.StorageOps.SourceByteStorageClear
open Solidity

/-- Primitive deletion has the same existing Source operation at each runtime
index, including zero-fuel failure. This does not identify their stored values. -/
theorem range_eq_int {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (fuel : Nat) (path : Source.SPath) (start count : Nat) :
 (Source.deleteRange (E:=E) (Γ:=Γ) frame fuel (.fixedBytes 1 (by decide)) path start count)=
 Source.deleteRange frame fuel (.int Source.IntTy.u256) path start count := by
 induction fuel generalizing start count with
 | zero => simp only [Source.deleteRange]
 | succ fuel ih =>
   cases count with
   | zero => rfl
   | succ count =>
     cases fuel with
     | zero => rfl
     | succ fuel =>
       change (Source.setCell frame (path.go (.index start)) none >>= fun _ =>
         Source.deleteRange frame (fuel+1) (.fixedBytes 1 (by decide)) path (start+1) count)=
         (Source.setCell frame (path.go (.index start)) none >>= fun _ =>
         Source.deleteRange frame (fuel+1) (.int Source.IntTy.u256) path (start+1) count)
       rw [ih]

/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageClear.range_eq_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms range_eq_int
end Solidity.Lowering.StorageOps.SourceByteStorageClear
