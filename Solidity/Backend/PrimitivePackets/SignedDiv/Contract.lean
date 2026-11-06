import Solidity.Backend.PrimitivePackets.SignedDiv.Execution

/-! Consume StatefulDivision's full original checked contract, retaining every
numeric stack-capacity premise, while selecting the whole expression publicly
and independently deriving its actual Source-local origin. -/
namespace Solidity.Backend.PrimitivePackets.SignedDiv
open Evm Evm.Memory

theorem checked_contract {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
 (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
 (target : State C Γ) (si sj : Source.Idx srcΓ (.int T)) (i j : Idx Γ (.val .int))
 (a b : PrimTy.int.Denote) (sl : source.1.get si=sourceValue a) (sr : source.1.get sj=sourceValue b)
 (tl : TEnv.get i target.env=a) (tr : TEnv.get j target.env=b)
 {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {m : Machine}
 (input : StateRepr L offset frame F target base m) (saved : List (Fin W))
 (zeroCapacity : Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩)
   ((saved.length+2:Nat):Int)=true)
 (overflowCapacity : Backend.Scalar.stackBound Backend.Scalar.signedDivOverflowTest
   ((saved.length+2:Nat):Int)=true)
 (bodyCapacity : Backend.Scalar.stackBound [.op .SDIV] ((saved.length+2:Nat):Int)=true) :
 (Source.evalE G {SF with checked:=true} (fuel+3) (.binary .div (.local si) (.local sj))).run source=
 ((Source.binVal true .div (sourceValue a) (sourceValue b)).map Source.RVal.val,source) ∧
 ValOutT .int (TRes.ofOpt (BinOp.div.evalT rfl a b))
  (run (selected (C:=C) offset F true i j).code {m with stack:=saved.map Word.val})
  {m with stack:=saved.map Word.val} ∧
 Backend.Scalar.signedDivExecute (Backend.Scalar.encodeValue .int a::Backend.Scalar.encodeValue .int b::
   saved.map (fun w=>BitVec.ofNat 256 w.val))=
 some (Backend.Scalar.signedDivOutcome a b (saved.map (fun w=>BitVec.ofNat 256 w.val))) ∧
 Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2:Nat):Int)=true ∧
 Backend.Scalar.stackBound Backend.Scalar.signedDivOverflowTest ((saved.length+2:Nat):Int)=true ∧
 Backend.Scalar.stackBound [.op .SDIV] ((saved.length+2:Nat):Int)=true := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 exact ⟨locals_origin G {SF with checked:=true} fuel source si sj a b sl sr,
  Backend.Passes.StatefulDivision.int_division (selected (C:=C) offset F true i j) input
   (by exact congrArg Except.ok tl) (by exact congrArg Except.ok tr) saved
   zeroCapacity overflowCapacity bodyCapacity⟩
end Solidity.Backend.PrimitivePackets.SignedDiv
