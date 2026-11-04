import SolidityBridge.RoadmapV15.P10.PublishedMultiply
import Solidity.Lowering.V07.SignedWordSubtraction

/-! Unchecked int256 subtraction: actual Source locals and canonical wrapped
word versus charged fetched SUB. Physical loading/compiler/world origin stays open. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedSignedSub
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
namespace Src
export Solidity.Lowering.V07.SignedWordSubtraction (ty source_locals_run)
end Src

theorem wrapped_word (v : Int) :
    BitVec.ofInt 256 (Src.ty.wrap v)=BitVec.ofInt 256 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [Src.ty,Solidity.Lowering.V07.SignedWordSubtraction.ty,
    Solidity.Lowering.V07.WordCasts.signed,Source.IntTy.wrap,Source.wrapBits]
  split <;> simp only [BitVec.toNat_ofInt,Int.sub_emod,Int.emod_self,sub_zero,Int.emod_emod]

theorem difference_word (x y : Int) :
    BitVec.ofInt 256 x-BitVec.ofInt 256 y=BitVec.ofInt 256 (x-y) := by
  simp only [Int.sub_eq_add_neg,BitVec.ofInt_add,BitVec.ofInt_neg,BitVec.sub_eq_add_neg]

theorem source_result_word {D : Source.Layout} (x y : Int) :
    (Source.intWrap Src.ty (x-y) : Source.Val D (.int Src.ty)).word.map
      (fun w => (BitVec.ofFin w : Scalar.Word))=some (BitVec.ofInt 256 (x-y)) := by
  change some (BitVec.ofFin (Source.intWord (Src.ty.wrap (x-y)) ))=_
  rw [PublishedMultiply.int_word,wrapped_word]

theorem fetched {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int Src.ty)) (x y : Int)
    (hx : Src.ty.lo≤x ∧ x≤Src.ty.hi) (hy : Src.ty.lo≤y ∧ y≤Src.ty.hi)
    (readLeft : s.1.get left=.int x hx) (readRight : s.1.get right=.int y hy)
    (valid : Array UInt256) (site : Site .SUB) (tail : Scalar.Stack)
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := (modularSite site (BitVec.ofInt 256 x::BitVec.ofInt 256 y::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((BitVec.ofInt 256 (x-y)::tail).map (fun z=>UInt256.mk z.toFin))
    (Source.evalE G {F with checked:=false} (sfuel+3) (.binary .sub (.local left) (.local right))).run s=
      (.ok (.val (Source.intWrap Src.ty (x-y))),s) ∧
    (Source.intWrap Src.ty (x-y) : Source.Val E.layout (.int Src.ty)).word.map
      (fun w => (BitVec.ofFin w : Scalar.Word))=some (BitVec.ofInt 256 (x-y)) ∧
    Assembly.driverSteps 1 (nfuel+2) valid input=.ok next ∧
    EVM.X (nfuel+2) valid input=EVM.X (nfuel+1) valid next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have src := Src.source_locals_run G F sfuel s left right x y hx hy readLeft readRight
  have native := wrapping_sub_agreement valid site (BitVec.ofInt 256 x) (BitVec.ofInt 256 y) tail room gas nfuel
  dsimp only at native
  rw [difference_word] at native
  exact ⟨src,source_result_word x y,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

#print axioms wrapped_word
#print axioms difference_word
#print axioms source_result_word
#print axioms fetched
end SolidityBridge.RoadmapV15.P10.PublishedSignedSub
