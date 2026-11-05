import SolidityBridge.RoadmapV15.P10.WrappingArithmeticConsumer
import SolidityBridge.RoadmapV15.P10.PublishedUnsignedOrder
import Solidity.Lowering.V07.UnsignedMultiplication

/-! Actual Source word observations of unchecked uint256 multiplication versus
charged fetched MUL. Physical operand loading and compiler origin remain open. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedMultiply
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.UnsignedDiv (sourceUInt)
open PublishedUnsignedOrder (source_range)
namespace Src
export Solidity.Lowering.V07.UnsignedMultiplication (source_locals_run)
end Src

theorem int_word (v : Int) : BitVec.ofFin (Source.intWord v)=BitVec.ofInt 256 v := by
  apply BitVec.eq_of_toNat_eq
  change (v % (2^256:Nat)).toNat % 2^256=(BitVec.ofInt 256 v).toNat
  rw [←BitVec.toNat_ofInt]
  exact Nat.mod_eq_of_lt (BitVec.ofInt 256 v).isLt

theorem wrapped_word (v : Int) :
    BitVec.ofInt 256 (Source.IntTy.u256.wrap v)=BitVec.ofInt 256 v := by
  change BitVec.ofInt 256 (v % (2^256:Nat))=BitVec.ofInt 256 v
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt,BitVec.toNat_ofInt,Int.emod_emod]

theorem product_word (a b : PrimTy.uint.Denote) :
    Scalar.encodeValue .uint a*Scalar.encodeValue .uint b=BitVec.ofInt 256 (a.val*b.val) := by
  exact (BitVec.ofInt_mul a.val b.val).symm

theorem source_result_word {D : Source.Layout} (a b : PrimTy.uint.Denote) :
    (Source.intWrap Source.IntTy.u256 (a.val*b.val) : Source.Val D (.int Source.IntTy.u256)).word.map
      (fun w => (BitVec.ofFin w : Scalar.Word))=some (Scalar.encodeValue .uint a*Scalar.encodeValue .uint b) := by
  change some (BitVec.ofFin (Source.intWord (Source.IntTy.u256.wrap (a.val*b.val)) ))=_
  rw [int_word,wrapped_word,product_word]

theorem fetched {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int Source.IntTy.u256)) (a b : PrimTy.uint.Denote)
    (readLeft : s.1.get left=sourceUInt E.layout a) (readRight : s.1.get right=sourceUInt E.layout b)
    (valid : Array UInt256) (site : Site .MUL) (tail : Scalar.Stack)
    (room : tail.length+2≤1024) (gas : 5≤site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      ((BitVec.ofInt 256 (a.val*b.val)::tail).map (fun z=>UInt256.mk z.toFin))
    (Source.evalE G {F with checked:=false} (sfuel+3) (.binary .mul (.local left) (.local right))).run s=
      (.ok (.val (Source.intWrap Source.IntTy.u256 (a.val*b.val))),s) ∧
    (Source.intWrap Source.IntTy.u256 (a.val*b.val) : Source.Val E.layout (.int Source.IntTy.u256)).word.map
      (fun w => (BitVec.ofFin w : Scalar.Word))=some (BitVec.ofInt 256 (a.val*b.val)) ∧
    Assembly.driverSteps 1 (nfuel+2) valid input=.ok next ∧
    EVM.X (nfuel+2) valid input=EVM.X (nfuel+1) valid next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have src := Src.source_locals_run G F sfuel s 256 (by decide) left right a.val b.val (source_range a) (source_range b) readLeft readRight
  have observed := source_result_word (D:=E.layout) a b
  rw [product_word] at observed
  have native := wrapping_mul_agreement valid site (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail room gas nfuel
  dsimp only at native
  rw [product_word] at native
  exact ⟨src,observed,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

#print axioms int_word
#print axioms wrapped_word
#print axioms product_word
#print axioms source_result_word
#print axioms fetched
end SolidityBridge.RoadmapV15.P10.PublishedMultiply
