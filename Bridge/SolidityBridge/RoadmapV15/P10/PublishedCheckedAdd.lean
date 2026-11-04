import SolidityBridge.RoadmapV15.P10.WrappingArithmeticConsumer
import SolidityBridge.RoadmapV15.P10.PublishedUnsignedOrder
import Solidity.Backend.PrimitivePackets.CheckedAdd.Source

/-! Published checked uint256 Source addition versus the raw fetched ADD body.
The overflow mismatch is retained; this is not compiler-guard correspondence. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedCheckedAdd
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.UnsignedDiv (sourceUInt)
open PublishedUnsignedOrder (source_range)
namespace Src
export Solidity.Backend.PrimitivePackets.CheckedAdd (source_success source_overflow)
end Src

theorem addition_word (a b : PrimTy.uint.Denote) :
    Scalar.encodeValue .uint a+Scalar.encodeValue .uint b=BitVec.ofInt 256 (a.val+b.val) := by
  exact (BitVec.ofInt_add a.val b.val).symm

theorem success_fetched {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int Source.IntTy.u256)) (a b : PrimTy.uint.Denote)
    (readLeft : s.1.get left=sourceUInt E.layout a) (readRight : s.1.get right=sourceUInt E.layout b)
    (fits : Source.IntTy.u256.lo≤a.val+b.val ∧ a.val+b.val≤Source.IntTy.u256.hi)
    (valid : Array UInt256) (site : Site .ADD) (tail : Scalar.Stack)
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((BitVec.ofInt 256 (a.val+b.val)::tail).map (fun z=>UInt256.mk z.toFin))
    (Source.evalE G {F with checked:=true} (sfuel+3) (.binary .add (.local left) (.local right))).run s=
      (.ok (.val (.int (a.val+b.val) fits)),s) ∧
    Assembly.driverSteps 1 (nfuel+2) valid input=.ok next ∧
    EVM.X (nfuel+2) valid input=EVM.X (nfuel+1) valid next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have src := Src.source_success G F sfuel s left right a.val b.val (source_range a) (source_range b) readLeft readRight fits
  have native := wrapping_add_agreement valid site (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail room gas nfuel
  dsimp only at native
  rw [addition_word] at native
  exact ⟨src,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem overflow_boundary {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int Source.IntTy.u256)) (a b : PrimTy.uint.Denote)
    (readLeft : s.1.get left=sourceUInt E.layout a) (readRight : s.1.get right=sourceUInt E.layout b)
    (overflow : ¬(Source.IntTy.u256.lo≤a.val+b.val ∧ a.val+b.val≤Source.IntTy.u256.hi))
    (valid : Array UInt256) (site : Site .ADD) (tail : Scalar.Stack)
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((BitVec.ofInt 256 (a.val+b.val)::tail).map (fun z=>UInt256.mk z.toFin))
    (Source.evalE G {F with checked:=true} (sfuel+3) (.binary .add (.local left) (.local right))).run s=
      (.error (.revert (Source.panicData .arithmetic)),s) ∧
    Assembly.driverSteps 1 (nfuel+2) valid input=.ok next ∧
    EVM.X (nfuel+2) valid input=EVM.X (nfuel+1) valid next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have src := Src.source_overflow G F sfuel s left right a.val b.val (source_range a) (source_range b) readLeft readRight overflow
  have native := wrapping_add_agreement valid site (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail room gas nfuel
  dsimp only at native
  rw [addition_word] at native
  exact ⟨src,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

#print axioms addition_word
#print axioms success_fetched
#print axioms overflow_boundary
end SolidityBridge.RoadmapV15.P10.PublishedCheckedAdd
