import SolidityBridge.RoadmapV15.P10.SignedGeConsumer
import Solidity.Backend.PrimitivePackets.Comparisons.LocalReads
import Solidity.Backend.PrimitivePackets.SignedDiv.Origin
import Solidity.Backend.Scalar.SignedDivision

/-! Published Source-local int256 comparisons to constructed fetched bodies.
No physical operand-loading, source admission or compiler-prefix origin claim. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedSignedOrder
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.SignedDiv
namespace Cmp
export Solidity.Backend.PrimitivePackets.Comparisons (expression source_run)
end Cmp

theorem ge_flag (a b : PrimTy.int.Denote) :
    Scalar.flag (!(decide ((Scalar.encodeValue .int a).toInt < (Scalar.encodeValue .int b).toInt))) =
      Scalar.flag (decide (b.val≤a.val)) := by
  simp only [Scalar.encode_int_toInt,←decide_not,Int.not_lt]

theorem lt_fetched {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int T)) (a b : PrimTy.int.Denote)
    (readLeft : s.1.get left=sourceValue a) (readRight : s.1.get right=sourceValue b)
    (valid : Array UInt256) (site : Site .SLT) (tail : Scalar.Stack)
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .int a::Scalar.encodeValue .int b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((Scalar.flag (decide (a.val<b.val))::tail).map (fun z=>UInt256.mk z.toFin))
    (Source.evalE G F (sfuel+3) (Cmp.expression .lt true left right)).run s=
      (.ok (.val (.bool (decide (a.val<b.val)))),s) ∧
    Assembly.driverSteps 1 (nfuel+2) valid input=.ok next ∧
    EVM.X (nfuel+2) valid input=EVM.X (nfuel+1) valid next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have src := Cmp.source_run G F sfuel s .lt true left right a.val b.val (range a) (range b) readLeft readRight
  have native := signed_lt_agreement valid site (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) tail room gas nfuel
  dsimp only at native
  rw [Scalar.encode_int_toInt,Scalar.encode_int_toInt] at native
  exact ⟨src,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem ge_fetched {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int T)) (a b : PrimTy.int.Denote)
    (readLeft : s.1.get left=sourceValue a) (readRight : s.1.get right=sourceValue b)
    (valid : Array UInt256) (seed : EVM.State) (before after : Backend.Program) (tail : Scalar.Stack)
    (fits : (Backend.encode (before++[.op .SLT])).length<UInt256.size)
    (room : tail.length+2≤1024) (gas : 6≤seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := signedGeInput seed before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) tail
    let next := signedGeOutput seed before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) tail
    (Source.evalE G F (sfuel+3) (Cmp.expression .ge true left right)).run s=
      (.ok (.val (.bool (decide (b.val≤a.val)))),s) ∧
    Assembly.driverSteps 2 (nfuel+3) valid input=.ok next ∧
    EVM.X (nfuel+3) valid input=EVM.X (nfuel+1) valid next ∧
    next.stack=(Scalar.flag (decide (b.val≤a.val))::tail).map (fun z=>UInt256.mk z.toFin) ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return ∧
    next.gasAvailable.toNat=seed.gasAvailable.toNat-6 := by
  have src := Cmp.source_run G F sfuel s .ge true left right a.val b.val (range a) (range b) readLeft readRight
  have native := signed_ge_execution valid seed before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) tail fits room gas nfuel
  have frame := signed_ge_frame seed before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) tail
  rw [ge_flag] at frame
  exact ⟨src,native.2.1,native.2.2,frame.2.2.2.2.1,frame.1,rfl,rfl,rfl,
    signed_ge_debit seed before after _ _ tail gas⟩

#print axioms ge_flag
#print axioms lt_fetched
#print axioms ge_fetched
end SolidityBridge.RoadmapV15.P10.PublishedSignedOrder
