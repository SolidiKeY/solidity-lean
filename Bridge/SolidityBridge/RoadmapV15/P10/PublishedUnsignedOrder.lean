import SolidityBridge.RoadmapV15.P10.UnsignedOrderConsumer
import Solidity.Backend.PrimitivePackets.Comparisons.LocalReads
import Solidity.Backend.PrimitivePackets.UnsignedDiv.Data

/-! Published uint256 local reads to constructed charged fetched LT/GT bodies.
The Scalar certificates supply representation transport, not a simulation premise. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedUnsignedOrder
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
namespace Cmp
export Solidity.Backend.PrimitivePackets.Comparisons (expression source_run)
end Cmp
open Solidity.Backend.PrimitivePackets.UnsignedDiv (sourceUInt)

theorem source_range (v : PrimTy.uint.Denote) :
    Source.IntTy.u256.lo≤v.val ∧ v.val≤Source.IntTy.u256.hi := by
  have h := Scalar.uint_range v
  change 0≤v.val ∧ v.val≤((2^256:Nat):Int)-1
  omega

theorem lt_flag (a b : PrimTy.uint.Denote) :
    Scalar.flag (decide ((Scalar.encodeValue .uint a).toNat<(Scalar.encodeValue .uint b).toNat))=
      Scalar.flag (decide (a.val<b.val)) := by
  have h := Scalar.uintLt.correct a b []
  change some [Scalar.flag (decide ((Scalar.encodeValue .uint a).toNat<(Scalar.encodeValue .uint b).toNat))]=
    some [Scalar.flag (decide (a.val<b.val))] at h
  exact (List.cons.inj (Option.some.inj h)).1

theorem gt_flag (a b : PrimTy.uint.Denote) :
    Scalar.flag (decide ((Scalar.encodeValue .uint b).toNat<(Scalar.encodeValue .uint a).toNat))=
      Scalar.flag (decide (b.val<a.val)) := by
  have h := Scalar.uintGt.correct a b []
  change some [Scalar.flag (decide ((Scalar.encodeValue .uint b).toNat<(Scalar.encodeValue .uint a).toNat))]=
    some [Scalar.flag (decide (b.val<a.val))] at h
  exact (List.cons.inj (Option.some.inj h)).1

theorem lt_fetched {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int Source.IntTy.u256)) (a b : PrimTy.uint.Denote)
    (readLeft : s.1.get left=sourceUInt E.layout a) (readRight : s.1.get right=sourceUInt E.layout b)
    (valid : Array UInt256) (site : Site .LT) (tail : Scalar.Stack)
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((Scalar.flag (decide (a.val<b.val))::tail).map (fun z=>UInt256.mk z.toFin))
    (Source.evalE G F (sfuel+3) (Cmp.expression .lt false left right)).run s=
      (.ok (.val (.bool (decide (a.val<b.val)))),s) ∧
    Assembly.driverSteps 1 (nfuel+2) valid input=.ok next ∧
    EVM.X (nfuel+2) valid input=EVM.X (nfuel+1) valid next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have src := Cmp.source_run G F sfuel s .lt false left right a.val b.val (source_range a) (source_range b) readLeft readRight
  have native := unsigned_lt_agreement valid site (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail room gas nfuel
  dsimp only at native
  rw [lt_flag] at native
  exact ⟨src,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem gt_fetched {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int Source.IntTy.u256)) (a b : PrimTy.uint.Denote)
    (readLeft : s.1.get left=sourceUInt E.layout a) (readRight : s.1.get right=sourceUInt E.layout b)
    (valid : Array UInt256) (site : Site .GT) (tail : Scalar.Stack)
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((Scalar.flag (decide (b.val<a.val))::tail).map (fun z=>UInt256.mk z.toFin))
    (Source.evalE G F (sfuel+3) (Cmp.expression .gt false left right)).run s=
      (.ok (.val (.bool (decide (b.val<a.val)))),s) ∧
    Assembly.driverSteps 1 (nfuel+2) valid input=.ok next ∧
    EVM.X (nfuel+2) valid input=EVM.X (nfuel+1) valid next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have src := Cmp.source_run G F sfuel s .gt false left right a.val b.val (source_range a) (source_range b) readLeft readRight
  have native := unsigned_gt_agreement valid site (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail room gas nfuel
  dsimp only at native
  rw [gt_flag] at native
  exact ⟨src,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

#print axioms source_range
#print axioms lt_flag
#print axioms gt_flag
#print axioms lt_fetched
#print axioms gt_fetched
end SolidityBridge.RoadmapV15.P10.PublishedUnsignedOrder
