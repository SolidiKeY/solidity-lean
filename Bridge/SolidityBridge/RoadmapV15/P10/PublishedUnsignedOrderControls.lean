import SolidityBridge.RoadmapV15.P10.PublishedUnsignedOrder
import SolidityBridge.RoadmapV15.P10.UnsignedOrderControls
import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Independent full-State Source/native uint256 comparison clients.
No invocation/physical load or source-to-code origin is inferred. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedUnsignedOrderControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.UnsignedDiv (sourceUInt)
open PublishedUnsignedOrder
open WordPushFixtures (spill u accounts)
namespace Fixture
export Solidity.Backend.PrimitivePackets.SignedMod.Controls (E globals frame)
end Fixture

def source (a b : PrimTy.uint.Denote) : Source.EMState Fixture.E [.int Source.IntTy.u256,.int Source.IntTy.u256] :=
  (.cons (sourceUInt Fixture.E.layout a) (.cons (sourceUInt Fixture.E.layout b) .nil),Source.St.init Fixture.E)
def n (v : Int) (h : PrimTy.uint.inRange v=true) : PrimTy.uint.Denote := ⟨v,h⟩

private theorem shape (op : Backend.Op) (perm : Bool) (result a b : Scalar.Word) :
    (Assembly.chargedPrepare (UnsignedOrderControls.input op 6 perm a b spill) 3).replaceStackAndIncrPC
      ((result::spill).map (fun z=>UInt256.mk z.toFin))=
      UnsignedOrderControls.expected op perm result a b spill := by
  simp only [UnsignedOrderControls.expected,UnsignedOrderControls.input,UnsignedOrderControls.site,
    modularSite,Site.state,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.before,WordPushFixtures.u,
    Backend.encode_cons,Backend.encode_nil,Instr.encode,List.length_append,List.length_cons,List.length_nil]
  rfl

theorem lt_client (pipeline : Roadmap.Pipeline) (checked perm : Bool) (a b : PrimTy.uint.Denote) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (Cmp.expression .lt false .here (.there .here))).run (source a b)=
      (.ok (.val (.bool (decide (a.val<b.val)))),source a b) ∧
    Assembly.driverSteps 1 2 #[]
      (UnsignedOrderControls.input .LT 6 perm (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill)=
      .ok (UnsignedOrderControls.expected .LT perm (Scalar.flag (decide (a.val<b.val)))
        (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill) ∧
    EVM.X 2 #[] (UnsignedOrderControls.input .LT 6 perm (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill)=
      EVM.X 1 #[] (UnsignedOrderControls.expected .LT perm (Scalar.flag (decide (a.val<b.val)))
        (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill) := by
  have h := lt_fetched (Fixture.globals pipeline) (Fixture.frame checked) 0 (source a b)
    .here (.there .here) a b rfl rfl #[] (UnsignedOrderControls.site .LT 6 perm) spill (by decide) (by change 3≤6;decide) 0
  dsimp only at h
  have hs := shape .LT perm (Scalar.flag (decide (a.val<b.val))) (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b)
  simp only [UnsignedOrderControls.input] at hs
  rw [hs] at h
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem gt_client (pipeline : Roadmap.Pipeline) (checked perm : Bool) (a b : PrimTy.uint.Denote) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (Cmp.expression .gt false .here (.there .here))).run (source a b)=
      (.ok (.val (.bool (decide (b.val<a.val)))),source a b) ∧
    Assembly.driverSteps 1 2 #[]
      (UnsignedOrderControls.input .GT 6 perm (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill)=
      .ok (UnsignedOrderControls.expected .GT perm (Scalar.flag (decide (b.val<a.val)))
        (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill) ∧
    EVM.X 2 #[] (UnsignedOrderControls.input .GT 6 perm (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill)=
      EVM.X 1 #[] (UnsignedOrderControls.expected .GT perm (Scalar.flag (decide (b.val<a.val)))
        (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill) := by
  have h := gt_fetched (Fixture.globals pipeline) (Fixture.frame checked) 0 (source a b)
    .here (.there .here) a b rfl rfl #[] (UnsignedOrderControls.site .GT 6 perm) spill (by decide) (by change 3≤6;decide) 0
  dsimp only at h
  have hs := shape .GT perm (Scalar.flag (decide (b.val<a.val))) (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b)
  simp only [UnsignedOrderControls.input] at hs
  rw [hs] at h
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem boundary_clients (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    Assembly.driverSteps 1 2 #[]
      (UnsignedOrderControls.input .GT 6 perm (Scalar.encodeValue .uint (n ((2^256:Nat)-1) (by decide))) (Scalar.encodeValue .uint (n 0 (by decide))) spill)=
      .ok (UnsignedOrderControls.expected .GT perm 1 (Scalar.encodeValue .uint (n ((2^256:Nat)-1) (by decide))) (Scalar.encodeValue .uint (n 0 (by decide))) spill) ∧
    Assembly.driverSteps 1 2 #[]
      (UnsignedOrderControls.input .LT 6 perm (Scalar.encodeValue .uint (n 0 (by decide))) (Scalar.encodeValue .uint (n (2^255:Nat) (by decide))) spill)=
      .ok (UnsignedOrderControls.expected .LT perm 1 (Scalar.encodeValue .uint (n 0 (by decide))) (Scalar.encodeValue .uint (n (2^255:Nat) (by decide))) spill) ∧
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (Cmp.expression .gt false .here (.there .here))).run
      (source (n ((2^256:Nat)-1) (by decide)) (n ((2^256:Nat)-1) (by decide)))=
      (.ok (.val (.bool false)),source (n ((2^256:Nat)-1) (by decide)) (n ((2^256:Nat)-1) (by decide))) := by
  exact ⟨(gt_client pipeline checked perm (n ((2^256:Nat)-1) (by decide)) (n 0 (by decide))).2.1,
    (lt_client pipeline checked perm (n 0 (by decide)) (n (2^255:Nat) (by decide))).2.1,
    (gt_client pipeline checked perm (n ((2^256:Nat)-1) (by decide)) (n ((2^256:Nat)-1) (by decide))).1⟩

theorem short_horizons (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 0
      (Cmp.expression .gt false .here (.there .here))).run (source (n 513 (by decide)) (n 7 (by decide)))=
      (.error .timeout,source (n 513 (by decide)) (n 7 (by decide))) ∧
    Assembly.driverSteps 1 1 #[]
      (UnsignedOrderControls.input .GT 6 perm (Scalar.encodeValue .uint (n 513 (by decide))) (Scalar.encodeValue .uint (n 7 (by decide))) spill)=.error .OutOfFuel := by
  exact ⟨rfl,rfl⟩

theorem complete_observation (perm : Bool) :
    let a := Scalar.encodeValue .uint (n (2^255:Nat) (by decide))
    let b := Scalar.encodeValue .uint (n 7 (by decide))
    let lt := UnsignedOrderControls.expected .LT perm 0 a b spill
    let gt := UnsignedOrderControls.expected .GT perm 1 a b spill
    lt.stack=[u 0,u 258,u 513] ∧ gt.stack=[u 1,u 258,u 513] ∧
    gt.stack≠[u 0,u 258,u 513] ∧ gt.stack≠[u 1,u 513,u 258] ∧
    a.toInt<b.toInt ∧
    lt.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x10,0x00] ∧
    gt.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x11,0x00] ∧
    gt.pc=u 4 ∧ gt.gasAvailable=u 3 ∧ gt.execLength=42 ∧
    gt.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    gt.returnData.data.toList=[0xcc,0xdd] ∧ gt.H_return.data.toList=[0xee,0xff] ∧
    gt.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    gt.accountMap=accounts ∧ gt.σ₀=accounts := by
  refine ⟨rfl,rfl,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 1,u 258,u 513]≠[u 0,u 258,u 513];decide
  · change [u 1,u 258,u 513]≠[u 1,u 513,u 258];decide
  · change (Scalar.encodeValue .uint (n (2^255:Nat) (by decide))).toInt < (Scalar.encodeValue .uint (n 7 (by decide))).toInt;decide

#print axioms lt_client
#print axioms gt_client
#print axioms boundary_clients
#print axioms short_horizons
#print axioms complete_observation
end SolidityBridge.RoadmapV15.P10.PublishedUnsignedOrderControls
