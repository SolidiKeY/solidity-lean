import SolidityBridge.RoadmapV15.P10.PublishedSignedOrder
import SolidityBridge.RoadmapV15.P10.SignedGeControls
import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Both-pipeline signed comparison clients in independent populated native
States. Source-local evaluation does not supply invocation/physical origin. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedSignedOrderControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.SignedDiv
open PublishedSignedOrder
open WordPushFixtures (seed before after spill u accounts)
namespace Fixture
export Solidity.Backend.PrimitivePackets.SignedMod.Controls (E globals frame)
end Fixture

def source (a b : PrimTy.int.Denote) : Source.EMState Fixture.E [.int T,.int T] :=
  (.cons (sourceValue a) (.cons (sourceValue b) .nil),Source.St.init Fixture.E)
def n (v : Int) (h : PrimTy.int.inRange v=true) : PrimTy.int.Denote := ⟨v,h⟩

private theorem lt_shape (perm : Bool) (a b : PrimTy.int.Denote) :
    (Assembly.chargedPrepare (SignedGeControls.ltInput 6 perm (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill) 3).replaceStackAndIncrPC
      ((Scalar.flag (decide (a.val<b.val))::spill).map (fun z=>UInt256.mk z.toFin))=
      SignedGeControls.ltExpected perm (Scalar.flag (decide (a.val<b.val))) (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill := by
  simp only [SignedGeControls.ltExpected,SignedGeControls.ltInput,SignedGeControls.ltSite,
    modularSite,Site.state,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.before,WordPushFixtures.u,
    Backend.encode_cons,Backend.encode_nil,Instr.encode,List.length_append,List.length_cons,List.length_nil]
  rfl

private theorem ge_shape (perm : Bool) (a b : PrimTy.int.Denote) :
    signedGeOutput (seed 6 perm) before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill=
      SignedGeControls.expected perm (Scalar.flag (decide (b.val≤a.val))) (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill := by
  have gasEq : (signedGeOutput (seed 6 perm) before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill).gasAvailable=u 0 := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact signed_ge_debit (seed 6 perm) before after _ _ spill (by change 6≤6;decide)
  change ({signedGeInput (seed 6 perm) before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill with
    pc:=u 5,gasAvailable:=(signedGeOutput (seed 6 perm) before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill).gasAvailable,
    execLength:=43,stack:=(Scalar.flag (!(decide ((Scalar.encodeValue .int a).toInt<(Scalar.encodeValue .int b).toInt)))::spill).map
      (fun z=>UInt256.mk z.toFin)} : EVM.State)=_
  rw [gasEq,ge_flag]
  rfl

theorem lt_client (pipeline : Roadmap.Pipeline) (checked perm : Bool) (a b : PrimTy.int.Denote) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (Cmp.expression .lt true .here (.there .here))).run (source a b)=
      (.ok (.val (.bool (decide (a.val<b.val)))),source a b) ∧
    Assembly.driverSteps 1 2 #[]
      (SignedGeControls.ltInput 6 perm (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill)=
      .ok (SignedGeControls.ltExpected perm (Scalar.flag (decide (a.val<b.val)))
        (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill) ∧
    EVM.X 2 #[] (SignedGeControls.ltInput 6 perm (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill)=
      EVM.X 1 #[] (SignedGeControls.ltExpected perm (Scalar.flag (decide (a.val<b.val)))
        (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill) := by
  have h := lt_fetched (Fixture.globals pipeline) (Fixture.frame checked) 0 (source a b)
    .here (.there .here) a b rfl rfl #[] (SignedGeControls.ltSite 6 perm) spill (by decide) (by change 3≤6;decide) 0
  dsimp only at h
  have shape := lt_shape perm a b
  simp only [SignedGeControls.ltInput] at shape
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem ge_client (pipeline : Roadmap.Pipeline) (checked perm : Bool) (a b : PrimTy.int.Denote) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (Cmp.expression .ge true .here (.there .here))).run (source a b)=
      (.ok (.val (.bool (decide (b.val≤a.val)))),source a b) ∧
    Assembly.driverSteps 2 3 #[]
      (signedGeInput (seed 6 perm) before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill)=
      .ok (SignedGeControls.expected perm (Scalar.flag (decide (b.val≤a.val)))
        (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill) ∧
    EVM.X 3 #[] (signedGeInput (seed 6 perm) before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill)=
      EVM.X 1 #[] (SignedGeControls.expected perm (Scalar.flag (decide (b.val≤a.val)))
        (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) spill) := by
  have h := ge_fetched (Fixture.globals pipeline) (Fixture.frame checked) 0 (source a b)
    .here (.there .here) a b rfl rfl #[] (seed 6 perm) before after spill (by decide) (by decide) (by change 6≤6;decide) 0
  dsimp only at h
  rw [ge_shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem negative_and_equal (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (Cmp.expression .lt true .here (.there .here))).run (source (n (-7) (by decide)) (n 7 (by decide)))=
      (.ok (.val (.bool true)),source (n (-7) (by decide)) (n 7 (by decide))) ∧
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (Cmp.expression .ge true .here (.there .here))).run (source (n (-7) (by decide)) (n (-7) (by decide)))=
      (.ok (.val (.bool true)),source (n (-7) (by decide)) (n (-7) (by decide))) ∧
    Assembly.driverSteps 2 3 #[]
      (signedGeInput (seed 6 perm) before after (Scalar.encodeValue .int (n 7 (by decide)))
        (Scalar.encodeValue .int (n (-7) (by decide))) spill)=
      .ok (SignedGeControls.expected perm 1 (Scalar.encodeValue .int (n 7 (by decide)))
        (Scalar.encodeValue .int (n (-7) (by decide))) spill) := by
  exact ⟨(lt_client pipeline checked perm (n (-7) (by decide)) (n 7 (by decide))).1,
    (ge_client pipeline checked perm (n (-7) (by decide)) (n (-7) (by decide))).1,
    (ge_client pipeline checked perm (n 7 (by decide)) (n (-7) (by decide))).2.1⟩

theorem minimum_client (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    Assembly.driverSteps 1 2 #[]
      (SignedGeControls.ltInput 6 perm (Scalar.encodeValue .int Scalar.minimumInt) (Scalar.encodeValue .int (n 0 (by decide))) spill)=
      .ok (SignedGeControls.ltExpected perm 1 (Scalar.encodeValue .int Scalar.minimumInt) (Scalar.encodeValue .int (n 0 (by decide))) spill) ∧
    Assembly.driverSteps 2 3 #[]
      (signedGeInput (seed 6 perm) before after (Scalar.encodeValue .int Scalar.minimumInt) (Scalar.encodeValue .int Scalar.minimumInt) spill)=
      .ok (SignedGeControls.expected perm 1 (Scalar.encodeValue .int Scalar.minimumInt) (Scalar.encodeValue .int Scalar.minimumInt) spill) := by
  exact ⟨(lt_client pipeline checked perm Scalar.minimumInt (n 0 (by decide))).2.1,
    (ge_client pipeline checked perm Scalar.minimumInt Scalar.minimumInt).2.1⟩

theorem short_horizons (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 0
      (Cmp.expression .ge true .here (.there .here))).run (source (n (-7) (by decide)) (n 7 (by decide)))=
      (.error .timeout,source (n (-7) (by decide)) (n 7 (by decide))) ∧
    Assembly.driverSteps 2 1 #[]
      (signedGeInput (seed 6 perm) before after (Scalar.encodeValue .int (n (-7) (by decide)))
        (Scalar.encodeValue .int (n 7 (by decide))) spill)=.error .OutOfFuel := by
  exact ⟨rfl,rfl⟩

theorem complete_observation (perm : Bool) :
    let a := Scalar.encodeValue .int (n (-7) (by decide))
    let b := Scalar.encodeValue .int (n 7 (by decide))
    let lt := SignedGeControls.ltExpected perm 1 a b spill
    let ge := SignedGeControls.expected perm 0 a b spill
    lt.stack=[u 1,u 258,u 513] ∧ ge.stack=[u 0,u 258,u 513] ∧
    lt.stack≠[u 0,u 258,u 513] ∧ lt.stack≠[u 1,u 513,u 258] ∧
    a.toNat>b.toNat ∧
    lt.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x12,0x00] ∧
    ge.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x12,0x15,0x00] ∧
    lt.pc=u 4 ∧ ge.pc=u 5 ∧ lt.gasAvailable=u 3 ∧ ge.gasAvailable=u 0 ∧
    lt.execLength=42 ∧ ge.execLength=43 ∧
    ge.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    ge.returnData.data.toList=[0xcc,0xdd] ∧ ge.H_return.data.toList=[0xee,0xff] ∧
    ge.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    ge.accountMap=accounts ∧ ge.σ₀=accounts := by
  refine ⟨rfl,rfl,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 1,u 258,u 513]≠[u 0,u 258,u 513];decide
  · change [u 1,u 258,u 513]≠[u 1,u 513,u 258];decide
  · change (Scalar.encodeValue .int (n (-7) (by decide))).toNat > (Scalar.encodeValue .int (n 7 (by decide))).toNat;decide

#print axioms lt_client
#print axioms ge_client
#print axioms negative_and_equal
#print axioms minimum_client
#print axioms short_horizons
#print axioms complete_observation
end SolidityBridge.RoadmapV15.P10.PublishedSignedOrderControls
