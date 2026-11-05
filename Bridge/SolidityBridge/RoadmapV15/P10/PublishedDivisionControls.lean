import SolidityBridge.RoadmapV15.P10.PublishedDivision
import SolidityBridge.RoadmapV15.P10.WordPushFixtures
import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Pure-expression Source fixtures and independently populated native body
states. These contexts do not supply invocation or physical operand origin. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedDivisionControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.SignedDiv
open WordPushFixtures (seed u accounts spill before after)
namespace Fixture
export Solidity.Backend.PrimitivePackets.SignedMod.Controls (E globals frame)
end Fixture

def source (a b : PrimTy.int.Denote) : Source.EMState Fixture.E [.int T,.int T] :=
  (.cons (sourceValue a) (.cons (sourceValue b) .nil),Source.St.init Fixture.E)
def site (perm : Bool) : Site .SDIV := ⟨seed 9 perm,before,after,by decide⟩
def input (a b : PrimTy.int.Denote) (perm : Bool) : EVM.State :=
  (modularSite (site perm) (Scalar.encodeValue .int a::Scalar.encodeValue .int b::spill)).state
def expected (value : Int) (perm : Bool) : EVM.State :=
  {(site perm).state with pc:=u 4,gasAvailable:=u 4,execLength:=42,stack:=(BitVec.ofInt 256 value::spill).map (fun w=>UInt256.mk w.toFin)}
def n (v : Int) (h : PrimTy.int.inRange v=true) : PrimTy.int.Denote := ⟨v,h⟩

private theorem expected_shape (a b : PrimTy.int.Denote) (r : Int) (perm : Bool) :
    (Assembly.chargedPrepare (input a b perm) 5).replaceStackAndIncrPC
      ((BitVec.ofInt 256 r::spill).map (fun w=>UInt256.mk w.toFin))=expected r perm := by
  change ({input a b perm with pc:=u 3+u 1,gasAvailable:=u 9-u 5,execLength:=42,stack:=(BitVec.ofInt 256 r::spill).map (fun w=>UInt256.mk w.toFin)} : EVM.State)=_
  have pc : u 3+u 1=u 4 := by rfl
  have gas : u 9-u 5=u 4 := by rfl
  rw [pc,gas]
  rfl

theorem client (pipeline : Roadmap.Pipeline) (checked perm : Bool) (a b : PrimTy.int.Denote)
    (nonzero : b.val≠0) (ordinary : ¬(a.val=-((2^255:Nat):Int) ∧ b.val = -1)) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (.binary .div (.local .here) (.local (.there .here)))).run (source a b)=
      (.ok (.val (sourceValue (quotient a b nonzero ordinary))),source a b) ∧
    Assembly.driverSteps 1 2 #[] (input a b perm)=.ok (expected (quotient a b nonzero ordinary).val perm) ∧
    EVM.X 2 #[] (input a b perm)=EVM.X 1 #[] (expected (quotient a b nonzero ordinary).val perm) ∧
    (expected (quotient a b nonzero ordinary).val perm).toState=(input a b perm).toState ∧
    (expected (quotient a b nonzero ordinary).val perm).memory=(input a b perm).memory ∧
    (expected (quotient a b nonzero ordinary).val perm).returnData=(input a b perm).returnData ∧
    (expected (quotient a b nonzero ordinary).val perm).H_return=(input a b perm).H_return := by
  have h := PublishedDivision.ordinary_fetched (Fixture.globals pipeline) (Fixture.frame checked) 0
    (source a b) .here (.there .here) a b rfl rfl nonzero ordinary (site perm) spill (by decide) (by change 5≤9;decide) 0
  dsimp only at h
  have shape := expected_shape a b (quotient a b nonzero ordinary).val perm
  simp only [input,Scalar.encodeValue] at shape
  simp only [Scalar.encodeValue] at h
  rw [shape] at h
  exact h

theorem zero_client (pipeline : Roadmap.Pipeline) (checked perm : Bool) (a : PrimTy.int.Denote) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (.binary .div (.local .here) (.local (.there .here)))).run (source a (n 0 (by decide)))=
      (.error (.revert (Source.panicData .divZero)),source a (n 0 (by decide))) ∧
    Assembly.driverSteps 1 2 #[] (input a (n 0 (by decide)) perm)=.ok (expected 0 perm) ∧
    EVM.X 2 #[] (input a (n 0 (by decide)) perm)=EVM.X 1 #[] (expected 0 perm) := by
  have h := PublishedDivision.zero_boundary (Fixture.globals pipeline) (Fixture.frame checked) 0
    (source a (n 0 (by decide))) .here (.there .here) a (n 0 (by decide)) rfl rfl rfl
    (site perm) spill (by decide) (by change 5≤9;decide) 0
  dsimp only at h
  have shape := expected_shape a (n 0 (by decide)) 0 perm
  simp only [input,Scalar.encodeValue] at shape
  simp only [Scalar.encodeValue] at h
  simp only [n] at shape h
  have zeroWord : BitVec.ofInt 256 0=(0 : Scalar.Word) := by rfl
  rw [zeroWord] at shape h
  rw [shape] at h
  exact h

theorem overflow_client (pipeline : Roadmap.Pipeline) (perm : Bool) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame true) 3
      (.binary .div (.local .here) (.local (.there .here)))).run (source Scalar.minimumInt (n (-1) (by decide)))=
      (.error (.revert (Source.panicData .arithmetic)),source Scalar.minimumInt (n (-1) (by decide))) ∧
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame false) 3
      (.binary .div (.local .here) (.local (.there .here)))).run (source Scalar.minimumInt (n (-1) (by decide)))=
      (.ok (.val (sourceValue Scalar.minimumInt)),source Scalar.minimumInt (n (-1) (by decide))) ∧
    Assembly.driverSteps 1 2 #[] (input Scalar.minimumInt (n (-1) (by decide)) perm)=.ok (expected Scalar.minimumInt.val perm) ∧
    EVM.X 2 #[] (input Scalar.minimumInt (n (-1) (by decide)) perm)=EVM.X 1 #[] (expected Scalar.minimumInt.val perm) := by
  have h := PublishedDivision.overflow_boundary (Fixture.globals pipeline) (Fixture.frame true) 0
    (source Scalar.minimumInt (n (-1) (by decide))) .here (.there .here) Scalar.minimumInt (n (-1) (by decide)) rfl rfl rfl rfl
    (site perm) spill (by decide) (by change 5≤9;decide) 0
  dsimp only at h
  have shape := expected_shape Scalar.minimumInt (n (-1) (by decide)) Scalar.minimumInt.val perm
  simp only [input,Scalar.encodeValue] at shape
  simp only [Scalar.encodeValue] at h
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
theorem negative_client (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (.binary .div (.local .here) (.local (.there .here)))).run (source (n (-7) (by decide)) (n 2 (by decide)))=
      (.ok (.val (sourceValue (n (-3) (by decide)))),source (n (-7) (by decide)) (n 2 (by decide))) ∧
    Assembly.driverSteps 1 2 #[] (input (n (-7) (by decide)) (n 2 (by decide)) perm)=.ok (expected (-3) perm) := by
  have h := client pipeline checked perm (n (-7) (by decide)) (n 2 (by decide)) (by decide) (by decide)
  exact ⟨h.1,h.2.1⟩

theorem signed_boundaries (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    Assembly.driverSteps 1 2 #[] (input (n (-7) (by decide)) (n (-2) (by decide)) perm)=.ok (expected 3 perm) ∧
    Assembly.driverSteps 1 2 #[] (input (n 7 (by decide)) (n (-2) (by decide)) perm)=.ok (expected (-3) perm) ∧
    Assembly.driverSteps 1 2 #[] (input Scalar.minimumInt (n 1 (by decide)) perm)=.ok (expected Scalar.minimumInt.val perm) ∧
    Assembly.driverSteps 1 2 #[] (input (n ((2^255:Nat)-1) (by decide)) (n 1 (by decide)) perm)=.ok (expected ((2^255:Nat)-1) perm) := by
  exact ⟨(client pipeline checked perm (n (-7) (by decide)) (n (-2) (by decide)) (by decide) (by decide)).2.1,
    (client pipeline checked perm (n 7 (by decide)) (n (-2) (by decide)) (by decide) (by decide)).2.1,
    (client pipeline checked perm Scalar.minimumInt (n 1 (by decide)) (by decide) (by decide)).2.1,
    (client pipeline checked perm (n ((2^255:Nat)-1) (by decide)) (n 1 (by decide)) (by decide) (by decide)).2.1⟩

theorem complete_ordered_observation (perm : Bool) :
    (expected (-3) perm).stack=[UInt256.mk (BitVec.ofInt 256 (-3)).toFin,u 258,u 513] ∧
    (expected (-3) perm).stack≠[UInt256.mk (BitVec.ofInt 256 (-4)).toFin,u 258,u 513] ∧
    (expected (-3) perm).stack≠[UInt256.mk (BitVec.ofInt 256 (-3)).toFin,u 513,u 258] ∧
    (expected (-3) perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x05,0x00] ∧
    (expected (-3) perm).pc=u 4 ∧ (expected (-3) perm).gasAvailable=u 4 ∧
    (expected (-3) perm).execLength=42 ∧
    (expected (-3) perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (expected (-3) perm).returnData.data.toList=[0xcc,0xdd] ∧
    (expected (-3) perm).H_return.data.toList=[0xee,0xff] ∧
    (expected (-3) perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (expected (-3) perm).accountMap=accounts ∧ (expected (-3) perm).σ₀=accounts := by
  refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [UInt256.mk (BitVec.ofInt 256 (-3)).toFin,u 258,u 513]≠[UInt256.mk (BitVec.ofInt 256 (-4)).toFin,u 258,u 513]
    decide
  · change [UInt256.mk (BitVec.ofInt 256 (-3)).toFin,u 258,u 513]≠[UInt256.mk (BitVec.ofInt 256 (-3)).toFin,u 513,u 258]
    decide

#print axioms client
#print axioms zero_client
#print axioms overflow_client
#print axioms negative_client
#print axioms signed_boundaries
#print axioms complete_ordered_observation
end SolidityBridge.RoadmapV15.P10.PublishedDivisionControls
