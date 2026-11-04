import SolidityBridge.RoadmapV15.P10.PublishedCheckedAdd
import SolidityBridge.RoadmapV15.P10.WrappingArithmeticFixtures
import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Checked Source success and panic versus independent populated raw ADD
records. These clients do not certify the missing compiler panic guard. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedCheckedAddControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.UnsignedDiv (sourceUInt)
open PublishedCheckedAdd
open WordPushFixtures (spill u accounts)
namespace Fixture
export Solidity.Backend.PrimitivePackets.SignedMod.Controls (E globals frame)
end Fixture

def source (a b : PrimTy.uint.Denote) : Source.EMState Fixture.E [.int Source.IntTy.u256,.int Source.IntTy.u256] :=
  (.cons (sourceUInt Fixture.E.layout a) (.cons (sourceUInt Fixture.E.layout b) .nil),Source.St.init Fixture.E)
def n (v : Int) (h : PrimTy.uint.inRange v=true) : PrimTy.uint.Denote := ⟨v,h⟩
def result (a b : PrimTy.uint.Denote) : Scalar.Word := BitVec.ofInt 256 (a.val+b.val)
def input (a b : PrimTy.uint.Denote) (perm : Bool) : EVM.State :=
  WrappingArithmeticFixtures.input .ADD 9 perm (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::spill)
def expected (a b : PrimTy.uint.Denote) (perm : Bool) : EVM.State :=
  WrappingArithmeticFixtures.observed .ADD 9 perm 3 (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill (result a b)

private theorem shape (a b : PrimTy.uint.Denote) (perm : Bool) :
    (Assembly.chargedPrepare (input a b perm) 3).replaceStackAndIncrPC
      ((result a b::spill).map (fun z=>UInt256.mk z.toFin))=expected a b perm := by
  simp only [input,expected,WrappingArithmeticFixtures.input,WrappingArithmeticFixtures.observed,
    WrappingArithmeticFixtures.site,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.u,WordPushFixtures.before]
  rfl

theorem success_client (pipeline : Roadmap.Pipeline) (perm : Bool) (a b : PrimTy.uint.Denote)
    (fits : Source.IntTy.u256.lo≤a.val+b.val ∧ a.val+b.val≤Source.IntTy.u256.hi) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame true) 3
      (.binary .add (.local .here) (.local (.there .here)))).run (source a b)=
      (.ok (.val (.int (a.val+b.val) fits)),source a b) ∧
    Assembly.driverSteps 1 2 #[] (input a b perm)=.ok (expected a b perm) ∧
    EVM.X 2 #[] (input a b perm)=EVM.X 1 #[] (expected a b perm) := by
  have h := success_fetched (Fixture.globals pipeline) (Fixture.frame true) 0 (source a b)
    .here (.there .here) a b rfl rfl fits #[] (WrappingArithmeticFixtures.site .ADD 9 perm) spill (by decide) (by change 3≤9;decide) 0
  dsimp only at h
  have hs := shape a b perm
  simp only [input,result,WrappingArithmeticFixtures.input] at hs
  rw [hs] at h
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem overflow_client (pipeline : Roadmap.Pipeline) (perm : Bool) (a b : PrimTy.uint.Denote)
    (overflow : ¬(Source.IntTy.u256.lo≤a.val+b.val ∧ a.val+b.val≤Source.IntTy.u256.hi)) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame true) 3
      (.binary .add (.local .here) (.local (.there .here)))).run (source a b)=
      (.error (.revert (Source.panicData .arithmetic)),source a b) ∧
    Assembly.driverSteps 1 2 #[] (input a b perm)=.ok (expected a b perm) ∧
    EVM.X 2 #[] (input a b perm)=EVM.X 1 #[] (expected a b perm) := by
  have h := overflow_boundary (Fixture.globals pipeline) (Fixture.frame true) 0 (source a b)
    .here (.there .here) a b rfl rfl overflow #[] (WrappingArithmeticFixtures.site .ADD 9 perm) spill (by decide) (by change 3≤9;decide) 0
  dsimp only at h
  have hs := shape a b perm
  simp only [input,result,WrappingArithmeticFixtures.input] at hs
  rw [hs] at h
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem nonzero_success (pipeline : Roadmap.Pipeline) (perm : Bool) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame true) 3
      (.binary .add (.local .here) (.local (.there .here)))).run (source (n 7 (by decide)) (n 513 (by decide)))=
      (.ok (.val (.int 520 (by decide))),source (n 7 (by decide)) (n 513 (by decide))) ∧
    Assembly.driverSteps 1 2 #[] (input (n 7 (by decide)) (n 513 (by decide)) perm)=.ok (expected (n 7 (by decide)) (n 513 (by decide)) perm) ∧
    EVM.X 2 #[] (input (n 7 (by decide)) (n 513 (by decide)) perm)=EVM.X 1 #[] (expected (n 7 (by decide)) (n 513 (by decide)) perm) := by
  exact success_client pipeline perm (n 7 (by decide)) (n 513 (by decide)) (by decide)

theorem boundary_clients (pipeline : Roadmap.Pipeline) (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (input (n ((2^256:Nat)-2) (by decide)) (n 1 (by decide)) perm)=
      .ok (expected (n ((2^256:Nat)-2) (by decide)) (n 1 (by decide)) perm) ∧
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame true) 3
      (.binary .add (.local .here) (.local (.there .here)))).run (source (n ((2^256:Nat)-1) (by decide)) (n 1 (by decide)))=
      (.error (.revert (Source.panicData .arithmetic)),source (n ((2^256:Nat)-1) (by decide)) (n 1 (by decide))) ∧
    Assembly.driverSteps 1 2 #[] (input (n ((2^256:Nat)-1) (by decide)) (n 1 (by decide)) perm)=
      .ok (expected (n ((2^256:Nat)-1) (by decide)) (n 1 (by decide)) perm) := by
  exact ⟨(success_client pipeline perm (n ((2^256:Nat)-2) (by decide)) (n 1 (by decide)) (by decide)).2.1,
    (overflow_client pipeline perm (n ((2^256:Nat)-1) (by decide)) (n 1 (by decide)) (by decide)).1,
    (overflow_client pipeline perm (n ((2^256:Nat)-1) (by decide)) (n 1 (by decide)) (by decide)).2.1⟩

theorem panic_observation :
    Source.panicData .arithmetic=[0x4e,0x48,0x7b,0x71]++List.replicate 31 0++[0x11] ∧
    Source.panicData .arithmetic≠[0xcc,0xdd] ∧
    result (n ((2^256:Nat)-1) (by decide)) (n 1 (by decide))=0 ∧
    result (n ((2^256:Nat)-2) (by decide)) (n 1 (by decide))=BitVec.ofNat 256 ((2^256:Nat)-1) := by
  decide

theorem complete_observation (perm : Bool) :
    let next := expected (n 7 (by decide)) (n 513 (by decide)) perm
    next.stack=[u 520,u 258,u 513] ∧ next.stack≠[u 8,u 258,u 513] ∧ next.stack≠[u 520,u 513,u 258] ∧
    next.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x01,0x00] ∧
    next.pc=u 4 ∧ next.gasAvailable=u 6 ∧ next.execLength=42 ∧
    next.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    next.returnData.data.toList=[0xcc,0xdd] ∧ next.H_return.data.toList=[0xee,0xff] ∧
    next.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧ next.accountMap=accounts ∧ next.σ₀=accounts := by
  refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 520,u 258,u 513]≠[u 8,u 258,u 513];decide
  · change [u 520,u 258,u 513]≠[u 520,u 513,u 258];decide

#print axioms success_client
#print axioms overflow_client
#print axioms nonzero_success
#print axioms boundary_clients
#print axioms panic_observation
#print axioms complete_observation
end SolidityBridge.RoadmapV15.P10.PublishedCheckedAddControls
