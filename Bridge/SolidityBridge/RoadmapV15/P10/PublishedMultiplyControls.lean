import SolidityBridge.RoadmapV15.P10.PublishedMultiply
import SolidityBridge.RoadmapV15.P10.WrappingArithmeticFixtures
import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Direct unchecked Source-word/native MUL clients with independent populated
States. No physical loading, compiler/frame/world origin or checked-mode claim. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedMultiplyControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.UnsignedDiv (sourceUInt)
open PublishedMultiply
open WordPushFixtures (spill u accounts)
namespace Fixture
export Solidity.Backend.PrimitivePackets.SignedMod.Controls (E globals frame)
end Fixture

def source (a b : PrimTy.uint.Denote) : Source.EMState Fixture.E [.int Source.IntTy.u256,.int Source.IntTy.u256] :=
  (.cons (sourceUInt Fixture.E.layout a) (.cons (sourceUInt Fixture.E.layout b) .nil),Source.St.init Fixture.E)
def n (v : Int) (h : PrimTy.uint.inRange v=true) : PrimTy.uint.Denote := ⟨v,h⟩
def result (a b : PrimTy.uint.Denote) : Scalar.Word := BitVec.ofInt 256 (a.val*b.val)
def input (a b : PrimTy.uint.Denote) (perm : Bool) : EVM.State :=
  WrappingArithmeticFixtures.input .MUL 11 perm (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::spill)
def expected (a b : PrimTy.uint.Denote) (perm : Bool) : EVM.State :=
  WrappingArithmeticFixtures.observed .MUL 11 perm 5 (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill (result a b)

private theorem shape (a b : PrimTy.uint.Denote) (perm : Bool) :
    (Assembly.chargedPrepare (input a b perm) 5).replaceStackAndIncrPC
      ((result a b::spill).map (fun z=>UInt256.mk z.toFin))=expected a b perm := by
  simp only [input,expected,WrappingArithmeticFixtures.input,WrappingArithmeticFixtures.observed,
    WrappingArithmeticFixtures.site,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.u,WordPushFixtures.before]
  rfl

theorem client (pipeline : Roadmap.Pipeline) (perm : Bool) (a b : PrimTy.uint.Denote) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame false) 3
      (.binary .mul (.local .here) (.local (.there .here)))).run (source a b)=
      (.ok (.val (Source.intWrap Source.IntTy.u256 (a.val*b.val))),source a b) ∧
    (Source.intWrap Source.IntTy.u256 (a.val*b.val) : Source.Val Fixture.E.layout (.int Source.IntTy.u256)).word.map
      (fun w => (BitVec.ofFin w : Scalar.Word))=some (result a b) ∧
    Assembly.driverSteps 1 2 #[] (input a b perm)=.ok (expected a b perm) ∧
    EVM.X 2 #[] (input a b perm)=EVM.X 1 #[] (expected a b perm) := by
  have h := fetched (Fixture.globals pipeline) (Fixture.frame false) 0 (source a b)
    .here (.there .here) a b rfl rfl #[] (WrappingArithmeticFixtures.site .MUL 11 perm) spill (by decide) (by change 5≤11;decide) 0
  dsimp only at h
  have hs := shape a b perm
  simp only [input,result,WrappingArithmeticFixtures.input] at hs
  rw [hs] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem nonzero_zero (pipeline : Roadmap.Pipeline) (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (input (n 7 (by decide)) (n 513 (by decide)) perm)=.ok (expected (n 7 (by decide)) (n 513 (by decide)) perm) ∧
    Assembly.driverSteps 1 2 #[] (input (n 0 (by decide)) (n ((2^256:Nat)-1) (by decide)) perm)=.ok (expected (n 0 (by decide)) (n ((2^256:Nat)-1) (by decide)) perm) := by
  exact ⟨(client pipeline perm (n 7 (by decide)) (n 513 (by decide))).2.2.1,
    (client pipeline perm (n 0 (by decide)) (n ((2^256:Nat)-1) (by decide))).2.2.1⟩

theorem overflow_clients (pipeline : Roadmap.Pipeline) (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (input (n (2^128:Nat) (by decide)) (n (2^128:Nat) (by decide)) perm)=.ok (expected (n (2^128:Nat) (by decide)) (n (2^128:Nat) (by decide)) perm) ∧
    Assembly.driverSteps 1 2 #[] (input (n ((2^256:Nat)-1) (by decide)) (n ((2^256:Nat)-1) (by decide)) perm)=.ok (expected (n ((2^256:Nat)-1) (by decide)) (n ((2^256:Nat)-1) (by decide)) perm) ∧
    (Source.intWrap Source.IntTy.u256 ((n (2^128:Nat) (by decide)).val*(n (2^128:Nat) (by decide)).val) : Source.Val Fixture.E.layout (.int Source.IntTy.u256)).word.map
      (fun w => (BitVec.ofFin w : Scalar.Word))=some 0 ∧
    (Source.intWrap Source.IntTy.u256 ((n ((2^256:Nat)-1) (by decide)).val*(n ((2^256:Nat)-1) (by decide)).val) : Source.Val Fixture.E.layout (.int Source.IntTy.u256)).word.map
      (fun w => (BitVec.ofFin w : Scalar.Word))=some 1 := by
  have zero := client pipeline perm (n (2^128:Nat) (by decide)) (n (2^128:Nat) (by decide))
  have one := client pipeline perm (n ((2^256:Nat)-1) (by decide)) (n ((2^256:Nat)-1) (by decide))
  have rz : result (n (2^128:Nat) (by decide)) (n (2^128:Nat) (by decide))=0 := by decide
  have ro : result (n ((2^256:Nat)-1) (by decide)) (n ((2^256:Nat)-1) (by decide))=1 := by decide
  exact ⟨zero.2.2.1,one.2.2.1,zero.2.1.trans (congrArg some rz),one.2.1.trans (congrArg some ro)⟩

theorem encoding_controls :
    BitVec.ofFin (Source.intWord (-1))=BitVec.ofNat 256 ((2^256:Nat)-1) ∧
    (BitVec.ofFin (Source.intWord (2^256:Nat)) : Scalar.Word)=0 ∧
    result (n ((2^256:Nat)-1) (by decide)) (n ((2^256:Nat)-1) (by decide))≠0 ∧
    result (n (2^128:Nat) (by decide)) (n (2^128:Nat) (by decide))≠1 := by
  decide

theorem complete_observation (perm : Bool) :
    let next := expected (n 7 (by decide)) (n 513 (by decide)) perm
    next.stack=[u 3591,u 258,u 513] ∧ next.stack≠[u 7,u 258,u 513] ∧ next.stack≠[u 3591,u 513,u 258] ∧
    next.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x02,0x00] ∧
    next.pc=u 4 ∧ next.gasAvailable=u 6 ∧ next.execLength=42 ∧
    next.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    next.returnData.data.toList=[0xcc,0xdd] ∧ next.H_return.data.toList=[0xee,0xff] ∧
    next.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧ next.accountMap=accounts ∧ next.σ₀=accounts := by
  refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 3591,u 258,u 513]≠[u 7,u 258,u 513];decide
  · change [u 3591,u 258,u 513]≠[u 3591,u 513,u 258];decide

#print axioms client
#print axioms nonzero_zero
#print axioms overflow_clients
#print axioms encoding_controls
#print axioms complete_observation
end SolidityBridge.RoadmapV15.P10.PublishedMultiplyControls
