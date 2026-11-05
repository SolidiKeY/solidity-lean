import SolidityBridge.RoadmapV15.P10.PublishedSignedSub
import SolidityBridge.RoadmapV15.P10.WrappingArithmeticFixtures
import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Both Source pipelines and actual fetched signed-subtraction clients.
Complete native observations, signed wrap boundaries and resource negatives. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedSignedSubControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open PublishedSignedSub
open WordPushFixtures (spill u accounts)
namespace Fixture
export Solidity.Backend.PrimitivePackets.SignedMod.Controls (E globals frame)
end Fixture

def source (x y : Int) (hx : Src.ty.lo≤x ∧ x≤Src.ty.hi) (hy : Src.ty.lo≤y ∧ y≤Src.ty.hi) :
    Source.EMState Fixture.E [.int Src.ty,.int Src.ty] :=
  (.cons (.int x hx) (.cons (.int y hy) .nil),Source.St.init Fixture.E)
def input (x y : Int) (perm : Bool) : EVM.State :=
  WrappingArithmeticFixtures.input .SUB 11 perm (BitVec.ofInt 256 x::BitVec.ofInt 256 y::spill)
def expected (x y : Int) (perm : Bool) : EVM.State :=
  WrappingArithmeticFixtures.observed .SUB 11 perm 3 (BitVec.ofInt 256 x) (BitVec.ofInt 256 y) spill (BitVec.ofInt 256 (x-y))

private theorem shape (x y : Int) (perm : Bool) :
    (Assembly.chargedPrepare (input x y perm) 3).replaceStackAndIncrPC
      ((BitVec.ofInt 256 (x-y)::spill).map (fun z=>UInt256.mk z.toFin))=expected x y perm := by
  simp only [input,expected,WrappingArithmeticFixtures.input,WrappingArithmeticFixtures.observed,
    WrappingArithmeticFixtures.site,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.u,WordPushFixtures.before]
  rfl

theorem client (pipeline : Roadmap.Pipeline) (perm : Bool) (x y : Int)
    (hx : Src.ty.lo≤x ∧ x≤Src.ty.hi) (hy : Src.ty.lo≤y ∧ y≤Src.ty.hi) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame false) 3
      (.binary .sub (.local .here) (.local (.there .here)))).run (source x y hx hy)=
      (.ok (.val (Source.intWrap Src.ty (x-y))),source x y hx hy) ∧
    (Source.intWrap Src.ty (x-y) : Source.Val Fixture.E.layout (.int Src.ty)).word.map
      (fun w => (BitVec.ofFin w : Scalar.Word))=some (BitVec.ofInt 256 (x-y)) ∧
    Assembly.driverSteps 1 2 #[] (input x y perm)=.ok (expected x y perm) ∧
    EVM.X 2 #[] (input x y perm)=EVM.X 1 #[] (expected x y perm) := by
  have h := fetched (Fixture.globals pipeline) (Fixture.frame false) 0 (source x y hx hy)
    .here (.there .here) x y hx hy rfl rfl #[] (WrappingArithmeticFixtures.site .SUB 11 perm) spill (by decide) (by change 3≤11;decide) 0
  dsimp only at h
  have hs := shape x y perm
  simp only [input,WrappingArithmeticFixtures.input] at hs
  rw [hs] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem boundary_clients (pipeline : Roadmap.Pipeline) (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (input (-7) 2 perm)=.ok (expected (-7) 2 perm) ∧
    Assembly.driverSteps 1 2 #[] (input (-(2^255:Nat):Int) 1 perm)=.ok (expected (-(2^255:Nat):Int) 1 perm) ∧
    Assembly.driverSteps 1 2 #[] (input ((2^255:Nat)-1) (-1) perm)=.ok (expected ((2^255:Nat)-1) (-1) perm) := by
  exact ⟨(client pipeline perm (-7) 2 (by decide) (by decide)).2.2.1,
    (client pipeline perm (-(2^255:Nat):Int) 1 (by decide) (by decide)).2.2.1,
    (client pipeline perm ((2^255:Nat)-1) (-1) (by decide) (by decide)).2.2.1⟩

theorem wrap_and_order :
    BitVec.ofInt 256 ((-(2^255:Nat):Int)-1)=BitVec.ofNat 256 ((2^255:Nat)-1) ∧
    BitVec.ofInt 256 ((((2^255:Nat)-1):Int)-(-1))=BitVec.ofNat 256 (2^255) ∧
    BitVec.ofInt 256 ((-7:Int)-2)≠BitVec.ofInt 256 (2-(-7:Int)) ∧
    BitVec.ofInt 256 ((-7:Int)-(-7))=0 := by decide

theorem complete_observation (perm : Bool) :
    let next := expected (-7) 2 perm
    next.stack=[u ((2^256:Nat)-9),u 258,u 513] ∧ next.stack≠[u 9,u 258,u 513] ∧
    next.stack≠[u ((2^256:Nat)-9),u 513,u 258] ∧
    next.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x03,0x00] ∧
    next.pc=u 4 ∧ next.gasAvailable=u 8 ∧ next.execLength=42 ∧
    next.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    next.returnData.data.toList=[0xcc,0xdd] ∧ next.H_return.data.toList=[0xee,0xff] ∧
    next.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧ next.accountMap=accounts ∧ next.σ₀=accounts := by
  refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u ((2^256:Nat)-9),u 258,u 513]≠[u 9,u 258,u 513];decide
  · change [u ((2^256:Nat)-9),u 258,u 513]≠[u ((2^256:Nat)-9),u 513,u 258];decide

theorem resource_order (perm : Bool) :
    Assembly.driverSteps 1 2 #[] {input (-7) 2 perm with gasAvailable:=u 2,stack:=[]} = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] {input (-7) 2 perm with gasAvailable:=u 3,stack:=[u 7]} = .error .StackUnderflow ∧
    Assembly.driverSteps 1 1 #[] {input (-7) 2 perm with gasAvailable:=u 0,stack:=[]} = .error .OutOfFuel := by
  cases perm <;> exact ⟨rfl,rfl,rfl⟩

#print axioms client
#print axioms boundary_clients
#print axioms wrap_and_order
#print axioms resource_order
#print axioms complete_observation
end SolidityBridge.RoadmapV15.P10.PublishedSignedSubControls
