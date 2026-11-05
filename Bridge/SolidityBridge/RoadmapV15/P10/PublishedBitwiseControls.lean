import SolidityBridge.RoadmapV15.P10.PublishedBitwise
import SolidityBridge.RoadmapV15.P10.BitwiseFixtures
import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Inhabited clean-width Source/native clients; independent complete expected
States retain ordered tails and buffers. No invocation/physical-load witness. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedBitwiseControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.Bitwise
open PublishedBitwise
open WordPushFixtures (spill u accounts)
namespace Fixture
export Solidity.Backend.PrimitivePackets.SignedMod.Controls (E globals frame)
end Fixture

def source (w : Fin 32) (x y : Nat) (hx : x<2^(unsigned w).bits) (hy : y<2^(unsigned w).bits) :
    Source.EMState Fixture.E [.int (unsigned w),.int (unsigned w)] :=
  (.cons (operand w x hx) (.cons (operand w y hy) .nil),Source.St.init Fixture.E)
def input (op : Source.BinOp) (x y : Nat) (perm : Bool) : EVM.State :=
  BitwiseFixtures.input (opcode op) 3 perm (BitVec.ofNat 256 x::BitVec.ofNat 256 y::spill)
def expected (op : Source.BinOp) (x y : Nat) (perm : Bool) : EVM.State :=
  BitwiseFixtures.observed (opcode op) perm (BitVec.ofNat 256 x) (BitVec.ofNat 256 y) spill (BitVec.ofNat 256 (value op x y))

theorem client (pipeline : Roadmap.Pipeline) (checked perm : Bool) (w : Fin 32)
    (op : Source.BinOp) (hop : Supported op) (x y : Nat)
    (hx : x<2^(unsigned w).bits) (hy : y<2^(unsigned w).bits) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3 (sourceExpr Fixture.E w op)).run (source w x y hx hy)=
      (.ok (.val (operand w (value op x y) (value_lt op hop _ _ _ hx hy))),source w x y hx hy) ∧
    Assembly.driverSteps 1 2 #[] (input op x y perm)=.ok (expected op x y perm) ∧
    EVM.X 2 #[] (input op x y perm)=EVM.X 1 #[] (expected op x y perm) ∧
    (expected op x y perm).toState=(input op x y perm).toState ∧
    (expected op x y perm).memory=(input op x y perm).memory ∧
    (expected op x y perm).returnData=(input op x y perm).returnData ∧
    (expected op x y perm).H_return=(input op x y perm).H_return := by
  have h := fetched (Fixture.globals pipeline) (Fixture.frame checked) 0 (Source.St.init Fixture.E)
    w op hop x y hx hy (BitwiseFixtures.site (opcode op) 3 perm) spill (by decide) (by change 3≤3;decide) 0
  simpa only [source,input,expected,BitwiseFixtures.input,BitwiseFixtures.observed,
    BitwiseFixtures.site,WordPushFixtures.seed,WordPushFixtures.before,WordPushFixtures.after,
    WordPushFixtures.u,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem three_clients (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    Assembly.driverSteps 1 2 #[] (input .bitAnd 0xaa55 0x0ff0 perm)=.ok (expected .bitAnd 0xaa55 0x0ff0 perm) ∧
    Assembly.driverSteps 1 2 #[] (input .bitOr 0xaa55 0x0ff0 perm)=.ok (expected .bitOr 0xaa55 0x0ff0 perm) ∧
    Assembly.driverSteps 1 2 #[] (input .bitXor 0xaa55 0x0ff0 perm)=.ok (expected .bitXor 0xaa55 0x0ff0 perm) := by
  exact ⟨(client pipeline checked perm ⟨1,by decide⟩ .bitAnd (Or.inl rfl) _ _ (by decide) (by decide)).2.1,
    (client pipeline checked perm ⟨1,by decide⟩ .bitOr (Or.inr (Or.inl rfl)) _ _ (by decide) (by decide)).2.1,
    (client pipeline checked perm ⟨1,by decide⟩ .bitXor (Or.inr (Or.inr rfl)) _ _ (by decide) (by decide)).2.1⟩

theorem narrow_boundary (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    Assembly.driverSteps 1 2 #[] (input .bitXor 255 240 perm)=.ok (expected .bitXor 255 240 perm) ∧
    (expected .bitXor 255 240 perm).stack=[u 15,u 258,u 513] ∧
    ¬(256<2^(unsigned ⟨0,by decide⟩).bits) := by
  exact ⟨(client pipeline checked perm ⟨0,by decide⟩ .bitXor (Or.inr (Or.inr rfl)) _ _ (by decide) (by decide)).2.1,rfl,by decide⟩

theorem horizons (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 2
      (sourceExpr Fixture.E ⟨0,by decide⟩ .bitAnd)).run
      (source ⟨0,by decide⟩ 255 240 (by decide) (by decide))=
      (.error .timeout,source ⟨0,by decide⟩ 255 240 (by decide) (by decide)) ∧
    Assembly.driverSteps 1 1 #[] (input .bitAnd 255 240 perm)=.error .OutOfFuel := by
  exact ⟨evalE_two (Fixture.globals pipeline) (Fixture.frame checked) _ _ (Or.inl rfl) _ _,rfl⟩

theorem complete_observation (perm : Bool) :
    (expected .bitAnd 0xaa55 0x0ff0 perm).stack=[u 0x0a50,u 258,u 513] ∧
    (expected .bitOr 0xaa55 0x0ff0 perm).stack=[u 0xaff5,u 258,u 513] ∧
    (expected .bitXor 0xaa55 0x0ff0 perm).stack=[u 0xa5a5,u 258,u 513] ∧
    (expected .bitAnd 0xaa55 0x0ff0 perm).stack≠[u 0xaff5,u 258,u 513] ∧
    (expected .bitAnd 0xaa55 0x0ff0 perm).stack≠[u 0x0a50,u 513,u 258] ∧
    (expected .bitAnd 0xaa55 0x0ff0 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x16,0x00] ∧
    (expected .bitOr 0xaa55 0x0ff0 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x17,0x00] ∧
    (expected .bitXor 0xaa55 0x0ff0 perm).executionEnv.code.data.toList=[0x60,0x7f,0x50,0x18,0x00] ∧
    (expected .bitAnd 0xaa55 0x0ff0 perm).pc=u 4 ∧
    (expected .bitAnd 0xaa55 0x0ff0 perm).gasAvailable=u 0 ∧
    (expected .bitAnd 0xaa55 0x0ff0 perm).execLength=42 ∧
    (expected .bitAnd 0xaa55 0x0ff0 perm).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (expected .bitAnd 0xaa55 0x0ff0 perm).returnData.data.toList=[0xcc,0xdd] ∧
    (expected .bitAnd 0xaa55 0x0ff0 perm).H_return.data.toList=[0xee,0xff] ∧
    (expected .bitAnd 0xaa55 0x0ff0 perm).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (expected .bitAnd 0xaa55 0x0ff0 perm).accountMap=accounts := by
  refine ⟨rfl,rfl,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 0x0a50,u 258,u 513]≠[u 0xaff5,u 258,u 513];decide
  · change [u 0x0a50,u 258,u 513]≠[u 0x0a50,u 513,u 258];decide

#print axioms client
#print axioms three_clients
#print axioms narrow_boundary
#print axioms horizons
#print axioms complete_observation
end SolidityBridge.RoadmapV15.P10.PublishedBitwiseControls
