import SolidityBridge.RoadmapV15.P10.PublishedRemainder
import SolidityBridge.RoadmapV15.P10.WordPushFixtures
import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Reuse the published Source fixture read-only. Source and native contexts
are separately populated; no physical loading or invocation-frame identity
relation is asserted by these pure arithmetic body observations. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedRemainderControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.SignedMod
open WordPushFixtures (seed u accounts spill before after)
namespace Fixture
export Solidity.Backend.PrimitivePackets.SignedMod.Controls (E globals frame source)
end Fixture

def site (perm : Bool) : Site .SMOD := ⟨seed 9 perm,before,after,by decide⟩
def input (x y : Int) (hx : Range x) (hy : Range y) (perm : Bool) : EVM.State :=
  (modularSite (site perm) (Scalar.encodeValue .int (lower x hx)::Scalar.encodeValue .int (lower y hy)::spill)).state
def expected (value : Int) (perm : Bool) : EVM.State :=
  {(site perm).state with pc := u 4,gasAvailable := u 4,execLength := 42,stack := (BitVec.ofInt 256 value::spill).map (fun w => UInt256.mk w.toFin)}

theorem client (pipeline : Roadmap.Pipeline) (checked perm : Bool)
    (x y : Int) (hx : Range x) (hy : Range y) (nonzero : y ≠ 0) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (.binary .mod (.local .here) (.local (.there .here)))).run (Fixture.source x y hx hy) =
      (.ok (.val (.int (x.tmod y) (remainder_range x y hy nonzero))),Fixture.source x y hx hy) ∧
    Assembly.driverSteps 1 2 #[] (input x y hx hy perm) = .ok (expected (x.tmod y) perm) ∧
    EVM.X 2 #[] (input x y hx hy perm) = EVM.X 1 #[] (expected (x.tmod y) perm) ∧
    (expected (x.tmod y) perm).toState = (input x y hx hy perm).toState ∧
    (expected (x.tmod y) perm).memory = (input x y hx hy perm).memory ∧
    (expected (x.tmod y) perm).returnData = (input x y hx hy perm).returnData ∧
    (expected (x.tmod y) perm).H_return = (input x y hx hy perm).H_return := by
  have h := PublishedRemainder.source_fetched (Fixture.globals pipeline) (Fixture.frame checked) 0
    (Fixture.source x y hx hy) .here (.there .here) x y hx hy rfl rfl nonzero
    (site perm) spill (by decide) (by change 5 ≤ 9;decide) 0
  dsimp only at h
  have shape : (Assembly.chargedPrepare (input x y hx hy perm) 5).replaceStackAndIncrPC
      ((Scalar.encodeValue .int (lower (x.tmod y) (remainder_range x y hy nonzero))::spill).map (fun w => UInt256.mk w.toFin)) = expected (x.tmod y) perm := by
    change ({input x y hx hy perm with pc := u 3+u 1,gasAvailable := u 9-u 5,execLength := 42,stack := (BitVec.ofInt 256 (x.tmod y)::spill).map (fun w => UInt256.mk w.toFin)} : EVM.State) = _
    have pc : u 3+u 1=u 4 := by rfl
    have gas : u 9-u 5=u 4 := by rfl
    rw [pc,gas]
    rfl
  dsimp only [input] at shape
  rw [shape] at h
  exact h
theorem zero_client (pipeline : Roadmap.Pipeline) (checked perm : Bool) (x : Int) (hx : Range x) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (.binary .mod (.local .here) (.local (.there .here)))).run (Fixture.source x 0 hx (by decide)) =
      (.error (.revert (Source.panicData .divZero)),Fixture.source x 0 hx (by decide)) ∧
    Assembly.driverSteps 1 2 #[] (input x 0 hx (by decide) perm) = .ok (expected 0 perm) ∧
    EVM.X 2 #[] (input x 0 hx (by decide) perm) = EVM.X 1 #[] (expected 0 perm) := by
  have h := PublishedRemainder.zero_boundary (Fixture.globals pipeline) (Fixture.frame checked) 0
    (Fixture.source x 0 hx (by decide)) .here (.there .here) x hx (by decide) rfl rfl
    (site perm) spill (by decide) (by change 5 ≤ 9;decide) 0
  dsimp only at h
  have shape : (Assembly.chargedPrepare (input x 0 hx (by decide) perm) 5).replaceStackAndIncrPC
      ((0::spill).map (fun (w : Scalar.Word) => UInt256.mk w.toFin)) = expected 0 perm := by
    change ({input x 0 hx (by decide) perm with pc := u 3+u 1,gasAvailable := u 9-u 5,execLength := 42,stack := (0::spill).map (fun (w : Scalar.Word) => UInt256.mk w.toFin)} : EVM.State) = _
    have pc : u 3+u 1=u 4 := by rfl
    have gas : u 9-u 5=u 4 := by rfl
    rw [pc,gas]
    rfl
  dsimp only [input] at shape
  rw [shape] at h
  exact h

theorem negative_client (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (.binary .mod (.local .here) (.local (.there .here)))).run (Fixture.source (-11) 3 (by decide) (by decide)) =
      (.ok (.val (.int (-2) (by decide))),Fixture.source (-11) 3 (by decide) (by decide)) ∧
    Assembly.driverSteps 1 2 #[] (input (-11) 3 (by decide) (by decide) perm) = .ok (expected (-2) perm) := by
  have h := client pipeline checked perm (-11) 3 (by decide) (by decide) (by decide)
  have result : (-11 : Int).tmod 3 = -2 := by decide
  simpa only [result] using And.intro h.1 h.2.1

theorem divisor_signs (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    Assembly.driverSteps 1 2 #[] (input (-11) (-3) (by decide) (by decide) perm) = .ok (expected (-2) perm) ∧
    Assembly.driverSteps 1 2 #[] (input 11 (-3) (by decide) (by decide) perm) = .ok (expected 2 perm) ∧
    Assembly.driverSteps 1 2 #[] (input ((2^255 : Nat)-1) 2 (by decide) (by decide) perm) = .ok (expected 1 perm) := by
  have a := (client pipeline checked perm (-11) (-3) (by decide) (by decide) (by decide)).2.1
  have b := (client pipeline checked perm 11 (-3) (by decide) (by decide) (by decide)).2.1
  have c := (client pipeline checked perm ((2^255 : Nat)-1) 2 (by decide) (by decide) (by decide)).2.1
  exact ⟨a,b,c⟩

theorem minimum_client (pipeline : Roadmap.Pipeline) (checked perm : Bool) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame checked) 3
      (.binary .mod (.local .here) (.local (.there .here)))).run (Fixture.source (-((2^255 : Nat):Int)) (-1) (by decide) (by decide)) =
      (.ok (.val (.int 0 (by decide))),Fixture.source (-((2^255 : Nat):Int)) (-1) (by decide) (by decide)) ∧
    Assembly.driverSteps 1 2 #[] (input (-((2^255 : Nat):Int)) (-1) (by decide) (by decide) perm) = .ok (expected 0 perm) := by
  have h := client pipeline checked perm (-((2^255 : Nat):Int)) (-1) (by decide) (by decide) (by decide)
  have result : (-((2^255 : Nat):Int)).tmod (-1) = 0 := minimum_remainder_neg_one
  simpa only [result] using And.intro h.1 h.2.1

theorem complete_ordered_observation (perm : Bool) :
    (expected (-2) perm).stack = [UInt256.mk (BitVec.ofInt 256 (-2)).toFin,u 258,u 513] ∧
    (expected (-2) perm).stack ≠ [u 2,u 258,u 513] ∧
    (expected (-2) perm).stack ≠ [UInt256.mk (BitVec.ofInt 256 (-2)).toFin,u 513,u 258] ∧
    (expected (-2) perm).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x07,0x00] ∧
    (expected (-2) perm).pc = u 4 ∧ (expected (-2) perm).gasAvailable = u 4 ∧
    (expected (-2) perm).execLength = 42 ∧
    (expected (-2) perm).memory.data.toList = [0xaa,0xbb]++List.replicate 30 0 ∧
    (expected (-2) perm).returnData.data.toList = [0xcc,0xdd] ∧
    (expected (-2) perm).H_return.data.toList = [0xee,0xff] ∧
    (expected (-2) perm).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (expected (-2) perm).accountMap = accounts ∧ (expected (-2) perm).σ₀ = accounts := by
  refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [UInt256.mk (BitVec.ofInt 256 (-2)).toFin,u 258,u 513] ≠ [u 2,u 258,u 513]
    decide
  · change [UInt256.mk (BitVec.ofInt 256 (-2)).toFin,u 258,u 513] ≠ [UInt256.mk (BitVec.ofInt 256 (-2)).toFin,u 513,u 258]
    decide

#print axioms client
#print axioms zero_client
#print axioms negative_client
#print axioms divisor_signs
#print axioms minimum_client
#print axioms complete_ordered_observation
end SolidityBridge.RoadmapV15.P10.PublishedRemainderControls
