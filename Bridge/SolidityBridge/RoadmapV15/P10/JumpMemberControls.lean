import SolidityBridge.RoadmapV15.P10.JumpMemberConsumer
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Populated membership/missing-target clients, preserving complete State.
The finite backend jumpdest computation is a fixture fact only, not general
agreement between scanners or adequacy of arbitrary supplied arrays. -/
namespace SolidityBridge.RoadmapV15.P10.JumpMemberControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed before u)

def after : Backend.Program := [.op .POP,.op .JUMPDEST,.op .STOP]
def valid : Array UInt256 := #[u 5]
def rest : List UInt256 := [u 258,u 513]
def site (gas : Nat) (perm : Bool) : Site .JUMPI := ⟨seed gas perm,before,after,by decide⟩
def input (gas : Nat) (perm : Bool) (destination condition : UInt256) (tail : List UInt256) : EVM.State :=
  (jumpMemberSite (site gas perm) destination condition tail).state
def observed (gas : Nat) (perm : Bool) (condition : UInt256) (tail : List UInt256) (pc : Nat) : EVM.State :=
  {input gas perm (u 5) condition tail with
    pc := u pc,gasAvailable := u (gas-10),execLength := 42,stack := tail}

private theorem execute (tail : List UInt256) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 1 2 valid (input 10 false (u 5) (u 2) tail) =
      .ok (observed 10 false (u 2) tail 5) := by
  have h := (jump_member_agreement valid (site 10 false) (u 5) (u 2) tail (by decide) room (by decide) 0).1
  simpa only [input,observed,site,seed,before,after,u,jumpMemberSite,Site.state,
    Assembly.chargedPrepare] using h

theorem taken_static :
    Assembly.driverSteps 1 2 valid (input 10 false (u 5) (u 2) rest) =
      .ok (observed 10 false (u 2) rest 5) ∧
    EVM.X 2 valid (input 10 false (u 5) (u 2) rest) =
      EVM.X 1 valid (observed 10 false (u 2) rest 5) := by
  have h := jump_member_agreement valid (site 10 false) (u 5) (u 2) rest (by decide) (by decide) (by decide) 0
  simpa only [input,observed,site,seed,before,after,u,jumpMemberSite,Site.state,
    Assembly.chargedPrepare] using h

theorem writable_zero_max :
    Assembly.driverSteps 1 2 valid (input 27 true (u 5) (u 0) rest) =
      .ok (observed 27 true (u 0) rest 4) ∧
    Assembly.driverSteps 1 2 valid (input 27 true (u 5) (u (2^256-1)) rest) =
      .ok (observed 27 true (u (2^256-1)) rest 5) := by
  have a := (jump_member_agreement valid (site 27 true) (u 5) (u 0) rest (by decide) (by decide) (by decide) 0).1
  have b := (jump_member_agreement valid (site 27 true) (u 5) (u (2^256-1)) rest (by decide) (by decide) (by decide) 0).1
  constructor
  · simpa only [input,observed,site,seed,before,after,u,jumpMemberSite,Site.state,Assembly.chargedPrepare] using a
  · simpa only [input,observed,site,seed,before,after,u,jumpMemberSite,Site.state,Assembly.chargedPrepare] using b

theorem legal_boundaries :
    Assembly.driverSteps 1 2 valid (input 10 false (u 5) (u 2) []) = .ok (observed 10 false (u 2) [] 5) ∧
    Assembly.driverSteps 1 2 valid (input 10 false (u 5) (u 2) (List.replicate 1022 (u 258))) =
      .ok (observed 10 false (u 2) (List.replicate 1022 (u 258)) 5) := by
  exact ⟨execute _ (by decide),execute _ (by simp only [List.length_replicate];decide)⟩

theorem missing_target_and_priority :
    (Assembly.driverSteps 1 2 valid (input 10 false (u 13) (u 2) rest) = .error .BadJumpDestination ∧
      EVM.X 1 valid (input 10 false (u 13) (u 2) rest) = .error .BadJumpDestination) ∧
    Assembly.driverSteps 1 2 #[] (input 10 true (u 5) (u 1) rest) = .error .BadJumpDestination ∧
    Assembly.driverSteps 1 2 valid (input 9 false (u 13) (u 2) rest) = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 valid ({input 10 false (u 13) (u 2) rest with stack := [u 13]}) = .error .StackUnderflow ∧
    Assembly.driverSteps 1 1 valid (input 0 false (u 13) (u 2) rest) = .error .OutOfFuel := by
  have a := jump_missing_refusal valid (site 10 false) (u 13) (u 2) rest (by decide) (by decide) (by decide) 0
  have b := (jump_missing_refusal #[] (site 10 true) (u 5) (u 1) rest (by decide) (by decide) (by decide) 0).1
  exact ⟨a,b,rfl,rfl,rfl⟩

theorem byte_image_and_ordered_state :
    Backend.jumpdests (Backend.encode (before ++ .op .JUMPI :: after)) = [5] ∧
    (input 10 false (u 5) (u 2) rest).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x57,0x50,0x5b,0x00] ∧
    (observed 10 false (u 2) rest 5).stack = [u 258,u 513] ∧
    (observed 10 false (u 2) rest 5).stack ≠ [u 513,u 258] ∧
    (observed 10 false (u 2) rest 5).pc ≠ u 4 ∧
    (observed 27 true (u 0) rest 4).pc ≠ u 5 ∧
    (observed 10 false (u 2) rest 5).gasAvailable = u 0 ∧
    (observed 27 true (u 0) rest 4).gasAvailable = u 17 ∧
    (observed 10 false (u 2) rest 5).execLength = 42 ∧
    (observed 10 false (u 2) rest 5).memory.data.toList = [0xaa,0xbb] ++ List.replicate 30 0 ∧
    (observed 10 false (u 2) rest 5).returnData.data.toList = [0xcc,0xdd] ∧
    (observed 10 false (u 2) rest 5).H_return.data.toList = [0xee,0xff] ∧
    (observed 10 false (u 2) rest 5).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (observed 10 false (u 2) rest 5).accountMap = WordPushFixtures.accounts ∧
    (observed 10 false (u 2) rest 5).σ₀ = WordPushFixtures.accounts := by
  have scan : Backend.jumpdests (Backend.encode (before ++ .op .JUMPI :: after)) = [5] := by
    change Backend.jumpdests [0x60,0x7f,0x50,0x57,0x50,0x5b,0x00] = [5]
    have push : Backend.immWidth (0x60 : UInt8) = 1 := rfl
    have pop : Backend.immWidth (0x50 : UInt8) = 0 := rfl
    have branch : Backend.immWidth (0x57 : UInt8) = 0 := rfl
    have dest : Backend.immWidth (0x5b : UInt8) = 0 := rfl
    have stop : Backend.immWidth (0x00 : UInt8) = 0 := rfl
    simp only [Backend.jumpdests,Backend.starts,push,pop,branch,dest,stop,List.drop_succ_cons,List.drop_zero]
    decide +kernel
  exact ⟨scan,rfl,rfl,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms taken_static
#print axioms writable_zero_max
#print axioms legal_boundaries
#print axioms missing_target_and_priority
#print axioms byte_image_and_ordered_state
end SolidityBridge.RoadmapV15.P10.JumpMemberControls
