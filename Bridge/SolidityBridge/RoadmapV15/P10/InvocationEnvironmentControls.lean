import SolidityBridge.RoadmapV15.P10.InvocationEnvironment
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Distinct owner/caller/origin, populated native States and actual charged
failure ordering. These do not witness CALL origin or a source/world frame. -/
namespace SolidityBridge.RoadmapV15.P10.InvocationEnvironmentControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed u accounts spill before after)

def entry (op : Backend.Op) (gas : Nat) (perm : Bool) (words : Scalar.Stack) : Site op :=
  ⟨{seed gas perm with
    stack := words.map (fun w => UInt256.mk w.toFin)
    executionEnv := {(seed gas perm).executionEnv with weiValue := u 37}},
    before,after,by decide⟩
def observed (op : Backend.Op) (perm : Bool) (words : Scalar.Stack) (value : UInt256) : EVM.State :=
  {(entry op 9 perm words).state with
    pc := u 4,gasAvailable := u 7,execLength := 42
    stack := value::words.map (fun w => UInt256.mk w.toFin)}

theorem address_client (perm : Bool) (words : Scalar.Stack) (room : words.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (entry .ADDRESS 9 perm words).state =
      .ok (observed .ADDRESS perm words (u 7)) := by
  have capacity : (entry .ADDRESS 9 perm words).state.stack.length+1 ≤ 1024 := by
    simpa only [entry,Site.state,List.length_map] using room
  exact (address_fetched (entry .ADDRESS 9 perm words) 0 (by change 2 ≤ 9;decide) capacity).1

theorem caller_client (perm : Bool) (words : Scalar.Stack) (room : words.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (entry .CALLER 9 perm words).state =
      .ok (observed .CALLER perm words (u 11)) := by
  have capacity : (entry .CALLER 9 perm words).state.stack.length+1 ≤ 1024 := by
    simpa only [entry,Site.state,List.length_map] using room
  exact (caller_fetched (entry .CALLER 9 perm words) 0 (by change 2 ≤ 9;decide) capacity).1

theorem callvalue_client (perm : Bool) (words : Scalar.Stack) (room : words.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (entry .CALLVALUE 9 perm words).state =
      .ok (observed .CALLVALUE perm words (u 37)) := by
  have capacity : (entry .CALLVALUE 9 perm words).state.stack.length+1 ≤ 1024 := by
    simpa only [entry,Site.state,List.length_map] using room
  exact (callvalue_fetched (entry .CALLVALUE 9 perm words) 0 (by change 2 ≤ 9;decide) capacity).1

theorem legal_capacity :
    Assembly.driverSteps 1 2 #[] (entry .CALLER 9 false []).state =
      .ok (observed .CALLER false [] (u 11)) ∧
    Assembly.driverSteps 1 2 #[] (entry .CALLVALUE 9 true (List.replicate 1023 513)).state =
      .ok (observed .CALLVALUE true (List.replicate 1023 513) (u 37)) := by
  exact ⟨caller_client _ _ (by decide),callvalue_client _ _ (by simp only [List.length_replicate];decide)⟩

theorem resource_order :
    Assembly.driverSteps 1 2 #[] (entry .ADDRESS 1 false spill).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 1 #[] (entry .CALLER 0 false spill).state = .error .OutOfFuel ∧
    Assembly.driverSteps 1 2 #[] (entry .CALLVALUE 9 false (List.replicate 1024 513)).state = .error .StackOverflow ∧
    Assembly.driverSteps 1 2 #[] (entry .CALLVALUE 1 true (List.replicate 1024 513)).state = .error .OutOfGass := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl⟩

theorem distinct_identities :
    (observed .ADDRESS false spill (u 7)).stack = [u 7,u 258,u 513] ∧
    (observed .CALLER true spill (u 11)).stack = [u 11,u 258,u 513] ∧
    (observed .CALLER true spill (u 11)).stack ≠ [u 19,u 258,u 513] ∧
    (observed .CALLER true spill (u 11)).stack ≠ [u 7,u 258,u 513] ∧
    (observed .CALLVALUE false spill (u 37)).stack ≠ [u 7,u 258,u 513] := by
  exact ⟨rfl,rfl,by decide,by decide,by decide⟩

theorem complete_ordered_observation :
    (observed .CALLVALUE false spill (u 37)).stack = [u 37,u 258,u 513] ∧
    (observed .CALLVALUE false spill (u 37)).stack ≠ [u 513,u 258,u 37] ∧
    (observed .CALLVALUE false spill (u 37)).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x34,0x00] ∧
    (observed .CALLVALUE false spill (u 37)).pc = u 4 ∧
    (observed .CALLVALUE false spill (u 37)).gasAvailable = u 7 ∧
    (observed .CALLVALUE false spill (u 37)).execLength = 42 ∧
    (observed .CALLVALUE false spill (u 37)).memory.data.toList = [0xaa,0xbb]++List.replicate 30 0 ∧
    (observed .CALLVALUE false spill (u 37)).activeWords = u 1 ∧
    (observed .CALLVALUE false spill (u 37)).returnData.data.toList = [0xcc,0xdd] ∧
    (observed .CALLVALUE false spill (u 37)).H_return.data.toList = [0xee,0xff] ∧
    (observed .CALLVALUE false spill (u 37)).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (observed .CALLVALUE false spill (u 37)).accountMap = accounts ∧
    (observed .CALLVALUE false spill (u 37)).σ₀ = accounts ∧
    (observed .CALLVALUE false spill (u 37)).substate = (seed 9 false).substate := by
  exact ⟨rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms address_client
#print axioms caller_client
#print axioms callvalue_client
#print axioms legal_capacity
#print axioms resource_order
#print axioms distinct_identities
#print axioms complete_ordered_observation
end SolidityBridge.RoadmapV15.P10.InvocationEnvironmentControls
