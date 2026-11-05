import SolidityBridge.RoadmapV15.P10.LinkedJumpFixtures

/-! Nontrivial clients of the published linked-loop reference certificate.
The entire Backend image aligns; no preceding source/prefix run is claimed.
Reference 72 is a real decoded target; following byte 73 is STOP, not a target. -/
namespace SolidityBridge.RoadmapV15.P10.LinkedJumpControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open LinkedJumpFixtures
open WordPushFixtures (u)

private theorem ref72 : 72 ∈ program.checked.image.refs := by
  change 72 ∈ [0,72]
  exact List.Mem.tail 0 (List.Mem.head [])

private theorem aligned (gas : Nat) (perm : Bool) :
    (site gas perm).state.executionEnv.code = program.frame.executionEnv.code := by rfl

private theorem execute (rest : List UInt256) (room : rest.length+2 ≤ 1024) :
    Assembly.driverSteps 1 2 program.validJumps (input 10 false (u 2) rest) =
      .ok (observed 10 false (u 2) rest 72) := by
  have h := (linked_reference_jumpi program 72 ref72 (site 10 false) (aligned 10 false)
    (u 2) rest room (by decide) 0).2.2.1
  simpa only [input,observed,site,WordPushFixtures.seed,before,after,u,jumpMemberSite,Site.state,
    Assembly.chargedPrepare] using h

theorem certified_exit :
    (u 72).toNat = 72 ∧
    EVM.decode (input 10 false (u 2) tail).executionEnv.code (u 72) = some (.JUMPDEST,none) ∧
    Assembly.driverSteps 1 2 program.validJumps (input 10 false (u 2) tail) =
      .ok (observed 10 false (u 2) tail 72) ∧
    EVM.X 2 program.validJumps (input 10 false (u 2) tail) =
      EVM.X 1 program.validJumps (observed 10 false (u 2) tail 72) := by
  have h := linked_reference_jumpi program 72 ref72 (site 10 false) (aligned 10 false)
    (u 2) tail (by decide) (by decide) 0
  simpa only [input,observed,site,WordPushFixtures.seed,before,after,u,jumpMemberSite,Site.state,
    Assembly.chargedPrepare] using h

theorem writable_zero :
    Assembly.driverSteps 1 2 program.validJumps (input 27 true (u 0) tail) =
      .ok (observed 27 true (u 0) tail 37) ∧
    EVM.X 2 program.validJumps (input 27 true (u 0) tail) =
      EVM.X 1 program.validJumps (observed 27 true (u 0) tail 37) := by
  have h := (linked_reference_jumpi program 72 ref72 (site 27 true) (aligned 27 true)
    (u 0) tail (by decide) (by decide) 0).2.2
  simpa only [input,observed,site,WordPushFixtures.seed,before,after,u,jumpMemberSite,Site.state,
    Assembly.chargedPrepare] using h

theorem legal_boundaries :
    Assembly.driverSteps 1 2 program.validJumps (input 10 false (u 2) []) =
      .ok (observed 10 false (u 2) [] 72) ∧
    Assembly.driverSteps 1 2 program.validJumps (input 10 false (u 2) (List.replicate 1022 (u 258))) =
      .ok (observed 10 false (u 2) (List.replicate 1022 (u 258)) 72) := by
  exact ⟨execute _ (by decide),execute _ (by simp only [List.length_replicate];decide)⟩

theorem stop_is_not_a_reference :
    73 ∉ program.checked.image.refs ∧
    (Assembly.driverSteps 1 2 program.validJumps
      (jumpMemberSite (site 10 false) (u 73) (u 2) tail).state = .error .BadJumpDestination ∧
    EVM.X 1 program.validJumps
      (jumpMemberSite (site 10 false) (u 73) (u 2) tail).state = .error .BadJumpDestination) := by
  refine ⟨?_,jump_missing_refusal program.validJumps (site 10 false) (u 73) (u 2) tail
    (by decide) (by decide) (by decide) 0⟩
  change 73 ∉ [0,72]
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  decide

theorem complete_ordered_observations :
    program.validJumps.toList = [u 0,u 1,u 37,u 72] ∧
    (input 10 false (u 2) tail).executionEnv.code.data.toList =
      [0x5b,0x5b,0x15,0x7f] ++ List.replicate 31 0 ++
        [0x48,0x57,0x5b,0x7f] ++ List.replicate 32 0 ++ [0x56,0x5b,0x00] ∧
    (input 10 false (u 2) tail).pc = u 36 ∧
    (input 10 false (u 2) tail).stack = [u 72,u 2,u 258,u 513] ∧
    (observed 10 false (u 2) tail 72).stack = [u 258,u 513] ∧
    (observed 10 false (u 2) tail 72).stack ≠ [u 513,u 258] ∧
    (observed 10 false (u 2) tail 72).pc ≠ u 37 ∧
    (observed 27 true (u 0) tail 37).pc ≠ u 72 ∧
    (observed 10 false (u 2) tail 72).gasAvailable = u 0 ∧
    (observed 27 true (u 0) tail 37).gasAvailable = u 17 ∧
    (observed 10 false (u 2) tail 72).execLength = 42 ∧
    (observed 10 false (u 2) tail 72).memory.data.toList = [0xaa,0xbb] ++ List.replicate 30 0 ∧
    (observed 10 false (u 2) tail 72).returnData.data.toList = [0xcc,0xdd] ∧
    (observed 10 false (u 2) tail 72).H_return.data.toList = [0xee,0xff] ∧
    (observed 10 false (u 2) tail 72).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (observed 10 false (u 2) tail 72).accountMap = WordPushFixtures.accounts ∧
    (observed 10 false (u 2) tail 72).σ₀ = WordPushFixtures.accounts := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms certified_exit
#print axioms writable_zero
#print axioms legal_boundaries
#print axioms stop_is_not_a_reference
#print axioms complete_ordered_observations
end SolidityBridge.RoadmapV15.P10.LinkedJumpControls
