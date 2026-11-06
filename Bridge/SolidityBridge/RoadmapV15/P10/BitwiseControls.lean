import SolidityBridge.RoadmapV15.P10.BitwiseFixtures

/-! Complete-State clients at nonzero opcode sites and different gas/permissions.
These local primitive checks do not establish compiler/source/Osaka coverage. -/
namespace SolidityBridge.RoadmapV15.P10.BitwiseControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open BitwiseFixtures
open WordPushFixtures (seed before after spill u)

theorem and_client :
    Scalar.step (.op .AND) (0xaa55::0x0ff0::spill) = some (0x0a50::spill) ∧
    Assembly.driverSteps 1 2 #[] (input .AND 3 false (0xaa55::0x0ff0::spill)) =
      .ok (observed .AND false 0xaa55 0x0ff0 spill 0x0a50) ∧
    EVM.X 2 #[] (input .AND 3 false (0xaa55::0x0ff0::spill)) =
      EVM.X 1 #[] (observed .AND false 0xaa55 0x0ff0 spill 0x0a50) := by
  have h := bitwise_and_agreement (site .AND 3 false) 0xaa55 0x0ff0 spill (by decide) (by decide) 0
  simpa only [input,observed,observedAt,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem or_client :
    Scalar.step (.op .OR) (0xaa55::0x0ff0::spill) = some (0xaff5::spill) ∧
    Assembly.driverSteps 1 2 #[] (input .OR 11 true (0xaa55::0x0ff0::spill)) =
      .ok (observedAt .OR 11 true 0xaa55 0x0ff0 spill 0xaff5) ∧
    EVM.X 2 #[] (input .OR 11 true (0xaa55::0x0ff0::spill)) =
      EVM.X 1 #[] (observedAt .OR 11 true 0xaa55 0x0ff0 spill 0xaff5) := by
  have h := bitwise_or_agreement (site .OR 11 true) 0xaa55 0x0ff0 spill (by decide) (by decide) 0
  simpa only [input,observed,observedAt,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem xor_client :
    Scalar.step (.op .XOR) (0xaa55::0x0ff0::spill) = some (0xa5a5::spill) ∧
    Assembly.driverSteps 1 2 #[] (input .XOR 3 false (0xaa55::0x0ff0::spill)) =
      .ok (observed .XOR false 0xaa55 0x0ff0 spill 0xa5a5) ∧
    EVM.X 2 #[] (input .XOR 3 false (0xaa55::0x0ff0::spill)) =
      EVM.X 1 #[] (observed .XOR false 0xaa55 0x0ff0 spill 0xa5a5) := by
  have h := bitwise_xor_agreement (site .XOR 3 false) 0xaa55 0x0ff0 spill (by decide) (by decide) 0
  simpa only [input,observed,observedAt,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

/-- Valid input1024 shrinks to1023; this is not an over-limit-state refusal. -/
theorem full_input_stack :
    Assembly.driverSteps 1 2 #[] (input .AND 3 false (0xaa55::0x0ff0::List.replicate 1022 258)) =
      .ok (observed .AND false 0xaa55 0x0ff0 (List.replicate 1022 258) 0x0a50) := by
  have h := (bitwise_and_agreement (site .AND 3 false) 0xaa55 0x0ff0 (List.replicate 1022 258)
    (by simp only [List.length_replicate];decide) (by decide) 0).2.1
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

/-- Raw gate probe ONLY: input1026 is outside the well-formed stack profile. -/
private theorem raw_overlimit :
    Assembly.driverSteps 1 2 #[] (input .AND 3 false (0xaa55::0x0ff0::List.replicate 1024 258)) =
      .error .StackOverflow := by
  let start := input .AND 3 false (0xaa55::0x0ff0::List.replicate 1024 258)
  have count : start.stack.length = 1026 := by
    change ((0xaa55::0x0ff0::List.replicate 1024 (258 : Scalar.Word)).map
      (fun w => UInt256.mk w.toFin)).length = 1026
    simp only [List.length_map,List.length_cons,List.length_replicate]
  have expansion : EVM.memoryExpansionCost start .AND = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : start.gasAvailable-UInt256.ofNat 0 = start.gasAvailable := by
    change UInt256.mk (start.gasAvailable.val-0) = start.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' start .AND = 3 := rfl
  have gate : Assembly.driverGate #[] start .AND = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,count]
    rfl
  have decoded : EVM.decode start.executionEnv.code start.pc = some (.AND,none) :=
    DecoderAgreement.decode_all (modularSite (site .AND 3 false)
      (0xaa55::0x0ff0::List.replicate 1024 258))
  change Assembly.driverSteps 1 2 #[] start = _
  simp only [Assembly.driverSteps]
  rw [decoded]
  dsimp only [Option.option,bind,Except.bind]
  rw [gate]

/-- Gas/arity/fuel refusals plus a separately labelled non-profile raw probe. -/
theorem refused_resources :
(let input := SolidityBridge.RoadmapV15.P10.BitwiseFixtures.input;
 Solidity.Evm.External.Assembly.driverSteps 1 2 #[] (input .AND 3 false [0xaa55]) = .error .StackUnderflow ∧
 Solidity.Evm.External.Assembly.driverSteps 1 2 #[] (input .AND 2 false [0xaa55]) = .error .OutOfGass ∧
 Solidity.Evm.External.Assembly.driverSteps 1 1 #[] (input .AND 0 false []) = .error .OutOfFuel ∧
 Solidity.Evm.External.Assembly.driverSteps 1 2 #[] (input .AND 3 false (0xaa55::0x0ff0::List.replicate 1024 258)) = .error .StackOverflow)
 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · exact raw_overlimit

theorem values_and_ordered_observations :
(let u := SolidityBridge.RoadmapV15.P10.WordPushFixtures.u;
 let tail := SolidityBridge.RoadmapV15.P10.WordPushFixtures.spill;
 let observed := SolidityBridge.RoadmapV15.P10.BitwiseFixtures.observed;
 let observedAt := SolidityBridge.RoadmapV15.P10.BitwiseFixtures.observedAt;
 let top : Solidity.Backend.Scalar.Word := BitVec.ofNat 256 (2^256-1);
 (top &&& 255) = 255 ∧ ((0 : Solidity.Backend.Scalar.Word) ||| top) = top ∧ (top ^^^ top) = 0 ∧
 (EvmYul.UInt256.xor (u (2^255)) (u 0)).toNat = 2^255 ∧
 ((0xff00 : Solidity.Backend.Scalar.Word) &&& 0xff) = 0 ∧
 ((0xff00 : Solidity.Backend.Scalar.Word) ||| 0xff) = ((0xff00 : Solidity.Backend.Scalar.Word) ^^^ 0xff) ∧
 (0x0a50 : Solidity.Backend.Scalar.Word) ≠ 0xaff5 ∧ (0xaff5 : Solidity.Backend.Scalar.Word) ≠ 0xa5a5 ∧
 (observed .AND false 0xaa55 0x0ff0 tail 0x0a50).stack = [u 0x0a50,u 258,u 513] ∧
 (observedAt .OR 11 true 0xaa55 0x0ff0 tail 0xaff5).stack = [u 0xaff5,u 258,u 513] ∧
 (observed .XOR false 0xaa55 0x0ff0 tail 0xa5a5).stack = [u 0xa5a5,u 258,u 513] ∧
 (observed .AND false 0xaa55 0x0ff0 tail 0x0a50).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x16,0x00] ∧
 (observedAt .OR 11 true 0xaa55 0x0ff0 tail 0xaff5).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x17,0x00] ∧
 (observed .XOR false 0xaa55 0x0ff0 tail 0xa5a5).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x18,0x00] ∧
 (observedAt .OR 11 true 0xaa55 0x0ff0 tail 0xaff5).gasAvailable.toNat = 8 ∧
 (observed .AND false 0xaa55 0x0ff0 tail 0x0a50).memory.data.toList = ([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0 ∧
 (observed .AND false 0xaa55 0x0ff0 tail 0x0a50).returnData.data.toList = [0xcc,0xdd] ∧
 (observed .AND false 0xaa55 0x0ff0 tail 0x0a50).H_return.data.toList = [0xee,0xff] ∧
 (observed .AND false 0xaa55 0x0ff0 tail 0x0a50).executionEnv.calldata.data.toList = [0x11,0x22,0x33])
 := by
  decide

#print axioms and_client
#print axioms or_client
#print axioms xor_client
#print axioms full_input_stack
#print axioms refused_resources
#print axioms values_and_ordered_observations
end SolidityBridge.RoadmapV15.P10.BitwiseControls
