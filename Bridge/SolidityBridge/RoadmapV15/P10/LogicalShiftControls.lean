import SolidityBridge.RoadmapV15.P10.LogicalShiftFixtures

/-! Inhabited selected-source clients and actual two-step complete-State controls.
Count saturation uses the full word; no source signed-count admission is changed. -/
namespace SolidityBridge.RoadmapV15.P10.LogicalShiftControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open LogicalShiftFixtures
open WordPushFixtures (seed before after spill u)

private theorem execute_shl (value count : Scalar.Word) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 2 4 #[] (input .SHL 6 false value count tail) =
      .ok (observed .SHL 6 false value count tail (if count.toNat < 256 then value <<< count.toNat else 0)) := by
  have h := (logical_shl_execution (seed 6 false) before after value count tail fits room (by decide) 1).2.1
  simpa only [input,observed,seed,before,after,u,logicalShiftInput,logicalShiftSwapped,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem typed_shl_client (value count : PrimTy.uint.Denote) :
    Scalar.run Scalar.uintShl.code (Scalar.encodeValue .uint value::Scalar.encodeValue .uint count::spill) =
      (BinOp.shl.evalT (p := .uint) rfl value count).map (fun r => Scalar.encodeValue .uint r::spill) ∧
    Assembly.driverSteps 2 4 #[] (input .SHL 12 true (Scalar.encodeValue .uint value) (Scalar.encodeValue .uint count) spill) =
      .ok (observed .SHL 12 true (Scalar.encodeValue .uint value) (Scalar.encodeValue .uint count) spill
        (if (Scalar.encodeValue .uint count).toNat < 256 then Scalar.encodeValue .uint value <<< (Scalar.encodeValue .uint count).toNat else 0)) ∧
    EVM.X 4 #[] (input .SHL 12 true (Scalar.encodeValue .uint value) (Scalar.encodeValue .uint count) spill) =
      EVM.X 2 #[] (observed .SHL 12 true (Scalar.encodeValue .uint value) (Scalar.encodeValue .uint count) spill
        (if (Scalar.encodeValue .uint count).toNat < 256 then Scalar.encodeValue .uint value <<< (Scalar.encodeValue .uint count).toNat else 0)) := by
  have h := selected_logical_shl_execution (seed 12 true) before after value count spill fits (by decide) (by decide) 1
  simpa only [input,observed,seed,before,after,u,logicalShiftInput,logicalShiftSwapped,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

private theorem execute_shr (value count : Scalar.Word) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 2 4 #[] (input .SHR 6 false value count tail) =
      .ok (observed .SHR 6 false value count tail (if count.toNat < 256 then value >>> count.toNat else 0)) := by
  have h := (logical_shr_execution (seed 6 false) before after value count tail fits room (by decide) 1).2.1
  simpa only [input,observed,seed,before,after,u,logicalShiftInput,logicalShiftSwapped,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem typed_shr_client (value count : PrimTy.uint.Denote) :
    Scalar.run Scalar.uintShr.code (Scalar.encodeValue .uint value::Scalar.encodeValue .uint count::spill) =
      (BinOp.shr.evalT (p := .uint) rfl value count).map (fun r => Scalar.encodeValue .uint r::spill) ∧
    Assembly.driverSteps 2 4 #[] (input .SHR 12 true (Scalar.encodeValue .uint value) (Scalar.encodeValue .uint count) spill) =
      .ok (observed .SHR 12 true (Scalar.encodeValue .uint value) (Scalar.encodeValue .uint count) spill
        (if (Scalar.encodeValue .uint count).toNat < 256 then Scalar.encodeValue .uint value >>> (Scalar.encodeValue .uint count).toNat else 0)) ∧
    EVM.X 4 #[] (input .SHR 12 true (Scalar.encodeValue .uint value) (Scalar.encodeValue .uint count) spill) =
      EVM.X 2 #[] (observed .SHR 12 true (Scalar.encodeValue .uint value) (Scalar.encodeValue .uint count) spill
        (if (Scalar.encodeValue .uint count).toNat < 256 then Scalar.encodeValue .uint value >>> (Scalar.encodeValue .uint count).toNat else 0)) := by
  have h := selected_logical_shr_execution (seed 12 true) before after value count spill fits (by decide) (by decide) 1
  simpa only [input,observed,seed,before,after,u,logicalShiftInput,logicalShiftSwapped,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem typed_nonzero_clients :
    (Scalar.run Scalar.uintShl.code (3::2::spill) = some (12::spill) ∧
    Assembly.driverSteps 2 4 #[] (input .SHL 12 true 3 2 spill) = .ok (observed .SHL 12 true 3 2 spill 12) ∧
    EVM.X 4 #[] (input .SHL 12 true 3 2 spill) = EVM.X 2 #[] (observed .SHL 12 true 3 2 spill 12)) ∧
    (Scalar.run Scalar.uintShr.code (128::7::spill) = some (1::spill) ∧
    Assembly.driverSteps 2 4 #[] (input .SHR 12 true 128 7 spill) = .ok (observed .SHR 12 true 128 7 spill 1) ∧
    EVM.X 4 #[] (input .SHR 12 true 128 7 spill) = EVM.X 2 #[] (observed .SHR 12 true 128 7 spill 1)) := by
  constructor
  · exact typed_shl_client ⟨3,by decide⟩ ⟨2,by decide⟩
  · have h := typed_shr_client ⟨128,by decide⟩ ⟨7,by decide⟩
    have sourceResult :
        (BinOp.shr.evalT (p := .uint) rfl ⟨128,by decide⟩ ⟨7,by decide⟩).map
          (fun r => Scalar.encodeValue .uint r::spill) = some (1::spill) := by decide
    rw [sourceResult] at h
    exact h

theorem saturation_boundaries :
    Assembly.driverSteps 2 4 #[] (input .SHL 6 false 7 0 spill) = .ok (observed .SHL 6 false 7 0 spill 7) ∧
    Assembly.driverSteps 2 4 #[] (input .SHL 6 false 1 255 spill) = .ok (observed .SHL 6 false 1 255 spill (BitVec.ofNat 256 (2^255))) ∧
    Assembly.driverSteps 2 4 #[] (input .SHL 6 false 7 256 spill) = .ok (observed .SHL 6 false 7 256 spill 0) ∧
    Assembly.driverSteps 2 4 #[] (input .SHR 6 false (BitVec.ofNat 256 (2^256-1)) 255 spill) =
      .ok (observed .SHR 6 false (BitVec.ofNat 256 (2^256-1)) 255 spill 1) ∧
    Assembly.driverSteps 2 4 #[] (input .SHR 6 false (BitVec.ofNat 256 (2^256-1)) 256 spill) =
      .ok (observed .SHR 6 false (BitVec.ofNat 256 (2^256-1)) 256 spill 0) ∧
    Assembly.driverSteps 2 4 #[] (input .SHR 6 false 258 (BitVec.ofNat 256 (2^256-1)) spill) =
      .ok (observed .SHR 6 false 258 (BitVec.ofNat 256 (2^256-1)) spill 0) := by
  exact ⟨execute_shl _ _ _ (by decide),execute_shl _ _ _ (by decide),execute_shl _ _ _ (by decide),
    execute_shr _ _ _ (by decide),execute_shr _ _ _ (by decide),execute_shr _ _ _ (by decide)⟩

theorem full_input_stack :
    Assembly.driverSteps 2 4 #[] (input .SHL 6 false 3 2 (List.replicate 1022 769)) =
      .ok (observed .SHL 6 false 3 2 (List.replicate 1022 769) 12) ∧
    Assembly.driverSteps 2 4 #[] (input .SHR 6 false 128 7 (List.replicate 1022 769)) =
      .ok (observed .SHR 6 false 128 7 (List.replicate 1022 769) 1) := by
  exact ⟨execute_shl _ _ _ (by simp only [List.length_replicate];decide),
    execute_shr _ _ _ (by simp only [List.length_replicate];decide)⟩

theorem refused_resources :
    Assembly.driverSteps 2 3 #[] (input .SHL 2 false 3 2 spill) = .error .OutOfGass ∧
    Assembly.driverSteps 2 3 #[] (input .SHL 5 false 3 2 spill) = .error .OutOfGass ∧
    Assembly.driverSteps 2 2 #[] (input .SHL 6 false 3 2 spill) = .error .OutOfFuel ∧
    Assembly.driverSteps 2 3 #[] (logicalShiftInput (seed 3 false) before after .SHR [128]) = .error .StackUnderflow ∧
    Assembly.driverSteps 2 3 #[] (logicalShiftInput (seed 2 false) before after .SHR [128]) = .error .OutOfGass := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩


theorem values_and_ordered_observations :
    Scalar.run [.op .SHL] (3::2::spill) ≠ some (12::spill) ∧
    Scalar.run Scalar.uintShl.code (7::256::spill) ≠ some (7::spill) ∧
    Scalar.run Scalar.uintShr.code (BitVec.ofNat 256 (2^255)::256::spill) = some (0::spill) ∧
    (BitVec.ofNat 256 (2^255)).sshiftRight 256 ≠ (0 : Scalar.Word) ∧
    (input .SHL 6 false 3 2 spill).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x90,0x1b,0x00] ∧
    (input .SHR 6 false 128 7 spill).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x90,0x1c,0x00] ∧
    (logicalShiftSwapped (seed 6 false) before after .SHL 3 2 spill).stack = [u 2,u 3,u 258,u 513] ∧
    (logicalShiftSwapped (seed 6 false) before after .SHL 3 2 spill).gasAvailable.toNat = 3 ∧
    (logicalShiftSwapped (seed 6 false) before after .SHL 3 2 spill).pc.toNat = 4 ∧
    (logicalShiftSwapped (seed 6 false) before after .SHL 3 2 spill).execLength = 42 ∧
    (observed .SHL 6 false 3 2 spill 12).stack = [u 12,u 258,u 513] ∧
    (observed .SHL 6 false 3 2 spill 12).gasAvailable.toNat = 0 ∧
    (observed .SHL 6 false 3 2 spill 12).pc.toNat = 5 ∧
    (observed .SHL 6 false 3 2 spill 12).execLength = 43 ∧
    (observed .SHL 6 false 3 2 spill 12).memory.data.toList = ([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0 ∧
    (observed .SHL 6 false 3 2 spill 12).returnData.data.toList = [0xcc,0xdd] ∧
    (observed .SHL 6 false 3 2 spill 12).H_return.data.toList = [0xee,0xff] ∧
    (observed .SHL 6 false 3 2 spill 12).executionEnv.calldata.data.toList = [0x11,0x22,0x33] := by
  decide


#print axioms typed_shl_client
#print axioms typed_shr_client
#print axioms typed_nonzero_clients
#print axioms saturation_boundaries
#print axioms full_input_stack
#print axioms refused_resources
#print axioms values_and_ordered_observations
end SolidityBridge.RoadmapV15.P10.LogicalShiftControls
