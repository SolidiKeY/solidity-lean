import SolidityBridge.RoadmapV15.P10.WrappingArithmeticFixtures

/-! Selected typed clients, actual full State/X and wrap/order/resource negatives.
These are wrapping operations; checked operations retain their separate failures. -/
namespace SolidityBridge.RoadmapV15.P10.WrappingArithmeticControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WrappingArithmeticFixtures
open WordPushFixtures (seed before after spill u)

private theorem execute_add (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 1 2 supplied (input .ADD 12 false (a::b::tail)) =
      .ok (observed .ADD 12 false 3 a b tail (a + b)) := by
  have h := (wrapping_add_agreement supplied (site .ADD 12 false) a b tail room (by decide) 0).2.1
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem selected_add_client (a b : PrimTy.uint.Denote) :
    Scalar.run Scalar.wrappingAdd.code (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::spill) =
      (BinOp.addW.evalT (p := .uint) rfl a b).map (fun r => Scalar.encodeValue .uint r::spill) ∧
    Assembly.driverSteps 1 2 supplied (input .ADD 12 true (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::spill)) =
      .ok (observed .ADD 12 true 3 (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill
        (Scalar.encodeValue .uint a + Scalar.encodeValue .uint b)) ∧
    EVM.X 2 supplied (input .ADD 12 true (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::spill)) =
      EVM.X 1 supplied (observed .ADD 12 true 3 (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill
        (Scalar.encodeValue .uint a + Scalar.encodeValue .uint b)) := by
  have h := selected_wrapping_add_agreement supplied (site .ADD 12 true) a b spill (by decide) (by decide) 0
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

private theorem execute_sub (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 1 2 supplied (input .SUB 12 false (a::b::tail)) =
      .ok (observed .SUB 12 false 3 a b tail (a - b)) := by
  have h := (wrapping_sub_agreement supplied (site .SUB 12 false) a b tail room (by decide) 0).2.1
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem selected_sub_client (a b : PrimTy.uint.Denote) :
    Scalar.run Scalar.wrappingSub.code (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::spill) =
      (BinOp.subW.evalT (p := .uint) rfl a b).map (fun r => Scalar.encodeValue .uint r::spill) ∧
    Assembly.driverSteps 1 2 supplied (input .SUB 12 true (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::spill)) =
      .ok (observed .SUB 12 true 3 (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill
        (Scalar.encodeValue .uint a - Scalar.encodeValue .uint b)) ∧
    EVM.X 2 supplied (input .SUB 12 true (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::spill)) =
      EVM.X 1 supplied (observed .SUB 12 true 3 (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill
        (Scalar.encodeValue .uint a - Scalar.encodeValue .uint b)) := by
  have h := selected_wrapping_sub_agreement supplied (site .SUB 12 true) a b spill (by decide) (by decide) 0
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

private theorem execute_mul (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 1 2 supplied (input .MUL 12 false (a::b::tail)) =
      .ok (observed .MUL 12 false 5 a b tail (a * b)) := by
  have h := (wrapping_mul_agreement supplied (site .MUL 12 false) a b tail room (by decide) 0).2.1
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem selected_mul_client (a b : PrimTy.uint.Denote) :
    Scalar.run Scalar.wrappingMul.code (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::spill) =
      (BinOp.mulW.evalT (p := .uint) rfl a b).map (fun r => Scalar.encodeValue .uint r::spill) ∧
    Assembly.driverSteps 1 2 supplied (input .MUL 12 true (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::spill)) =
      .ok (observed .MUL 12 true 5 (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill
        (Scalar.encodeValue .uint a * Scalar.encodeValue .uint b)) ∧
    EVM.X 2 supplied (input .MUL 12 true (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::spill)) =
      EVM.X 1 supplied (observed .MUL 12 true 5 (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) spill
        (Scalar.encodeValue .uint a * Scalar.encodeValue .uint b)) := by
  have h := selected_wrapping_mul_agreement supplied (site .MUL 12 true) a b spill (by decide) (by decide) 0
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

/-- Inhabited intrinsic uint underflow wraps, with actual source and native results. -/
theorem typed_wrap_subtraction :
    Scalar.run Scalar.wrappingSub.code (0::1::spill) = some (BitVec.ofNat 256 (2^256-1)::spill) ∧
    Assembly.driverSteps 1 2 supplied (input .SUB 12 true (0::1::spill)) =
      .ok (observed .SUB 12 true 3 0 1 spill (BitVec.ofNat 256 (2^256-1))) ∧
    EVM.X 2 supplied (input .SUB 12 true (0::1::spill)) =
      EVM.X 1 supplied (observed .SUB 12 true 3 0 1 spill (BitVec.ofNat 256 (2^256-1))) := by
  exact selected_sub_client ⟨0,by decide⟩ ⟨1,by decide⟩

theorem wrap_boundaries :
    Assembly.driverSteps 1 2 supplied (input .ADD 12 false (BitVec.ofNat 256 (2^256-1)::1::spill)) =
      .ok (observed .ADD 12 false 3 (BitVec.ofNat 256 (2^256-1)) 1 spill 0) ∧
    Assembly.driverSteps 1 2 supplied (input .SUB 12 false (0::1::spill)) =
      .ok (observed .SUB 12 false 3 0 1 spill (BitVec.ofNat 256 (2^256-1))) ∧
    Assembly.driverSteps 1 2 supplied (input .MUL 12 false (BitVec.ofNat 256 (2^255)::2::spill)) =
      .ok (observed .MUL 12 false 5 (BitVec.ofNat 256 (2^255)) 2 spill 0) := by
  exact ⟨execute_add _ _ _ (by decide),execute_sub _ _ _ (by decide),execute_mul _ _ _ (by decide)⟩

/-- Legal input1024 becomes output1023, keeping every tail word. -/
theorem full_input_stack :
    Assembly.driverSteps 1 2 supplied (input .ADD 12 false (258::513::List.replicate 1022 769)) =
      .ok (observed .ADD 12 false 3 258 513 (List.replicate 1022 769) 771) ∧
    Assembly.driverSteps 1 2 supplied (input .SUB 12 false (513::258::List.replicate 1022 769)) =
      .ok (observed .SUB 12 false 3 513 258 (List.replicate 1022 769) 255) ∧
    Assembly.driverSteps 1 2 supplied (input .MUL 12 false (258::513::List.replicate 1022 769)) =
      .ok (observed .MUL 12 false 5 258 513 (List.replicate 1022 769) 132354) := by
  exact ⟨execute_add _ _ _ (by simp only [List.length_replicate];decide),
    execute_sub _ _ _ (by simp only [List.length_replicate];decide),
    execute_mul _ _ _ (by simp only [List.length_replicate];decide)⟩

theorem refused_resources :
    Assembly.driverSteps 1 2 supplied (input .ADD 2 false []) = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 supplied (input .SUB 3 false [258]) = .error .StackUnderflow ∧
    Assembly.driverSteps 1 2 supplied (input .MUL 4 false [258]) = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 supplied (input .MUL 5 false [258]) = .error .StackUnderflow ∧
    Assembly.driverSteps 1 1 supplied (input .MUL 0 false []) = .error .OutOfFuel := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem values_and_ordered_observations :
    (BinOp.sub.evalT (p := .uint) rfl ⟨0,by decide⟩ ⟨1,by decide⟩) = none ∧
    (BinOp.subW.evalT (p := .uint) rfl ⟨0,by decide⟩ ⟨1,by decide⟩) ≠ none ∧
    UInt256.sub (u 0) (u 1) ≠ UInt256.sub (u 1) (u 0) ∧
    EVM.C' (input .ADD 12 false [258,513]) .ADD = 3 ∧
    EVM.C' (input .MUL 12 false [258,513]) .MUL = 5 ∧
    supplied.toList = [u 37,u 99] ∧
    (input .ADD 12 true (258::513::spill)).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x01,0x00] ∧
    (input .SUB 12 true (258::513::spill)).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x03,0x00] ∧
    (input .MUL 12 true (258::513::spill)).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x02,0x00] ∧
    (input .SUB 12 true (258::513::spill)).stack = [u 258,u 513,u 258,u 513] ∧
    (observed .MUL 12 true 5 258 513 spill 132354).stack = [u 132354,u 258,u 513] ∧
    (observed .MUL 12 true 5 258 513 spill 132354).pc.toNat = 4 ∧
    (observed .MUL 12 true 5 258 513 spill 132354).gasAvailable.toNat = 7 ∧
    (observed .MUL 12 true 5 258 513 spill 132354).execLength = 42 ∧
    (observed .MUL 12 true 5 258 513 spill 132354).memory.data.toList = ([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0 ∧
    (observed .MUL 12 true 5 258 513 spill 132354).returnData.data.toList = [0xcc,0xdd] ∧
    (observed .MUL 12 true 5 258 513 spill 132354).H_return.data.toList = [0xee,0xff] ∧
    (observed .MUL 12 true 5 258 513 spill 132354).executionEnv.calldata.data.toList = [0x11,0x22,0x33] := by
  decide

#print axioms selected_add_client
#print axioms selected_sub_client
#print axioms selected_mul_client
#print axioms typed_wrap_subtraction
#print axioms wrap_boundaries
#print axioms full_input_stack
#print axioms refused_resources
#print axioms values_and_ordered_observations
end SolidityBridge.RoadmapV15.P10.WrappingArithmeticControls
