import SolidityBridge.RoadmapV15.P10.UintNotFixtures

/-! Typed selected complement clients and populated whole-State observations.
Canonical uint source evaluation is consumed from its existing certificate.
The nonempty supplied array has no global scanner-correctness claim. -/
namespace SolidityBridge.RoadmapV15.P10.UintNotControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open UintNotFixtures
open WordPushFixtures (seed before after spill u)

private theorem execute (a : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 supplied (input 3 false (a::tail)) =
      .ok (observed 3 false a tail (~~~a)) := by
  have h := (uint_not_agreement supplied (site 3 false) a tail room (by decide) 0).2.1
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem producer_client (a : PrimTy.uint.Denote) :
    Scalar.run Scalar.uintNot.code (Scalar.encodeValue .uint a::spill) =
      (UnOp.bnot.evalT (p := .uint) rfl a).map (fun r => Scalar.encodeValue .uint r::spill) ∧
    Assembly.driverSteps 1 2 supplied (input 11 true (Scalar.encodeValue .uint a::spill)) =
      .ok (observed 11 true (Scalar.encodeValue .uint a) spill (~~~Scalar.encodeValue .uint a)) ∧
    EVM.X 2 supplied (input 11 true (Scalar.encodeValue .uint a::spill)) =
      EVM.X 1 supplied (observed 11 true (Scalar.encodeValue .uint a) spill (~~~Scalar.encodeValue .uint a)) := by
  have h := selected_uint_not_agreement supplied (site 11 true) a spill (by decide) (by decide) 0
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

/-- A nonzero intrinsic uint inhabits both source and fetched conclusions. -/
theorem typed_258 :
    let a : PrimTy.uint.Denote := ⟨258,by decide⟩
    Scalar.run Scalar.uintNot.code (Scalar.encodeValue .uint a::spill) =
      (UnOp.bnot.evalT (p := .uint) rfl a).map (fun r => Scalar.encodeValue .uint r::spill) ∧
    Assembly.driverSteps 1 2 supplied (input 11 true (258::spill)) =
      .ok (observed 11 true 258 spill (BitVec.ofNat 256 (2^256-259))) ∧
    EVM.X 2 supplied (input 11 true (258::spill)) =
      EVM.X 1 supplied (observed 11 true 258 spill (BitVec.ofNat 256 (2^256-259))) := by
  exact producer_client ⟨258,by decide⟩

theorem raw_boundaries :
    Assembly.driverSteps 1 2 supplied (input 3 false (0::spill)) =
      .ok (observed 3 false 0 spill (BitVec.ofNat 256 (2^256-1))) ∧
    Assembly.driverSteps 1 2 supplied (input 3 false (BitVec.ofNat 256 (2^256-1)::spill)) =
      .ok (observed 3 false (BitVec.ofNat 256 (2^256-1)) spill 0) ∧
    Assembly.driverSteps 1 2 supplied (input 3 false (BitVec.ofNat 256 (2^255)::spill)) =
      .ok (observed 3 false (BitVec.ofNat 256 (2^255)) spill (BitVec.ofNat 256 (2^255-1))) := by
  exact ⟨execute _ _ (by decide),execute _ _ (by decide),execute _ _ (by decide)⟩

/-- The full legal unary input preserves every caller-tail word. -/
theorem full_input_stack :
    Assembly.driverSteps 1 2 supplied (input 3 false (258::List.replicate 1023 513)) =
      .ok (observed 3 false 258 (List.replicate 1023 513) (BitVec.ofNat 256 (2^256-259))) := by
  exact execute _ _ (by simp only [List.length_replicate];decide)

theorem refused_resources :
    Assembly.driverSteps 1 2 supplied (input 3 false []) = .error .StackUnderflow ∧
    Assembly.driverSteps 1 2 supplied (input 2 false []) = .error .OutOfGass ∧
    Assembly.driverSteps 1 1 supplied (input 0 false []) = .error .OutOfFuel := by
  exact ⟨rfl,rfl,rfl⟩

theorem values_and_ordered_observations :
    (~~~(258 : Scalar.Word)).toNat = 2^256-259 ∧
    (UInt256.lnot (u 258)).toNat ≠ (UInt256.isZero (u 258)).toNat ∧
    (UInt256.lnot (u 0)).toNat ≠ 0 ∧
    (~~~(BitVec.ofNat 256 (2^256+258))).toNat = 2^256-259 ∧
    supplied.toList = [u 37,u 99] ∧
    (input 11 true (258::spill)).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x19,0x00] ∧
    (input 11 true (258::spill)).executionEnv.code.data.toList ≠ [0x60,0x7f,0x50,0x15,0x00] ∧
    (input 11 true (258::spill)).stack = [u 258,u 258,u 513] ∧
    (observed 11 true 258 spill (~~~258)).stack = [u (2^256-259),u 258,u 513] ∧
    (observed 11 true 258 spill (~~~258)).pc.toNat = 4 ∧
    (observed 11 true 258 spill (~~~258)).gasAvailable.toNat = 8 ∧
    (observed 11 true 258 spill (~~~258)).execLength = 42 ∧
    (observed 11 true 258 spill (~~~258)).memory.data.toList = ([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0 ∧
    (observed 11 true 258 spill (~~~258)).returnData.data.toList = [0xcc,0xdd] ∧
    (observed 11 true 258 spill (~~~258)).H_return.data.toList = [0xee,0xff] ∧
    (observed 11 true 258 spill (~~~258)).executionEnv.calldata.data.toList = [0x11,0x22,0x33] := by
  decide

#print axioms producer_client
#print axioms typed_258
#print axioms raw_boundaries
#print axioms full_input_stack
#print axioms refused_resources
#print axioms values_and_ordered_observations
end SolidityBridge.RoadmapV15.P10.UintNotControls
