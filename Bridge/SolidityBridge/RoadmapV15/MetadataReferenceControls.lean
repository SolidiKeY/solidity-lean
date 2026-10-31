import SolidityBridge.RoadmapV15.MetadataReference

/-! Exact numeric/ABI/packed metadata bytes and actual reference push controls.
These fixtures preserve metadata refusal and make no source resolver or fetched
code/resource/Osaka claim. -/
namespace SolidityBridge.RoadmapV15.MetadataReferenceControls
open Solidity Solidity.Backend
private def sel : Fin (2 ^ 32) := ⟨0x01020304, by decide⟩
private def receiver : Environment.Address := environmentReferenceAddress (.ofNat 7)
example : (Environment.selectorCode sel).encode = [0x63, 1, 2, 3, 4] := by decide +kernel
example : (Environment.selectorAbiCode sel).encode = [0x7f, 1, 2, 3, 4] ++ List.replicate 28 0 := by decide +kernel
example : (Environment.functionCode receiver sel).encode = [0x77] ++ List.replicate 19 0 ++ [7, 1, 2, 3, 4] := by decide +kernel
example : Environment.declarationCode { callable := .abi .externalFn .selected none } = none := rfl
example : Environment.declarationCode { callable := .constructor } = none := rfl
example : (Solidity.Evm.External.Memory.encoding (EvmYul.UInt256.ofNat sel.val)).toList =
    List.replicate 28 0 ++ [1, 2, 3, 4] := by
  rw [reference_encoding_bytes]; decide +kernel
example : (Solidity.Evm.External.Memory.encoding
    (EvmYul.UInt256.ofNat (Environment.selectorAbiValue sel).val)).toList =
    [1, 2, 3, 4] ++ List.replicate 28 0 := by
  rw [reference_encoding_bytes]; decide +kernel
example : (toBytesBE 4 sel.val).toList ≠ (toBytesBE 4 sel.val).toList.reverse := by decide +kernel
example : (toBytesBE 4 sel.val).toList ≠ [1, 2, 3] := by decide +kernel
example : EvmYul.uInt256OfByteArray (toBytesBE 4 sel.val).toList.toByteArray ≠
    EvmYul.UInt256.ofNat (Environment.selectorAbiValue sel).val := by
  rw [metadata_reference_read ⟨4, by decide⟩ ⟨sel.val, sel.isLt⟩]
  decide +kernel
example : EvmYul.uInt256OfByteArray (toBytesBE 0 0).toList.toByteArray = .ofNat 0 :=
  metadata_reference_read ⟨0, by decide⟩ ⟨0, by decide⟩
example : EvmYul.uInt256OfByteArray (toBytesBE 32 (2 ^ 256 - 1)).toList.toByteArray =
    .ofNat (2 ^ 256 - 1) := metadata_reference_read ⟨32, by decide⟩ ⟨_, by decide⟩
example (s : EvmYul.EVM.State) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (.PUSH4, some
      (EvmYul.uInt256OfByteArray (toBytesBE 4 sel.val).toList.toByteArray, 4)))
      {s with stack := [.ofNat 258, .ofNat 513]} = .ok
      ((Solidity.Evm.External.Memory.prepare {s with stack := [.ofNat 258, .ofNat 513]}).replaceStackAndIncrPC
        [.ofNat sel.val, .ofNat 258, .ofNat 513] 5) :=
  (metadata_selector_reference sel [] s [.ofNat 258, .ofNat 513] fuel).2
example (s : EvmYul.EVM.State) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (.PUSH32, some
      (EvmYul.uInt256OfByteArray (toBytesBE 32 (Environment.selectorAbiValue sel).val).toList.toByteArray, 32)))
      {s with stack := [.ofNat 258, .ofNat 513]} = .ok
      ((Solidity.Evm.External.Memory.prepare {s with stack := [.ofNat 258, .ofNat 513]}).replaceStackAndIncrPC
        [.ofNat (sel.val * 2 ^ 224), .ofNat 258, .ofNat 513] 33) :=
  metadata_abi_reference sel s [.ofNat 258, .ofNat 513] fuel
example (s : EvmYul.EVM.State) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (.PUSH24, some
      (EvmYul.uInt256OfByteArray (toBytesBE 24 (Environment.packedFunction receiver sel).val).toList.toByteArray, 24)))
      {s with stack := [.ofNat 258, .ofNat 513]} = .ok
      ((Solidity.Evm.External.Memory.prepare {s with stack := [.ofNat 258, .ofNat 513]}).replaceStackAndIncrPC
        [.ofNat (receiver.1.1.toNat * 2 ^ 32 + sel.val), .ofNat 258, .ofNat 513] 25) :=
  metadata_function_reference receiver sel s [.ofNat 258, .ofNat 513] fuel
example (s : EvmYul.EVM.State) : EvmYul.EVM.step 1 0 (some (.PUSH4, none)) s = .error .StackUnderflow := rfl
example (s : EvmYul.EVM.State) : EvmYul.EVM.step 0 0 (some (.PUSH4, none)) s = .error .OutOfFuel := rfl
#print axioms metadata_reference_read
#print axioms metadata_selector_reference
#print axioms metadata_abi_reference
#print axioms metadata_function_reference
end SolidityBridge.RoadmapV15.MetadataReferenceControls
