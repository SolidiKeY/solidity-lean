import Solidity.Backend.Environment.Metadata
import SolidityBridge.RoadmapV15.EnvironmentReference

/-! Actual reference immediate reading and supplied PUSH4/24/32 dispatch for
published canonical selector/address-function metadata. No declaration resolver,
raw msg.sig admission, fetched-decoder/code association, gas/X/Osaka or compiler
correctness is added. Missing canonical metadata remains the producer's refusal.
-/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend

/-- Exact width/byte order for every bounded metadata immediate, including0/32.
Uses the actual reference reader, not a copied word decoder. -/
theorem metadata_reference_read (width : Fin 33) (v : Fin (256 ^ width.val)) :
    EvmYul.uInt256OfByteArray (toBytesBE width.val v.val).toList.toByteArray =
      EvmYul.UInt256.ofNat v.val := by
  unfold EvmYul.uInt256OfByteArray
  change EvmYul.UInt256.ofNat (EvmYul.fromBytesBigEndian
    (toBytesBE width.val v.val).toList.toByteArray.data.toList) = _
  rw [Solidity.Evm.External.Memory.list_bytes, Array.toArray_toList,
    reference_big_reader, ofBytesBE_toBytesBE width.val v.val v.isLt]

/-- The committed numeric selector is low-aligned; both complete stack tails
and the real reference PC increment are retained. -/
theorem metadata_selector_reference (sel : Fin (2 ^ 32))
    (tail : List Solidity.Backend.Environment.Word) (s : EvmYul.EVM.State)
    (referenceTail : List EvmYul.UInt256) (fuel : Nat) :
    Solidity.Backend.Environment.pushStep (Solidity.Backend.Environment.selectorCode sel) tail =
      some (Solidity.Backend.Environment.selectorWord sel :: tail) ∧
    EvmYul.EVM.step (fuel + 1) 0 (some (.PUSH4, some
      (EvmYul.uInt256OfByteArray (toBytesBE 4 sel.val).toList.toByteArray, 4)))
      {s with stack := referenceTail} = .ok
        ((Solidity.Evm.External.Memory.prepare {s with stack := referenceTail}).replaceStackAndIncrPC
          (EvmYul.UInt256.ofNat sel.val :: referenceTail) 5) := by
  constructor
  · exact Solidity.Backend.Environment.selector_correct sel tail
  · rw [metadata_reference_read ⟨4, by decide⟩ ⟨sel.val, sel.isLt⟩]
    rfl

/-- ABI bytes4 uses the actual published left-aligned value and PUSH32, rather
than silently reusing the low numeric selector representation. -/
theorem metadata_abi_reference (sel : Fin (2 ^ 32)) (s : EvmYul.EVM.State)
    (referenceTail : List EvmYul.UInt256) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (.PUSH32, some
      (EvmYul.uInt256OfByteArray (toBytesBE 32
        (Solidity.Backend.Environment.selectorAbiValue sel).val).toList.toByteArray, 32)))
      {s with stack := referenceTail} = .ok
        ((Solidity.Evm.External.Memory.prepare {s with stack := referenceTail}).replaceStackAndIncrPC
          (EvmYul.UInt256.ofNat (sel.val * 2 ^ 224) :: referenceTail) 33) := by
  rw [metadata_reference_read ⟨32, by decide⟩ (Solidity.Backend.Environment.selectorAbiValue sel)]
  rfl

/-- Existing external-function address/selector packing reaches the actual
reference PUSH24 unchanged; no new function-value representation is invented. -/
theorem metadata_function_reference (a : Solidity.Backend.Environment.Address)
    (sel : Fin (2 ^ 32)) (s : EvmYul.EVM.State)
    (referenceTail : List EvmYul.UInt256) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (.PUSH24, some
      (EvmYul.uInt256OfByteArray (toBytesBE 24
        (Solidity.Backend.Environment.packedFunction a sel).val).toList.toByteArray, 24)))
      {s with stack := referenceTail} = .ok
        ((Solidity.Evm.External.Memory.prepare {s with stack := referenceTail}).replaceStackAndIncrPC
          (EvmYul.UInt256.ofNat (a.1.1.toNat * 2 ^ 32 + sel.val) :: referenceTail) 25) := by
  rw [metadata_reference_read ⟨24, by decide⟩ (Solidity.Backend.Environment.packedFunction a sel)]
  rfl
end SolidityBridge.RoadmapV15
