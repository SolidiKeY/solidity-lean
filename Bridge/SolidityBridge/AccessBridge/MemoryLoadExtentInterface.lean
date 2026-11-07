import SolidityBridge.AccessBridge.MemoryLoadInterface

/-! Additive MLOAD extent observations. The original all-offset payload and
charged contracts are unchanged. The exact post-image boundary is an iff,
not a narrowed input-admission predicate. -/
namespace SolidityBridge.AccessBridge
open Solidity Solidity.Backend EvmYul
open Solidity.Evm.TryByteImage

structure MemoryLoadExtentCertificate : Prop where
  active : ∀ (native : EvmYul.MachineState) (offset : UInt256),
    (native.mload offset).2.activeWords.toNat =
      max native.activeWords.toNat ((offset.toNat+63)/32)
  post_image : ∀ {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (native : EvmYul.MachineState) (span : ByteSpan frame.capacity) (offset : UInt256),
    offset.toNat=span.offset.val.toNat →
    span.length.val.toNat=32 → FrameImage frame native →
    (FrameImage (Yul.Adapters.P6ByteMemory.touch frame span)
      (native.mload offset).2 ↔
    32*(Yul.Adapters.P6ByteMemory.touch frame span).highWaterWords<UInt256.size)

end SolidityBridge.AccessBridge
