import SolidityBridge.AccessBridge.MemoryInterface

/-! Raw MLOAD payload contract over the existing P6 frame and pinned reader.
All native offsets are covered, including partial/exterior reads. No host bound
is imposed on reserved capacity, offsets or initial bytes. This does not assert
post active-extent representation, Source origin or full compiler adequacy.
Consumers pair it with MemoryAccessCertificate.load_charged for actual original
charges, errors and complete reached states. -/
namespace SolidityBridge.AccessBridge
open Solidity Solidity.Backend EvmYul
open Solidity.Evm.TryByteImage

structure MemoryLoadCertificate : Prop where
  payload : ∀ {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
      (native : EvmYul.MachineState) (offset : UInt256), FrameImage frame native →
    (native.mload offset).1.toNat = ofBytesBE
      (Environment.readMemory (MemoryOps.Physical.frameBytes frame) offset.toNat 32)
  unchanged_bytes : ∀ (native : EvmYul.MachineState) (offset : UInt256),
    (native.mload offset).2.memory = native.memory

end SolidityBridge.AccessBridge
