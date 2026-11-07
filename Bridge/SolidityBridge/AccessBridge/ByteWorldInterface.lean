import Solidity.Backend.MemoryOps.PhysicalByteWorldInterface
import SolidityBridge.AccessBridge.MemoryLoadInterface

/-! H26 consumer contract across the frozen P6 byte-world field and the pinned
MLOAD payload interface. Initial images and address scaling stay explicit.
No byte-world producer, compiler selection or post-active-image claim is made. -/
namespace SolidityBridge.AccessBridge
open Solidity Solidity.Backend EvmYul
open Solidity.Evm.TryByteImage

/-- Complete paired observations at one initially represented word cell.
The native result is compared through its complete ordered serialization,
not an assumed inverse between the two existing word encoders. -/
structure ByteWorldLoadCertificate (code : Nat → Backend.Program) : Prop where
  paired : MemoryOps.Physical.ByteWorld.Producer code →
    ∀ {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (native : EvmYul.MachineState) (_image : FrameImage frame native)
    (m : Evm.Machine) (cells : Nat → Prop),
    MemoryOps.Physical.WordFrame m (MemoryOps.Physical.frameBytes frame) cells →
    ∀ (runtime : Environment.Frame) (cell : Fin Evm.W) (offset : UInt256)
    (_scaled : offset.toNat=32*cell.val) (_selected : cells cell.val)
    (tail : List Environment.Word), tail.length+1≤1024 →
    ∃ value : Fin Evm.W,
      m.mem cell.val=.val value ∧
      Evm.run [.mloadAt] (m.push (.val cell))=.ok (m.push (.val value)) 0 ∧
      Environment.runSlice runtime (code cell.val)
        ⟨tail,MemoryOps.Physical.frameBytes frame⟩=
        some ⟨lenU value.val value.isLt::tail,MemoryOps.Physical.frameBytes frame⟩ ∧
      (native.mload offset).1.toNat=ofBytesBE (Semantics.wordBytes value.val) ∧
      (toBytesBE 32 (native.mload offset).1.toNat).toList=Semantics.wordBytes value.val ∧
      (native.mload offset).2.memory=native.memory ∧
      MemoryOps.Physical.WordFrame (m.push (.val value))
        (MemoryOps.Physical.frameBytes frame) cells

end SolidityBridge.AccessBridge
