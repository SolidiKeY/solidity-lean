import SolidityBridge.AccessBridge.ByteWorldInterface

/-! Additive numeric consequence of the existing paired observation contract.
No producer, source-origin or post-active premise is changed or discharged. -/
namespace SolidityBridge.AccessBridge
open Solidity Solidity.Backend EvmYul
open Solidity.Evm.TryByteImage

structure ByteWorldNumericCertificate (code : Nat → Backend.Program) : Prop
    extends ByteWorldLoadCertificate code where
  numeric : MemoryOps.Physical.ByteWorld.Producer code →
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
      (native.mload offset).1.toNat=value.val ∧
      (native.mload offset).2.memory=native.memory ∧
      MemoryOps.Physical.WordFrame (m.push (.val value))
        (MemoryOps.Physical.frameBytes frame) cells

end SolidityBridge.AccessBridge
