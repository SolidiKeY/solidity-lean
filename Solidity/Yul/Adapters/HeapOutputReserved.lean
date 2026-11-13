import Solidity.Yul.Adapters.HeapCallOutput

/-! Reserved-word preservation for actual call-output writes. Heap object
separation does not protect the free pointer or shared zero word. This law
requires the actual returned prefix to miss those bytes; it neither cleans
memory nor infers source admission, gas or allocation provenance. -/
namespace Solidity.Yul.Adapters.HeapOutputReserved
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views
variable {C : Contract} {Γ : Ctx}

/-- The scratch region is unrestricted. Only bytes [64,128) are protected. -/
theorem preserve (initial : FrameMem C Γ) (input output : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes) (free : Solidity.Roadmap.Word)
    (reserved : ReservedOK (frameBytes initial) free)
    (away : ∀ i : Fin 64,64+i.val<output.offset.val.toNat ∨
      output.offset.val.toNat+min output.length.val.toNat data.length≤64+i.val) :
    ReservedOK (frameBytes (RawPhysicalCallAccess.reached initial input output data)) free := by
  rw [RawPhysicalCallAccess.image]
  constructor
  · have words := mload_congr (frameBytes (RawPhysicalCallOutput.copy initial output data))
      (frameBytes initial) 64 (fun i => RawPhysicalCallOutput.outside initial output data (64+i.val)
        (away ⟨i.val,by have bound:=i.isLt;omega⟩))
    exact (congrArg Fin.val words).trans reserved.1
  · intro i
    rw [RawPhysicalCallOutput.outside initial output data (96+i.val)]
    · exact reserved.2 i
    · have bound:=i.isLt
      have separation :=  away ⟨32+i.val,by omega⟩
      change 64+(32+i.val)<output.offset.val.toNat ∨
        output.offset.val.toNat+min output.length.val.toNat data.length≤64+(32+i.val) at separation
      omega

/-- Useful interval condition includes an empty return at any offset. This
concerns bytes actually written, independently of requested access extent. -/
theorem preserve_interval (initial : FrameMem C Γ) (input output : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes) (free : Solidity.Roadmap.Word)
    (reserved : ReservedOK (frameBytes initial) free)
    (safe : min output.length.val.toNat data.length=0 ∨
      output.offset.val.toNat+min output.length.val.toNat data.length≤64 ∨ 128≤output.offset.val.toNat) :
    ReservedOK (frameBytes (RawPhysicalCallAccess.reached initial input output data)) free := by
  apply preserve initial input output data free reserved
  intro i
  have bound:=i.isLt
  rcases safe with empty | before | after
  · omega
  · omega
  · omega
end Solidity.Yul.Adapters.HeapOutputReserved
