import Solidity.Yul.Compilation.PhysicalStore
import Solidity.Yul.Views.MixedHeapControls
/-! Concrete constant-store/view/image controls. Existing producer heap and
placement are inputs, not a duplicate layout. No native gas/1024/MemOK claim. -/
namespace Solidity.Yul.Compilation.PhysicalStore.Controls
open Solidity.Yul.Views
open Solidity.Yul.Views.Controls (mixedHeap mixedPlacement mixedChild mixedResidual)

def dirty : Roadmap.Word := ⟨2^200+257,by decide⟩
def payload : Roadmap.Word := ⟨0xab*2^248+2^200+257,by decide⟩
def memory : ByteView := fun n => UInt8.ofNat (n+9)
def initial : Backend.Environment.Slice := ⟨[uintOfNat 77,uintOfNat 99],memory⟩
def observe (code : Backend.Program) (s : Backend.Environment.Slice) (points : List Nat) :=
  (Backend.Environment.runData code s).map (fun out => (out.stack.map (fun w => w.1.toNat),points.map out.memory))
#check byte_run
#check word_memory
#guard observe (byteCode 31 dirty) initial [30,31,32] = some ([77,99],[39,1,41])
#guard observe (byteCode 32 0x1ff) initial [31,32,33] = some ([77,99],[40,255,42])
#guard (Backend.Environment.runData (wordCode 31 payload) initial).map
  (fun out => (mload out.memory 31).val) = some payload.val
#guard observe (wordCode 31 payload) initial [30,31,62,63] = some ([77,99],[39,0xab,1,72])
#guard (Backend.Environment.runData (wordCode 31 payload ++ byteCode 32 0x1fe) initial).map
  (fun out => (out.stack.map (fun w => w.1.toNat),out.memory 31,out.memory 32,out.memory 62)) =
  some ([77,99],0xab,0xfe,1)
#guard (wordCode 31 payload).length = 96
#guard (selectWord (2^256-32) payload).isSome
#guard (selectWord (2^256-31) payload).isNone
#guard (selectWord (2^256) payload).isNone
#guard @decide (ValidRange (2^256-32) 32) (by unfold ValidRange; infer_instance)
#guard !(@decide (ValidRange (2^256-31) 32) (by unfold ValidRange; infer_instance))
#guard observe (byteCode ⟨2^256-1,by decide⟩ 0x1ab) initial [2^256-2,2^256-1] =
  some ([77,99],[7,0xab])
#guard (Backend.Environment.runData [.op .MSTORE8] (⟨[],memory⟩ : Backend.Environment.Slice)).isNone
#guard (Backend.Environment.runData [.op .MSTORE8] (⟨[uintOfNat 31],memory⟩ : Backend.Environment.Slice)).isNone
#guard (Backend.Environment.runData [.op .MSTORE] initial).isNone
-- Success in this byte slice does not enforce the actual EVM stack bound.
def oversized : Backend.Environment.Slice := ⟨List.replicate 1025 (uintOfNat 1),memory⟩
#guard (Backend.Environment.runData (byteCode 31 dirty) oversized).map (fun out => out.stack.length) = some 1025

def image : MemoryImage mixedPlacement (.bytes (l := .memory) mixedChild) := .bytes mixedChild (by decide)
def imageInput : Backend.Environment.Slice := ⟨initial.stack,image.encode mixedResidual (mixedPlacement.address 0)⟩
#guard (mixedHeap.get 0).isSome
#guard (mixedPlacement.address 0) = 128
#guard image.span = 35
#check image_frame image mixedResidual (mixedPlacement.address 0) 31 dirty (Or.inl (by decide))
#check byte_run 31 dirty imageInput
#guard (Backend.Environment.runData (byteCode 31 dirty) imageInput).map
  (fun out => readBytes out.memory 160 3) = some mixedChild
#guard (Backend.Environment.runData (byteCode 31 dirty) imageInput).map
  (fun out => (mload out.memory 128).val) = some 3
#guard (Backend.Environment.runData (byteCode 31 dirty) imageInput).map
  (fun out => (mload out.memory 64).val) = some 1664
#guard (Backend.Environment.runData (byteCode 31 dirty) imageInput).map
  (fun out => readBytes out.memory 96 32) = some (List.replicate 32 0)
-- An inside-header mutation invalidates the old logical image's length read;
-- the outside-frame premise cannot simply be dropped.
#guard (Backend.Environment.runData (byteCode 159 1) imageInput).map
  (fun out => (mload out.memory 128).val) = some 1
#print axioms byte_run
#print axioms word_memory
#print axioms image_frame
end Solidity.Yul.Compilation.PhysicalStore.Controls
