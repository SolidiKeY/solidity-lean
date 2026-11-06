import Solidity.Yul.Views.ByteObjects
import Solidity.Yul.Views.Controls

/-! Inhabited read-side source-layout obligations, including actual struct nth. -/
namespace Solidity.Yul.Views.Controls

def byteObject : Source.Data layout (.bytes .memory) := .bytes [0xaa, 0xbb]

theorem byte_header : ObjectWord (fun a => 128 + a * 64) byteObject 0 2 :=
  .bytesLength [0xaa, 0xbb] (by decide)

theorem byte_payload : ObjectByte byteObject 33 0xbb :=
  .bytes [0xaa, 0xbb] ⟨1, by decide⟩

def unalignedBytes : ByteView := bytesObjectView [0xaa, 0xbb] (by decide) ascending 129

theorem byte_component : mload unalignedBytes 129 = 2 ∧ unalignedBytes 162 = 0xbb ∧
    unalignedBytes 163 = 163 ∧ unalignedBytes 128 = 128 := by
  refine ⟨bytesObject_header _ _ _ _, ?_⟩
  decide

theorem byte_component_decode : decodeBytesObject layout unalignedBytes 129 = byteObject :=
  decode_bytesObjectView layout _ _ _ _

/-- Shared zero-slot *object reads* work; pointer/heap alias integration is separate. -/
theorem zero_slot_empty : decodeBytesObject layout zero 96 = .bytes [] ∧
    decodeStringObject layout zero 96 = .string [] := by
  constructor <;> rfl

def fieldsLayout : Source.Layout := ⟨fun _ => [.bool], fun _ => 1, fun _ => .bool⟩
def structName : Source.DeclName := ⟨none, "One"⟩
def members : Source.DataList fieldsLayout [.bool] := .cons (.val (.bool true)) .nil

theorem struct_word : ObjectWord (D := fieldsLayout) (fun a => 128 + a * 64)
    (.struct (l := .memory) (d := structName) members) 0 1 :=
  .structMember members 0 (.bool true) 1 rfl (.scalar (.bool true) 1 rfl)

#print axioms byte_header
#print axioms byte_payload
#print axioms struct_word
#print axioms byte_component
#print axioms byte_component_decode
#print axioms zero_slot_empty

end Solidity.Yul.Views.Controls
