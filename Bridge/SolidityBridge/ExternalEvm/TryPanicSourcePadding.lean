import SolidityBridge.ExternalEvm.PaddingInterface
import SolidityBridge.ExternalEvm.TryMemory

/-! H8 consumers of the published H7 logical padding supplier.
No native allocation, finite-entry attainment, source lowering or execution claim.
The actual ordered stores and conditional capacity are retained. -/
namespace Solidity.Evm.External.TryPanicSourcePadding
open EvmYul
open Memory

theorem word_encoding (v : UInt256) : v.toByteArray = encoding v :=
  serialize_eq 32 paddingCorrect32 (Nat.le_refl 32) v

theorem actual_word_write_read (m : ByteArray) (a : Nat) (v : UInt256)
    (capacity : a + 32 ≤ m.size) :
    (ByteArray.write v.toByteArray 0 m a 32).readWithPadding a 32 = v.toByteArray :=
  write_readback _ _ _ (padding_zero 32 paddingCorrect32) (serialize_h7 v).1 capacity

/-- The first store's capacity consequence is derived, not assumed for its result. -/
theorem overlap_read (m : MachineState) (x y : UInt256) (capacity : 36 ≤ m.memory.size) :
    ((m.mstore (.ofNat 0) x).mstore (.ofNat 4) y).memory.readWithPadding 4 32 =
      encoding y := by
  rw [TryMemory.overlap_memory]
  have size : (ByteArray.write x.toByteArray 0 m.memory 0 32).size = m.memory.size :=
    write_size _ _ _ (padding_zero 32 paddingCorrect32) (serialize_h7 x).1 (by omega)
  rw [actual_word_write_read _ 4 y (by rw [size]; exact capacity),word_encoding]

theorem overlap_decoded (m : MachineState) (x y : UInt256) (capacity : 36 ≤ m.memory.size) :
    fromByteArrayBigEndian
      (((m.mstore (.ofNat 0) x).mstore (.ofNat 4) y).memory.readWithPadding 4 32) = y.toNat := by
  rw [overlap_read m x y capacity]
  exact (encoding_spec y).2

/-- The second write preserves the actual first store's four selector bytes. -/
theorem overlap_selector_prefix (m : MachineState) (x y : UInt256)
    (capacity : 36 ≤ m.memory.size) (j : Nat) (small : j < 4) :
    ((m.mstore (.ofNat 0) x).mstore (.ofNat 4) y).memory.data[j]! =
      (encoding x).data[j]! := by
  rw [TryMemory.overlap_memory]
  have size : (ByteArray.write x.toByteArray 0 m.memory 0 32).size = m.memory.size :=
    write_size _ _ _ (padding_zero 32 paddingCorrect32) (serialize_h7 x).1 (by omega)
  rw [write_get_frame y.toByteArray _ 4 j (padding_zero 32 paddingCorrect32)
    (serialize_h7 y).1 (by rw [size]; exact capacity)
    (by rw [size]; omega) (Or.inl small)]
  have first : (ByteArray.write x.toByteArray 0 m.memory 0 32).data[0 + j]! =
      x.toByteArray.data[j]! :=
    write_get_same _ _ 0 j (padding_zero 32 paddingCorrect32)
      (serialize_h7 x).1 (by omega) (by omega)
  simpa only [Nat.zero_add,word_encoding] using first

/-- Each payload byte comes from the actual second word, including overlap. -/
theorem overlap_payload_byte (m : MachineState) (x y : UInt256)
    (capacity : 36 ≤ m.memory.size) (j : Nat) (small : j < 32) :
    ((m.mstore (.ofNat 0) x).mstore (.ofNat 4) y).memory.data[4 + j]! =
      (encoding y).data[j]! := by
  rw [TryMemory.overlap_memory]
  have size : (ByteArray.write x.toByteArray 0 m.memory 0 32).size = m.memory.size :=
    write_size _ _ _ (padding_zero 32 paddingCorrect32) (serialize_h7 x).1 (by omega)
  rw [write_get_same y.toByteArray _ 4 j (padding_zero 32 paddingCorrect32)
    (serialize_h7 y).1 (by rw [size]; exact capacity) small,word_encoding]

/-- A zero requested return length has a proved logical value under H7. This
still says nothing about actual source invocation, charge/fuel, or child outcome. -/
theorem zero_return (m : MachineState) (a : Nat) :
    m.memory.readWithPadding a 0 = ByteArray.empty := readWithPadding_zero _ _

end Solidity.Evm.External.TryPanicSourcePadding
