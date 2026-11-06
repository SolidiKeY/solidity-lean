import SolidityBridge.ExternalEvm.PaddingInterface
import SolidityBridge.ExternalEvm.BoundedScannerPrefix

/-! Kernel controls requiring the explicitly declared H7 vendor dependency.
A PUSH payload is not a jump destination; native allocator/scanner compatibility
and source execution are not supplied by these checks. They use the H7
logical bodies in the vendored EvmYul/FFI/ffi.lean and EvmYul/EVM/Semantics.lean
(see vendor/EvmYul/VENDOR.md). -/
namespace Solidity.Evm.External.H7Checks
open EvmYul EvmYul.EVM

def code : ByteArray := ⟨#[0x60,0x5b,0x5b]⟩

theorem actual_table : D_J code (.ofNat 0) = #[.ofNat 2] := by
  have bounded : code.size + 33 < UInt256.size := by decide
  rw [D_J,D_J_aux_bounded code (.ofNat 0) #[] bounded]
  rw [Assembly.word_nat 0 (by decide)]
  unfold code
  rw [Solidity.Evm.External.Assembly.scanner_byte_step (⟨#[0x60,0x5b,0x5b]⟩ : ByteArray) 0 (0x60 : UInt8) 1 false #[] rfl rfl rfl]; simp only [Bool.false_eq_true, if_false]; rw [Solidity.Evm.External.Assembly.scanner_byte_step (⟨#[0x60,0x5b,0x5b]⟩ : ByteArray) 2 (0x5b : UInt8) 0 true #[] rfl rfl rfl]; simp only []; rw [EvmYul.EVM.D_J_scan]; rfl

theorem payload_rejected :
    (D_J code (.ofNat 0)).contains (.ofNat 1) = false ∧
      (D_J code (.ofNat 0)).contains (.ofNat 2) = true := by
  rw [actual_table]
  decide

theorem zero_length_reader (source : ByteArray) (addr : Nat) :
    source.readWithPadding addr 0 = .empty :=
  Memory.readWithPadding_zero source addr

theorem serialized_word (word : UInt256) :
    word.toByteArray.size = 32 ∧ fromByteArrayBigEndian word.toByteArray = word.toNat :=
  Memory.serialize_h7 word
end Solidity.Evm.External.H7Checks
