import SolidityBridge.AccessBridge.ByteWorldNumericInterface
import SolidityBridge.AccessBridge.ByteWorldLoad

namespace SolidityBridge.AccessBridge.ByteWorldNumeric
open Solidity Solidity.Backend EvmYul
open Solidity.Evm.TryByteImage

private theorem digits_map (k n : Nat) :
    Failure.digits k n = (List.range k).map
      (fun i => UInt8.ofNat (n / 256 ^ (k - 1 - i) % 256)) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [Failure.digits, ih, List.range_succ, List.map_append, List.map_singleton]
    apply congrArg₂ List.append
    · apply List.map_congr_left
      intro i hi
      have small : i < k := List.mem_range.mp hi
      have exponent : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [exponent, Nat.div_div_eq_div_mul, Nat.pow_succ']
    · have exponent : k + 1 - 1 - k = 0 := by omega
      simp only [exponent, Nat.pow_zero, Nat.div_one]

theorem word_bytes_digits (n : Nat) :
    Semantics.wordBytes n = Failure.digits 32 n := by
  exact (digits_map 32 n).symm

theorem read_word_bytes (word : Fin Evm.W) :
    ofBytesBE (Semantics.wordBytes word.val) = word.val := by
  change Failure.readImmediate (Semantics.wordBytes word.val) = word.val
  rw [word_bytes_digits]
  apply Failure.read_digits
  have width : (256 : Nat)^32 = Evm.W := by decide
  rw [width]
  exact word.isLt

theorem paired_numeric {code : Nat → Backend.Program}
    (producer : MemoryOps.Physical.ByteWorld.Producer code)
    {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (native : EvmYul.MachineState) (image : FrameImage frame native)
    (m : Evm.Machine) (cells : Nat → Prop)
    (initial : MemoryOps.Physical.WordFrame m (MemoryOps.Physical.frameBytes frame) cells)
    (runtime : Environment.Frame) (cell : Fin Evm.W) (offset : UInt256)
    (scaled : offset.toNat=32*cell.val) (selected : cells cell.val)
    (tail : List Environment.Word) (room : tail.length+1≤1024) :
    ∃ value : Fin Evm.W,
      m.mem cell.val=.val value ∧
      Evm.run [.mloadAt] (m.push (.val cell))=.ok (m.push (.val value)) 0 ∧
      Environment.runSlice runtime (code cell.val)
        ⟨tail,MemoryOps.Physical.frameBytes frame⟩=
        some ⟨lenU value.val value.isLt::tail,MemoryOps.Physical.frameBytes frame⟩ ∧
      (native.mload offset).1.toNat=value.val ∧
      (native.mload offset).2.memory=native.memory ∧
      MemoryOps.Physical.WordFrame (m.push (.val value))
        (MemoryOps.Physical.frameBytes frame) cells := by
  obtain ⟨value,word,intrinsic,byteRun,read,_serialized,memory,post⟩ :=
    ByteWorldLoad.paired_load producer frame native image m cells initial runtime
      cell offset scaled selected tail room
  rw [read_word_bytes] at read
  exact ⟨value,word,intrinsic,byteRun,read,memory,post⟩

def certificate (code : Nat → Backend.Program) : ByteWorldNumericCertificate code where
  toByteWorldLoadCertificate := ByteWorldLoad.certificate code
  numeric := paired_numeric

/-- info: 'SolidityBridge.AccessBridge.ByteWorldNumeric.read_word_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_word_bytes
/-- info: 'SolidityBridge.AccessBridge.ByteWorldNumeric.paired_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms paired_numeric
/-- info: 'SolidityBridge.AccessBridge.ByteWorldNumeric.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate

end SolidityBridge.AccessBridge.ByteWorldNumeric
