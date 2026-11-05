import Solidity.Yul.Compilation.PhysicalStore
import Solidity.Backend.Environment.Composition
/-! Constant physical-view hashing with the ACTUAL canonical withKeccak field.
The target's existing byte-data/hash slice computes real Keccak; this adapter
neither fixes other source Fixed instances nor proves native/G24/world closure.
No collision/injectivity assumption, new hash/state/layout or source AST. -/
namespace Solidity.Yul.Compilation.PhysicalHash
open Solidity.Yul.Views

/-- Existing bounded target word constructor, not another source word meaning. -/
def targetWord (value : Roadmap.Word) : Backend.Environment.Word := lenU value.val value.isLt

def hashCode (address length : Roadmap.Word) : Backend.Program :=
  Backend.Environment.keccakCode address length

def selectHash (address length : Roadmap.Word) : Option Backend.Program :=
  if length.val = 0 ∨ address.val+length.val≤2^256 then some (hashCode address length) else none

def storeThenHash (address : Roadmap.Word) (value : Roadmap.Word) : Backend.Program :=
  PhysicalStore.wordCode address.val value ++ hashCode address 32

/-- Exact representation of the actual canonical source hash in the existing
target word. No extra hash premise or collision assumption. -/
theorem digest_view (m : ByteView) (address length : Nat) :
    Backend.Environment.digest (Backend.Environment.readMemory m address length) =
      targetWord (keccak256 Roadmap.Evm.withKeccak m address length) := by
  apply Subtype.ext
  change ((Keccak.keccak256Nat ((readBytes m address length).map UInt8.toNat) : Nat) : Int) =
    ((Keccak.keccak256Nat ((readBytes m address length).map UInt8.toNat) % 2^256 : Nat) : Int)
  rw [Nat.mod_eq_of_lt (Backend.Environment.keccak_bound (readBytes m address length))]

/-- Full byte-materialization/hash execution for arbitrary memory and caller
stack. The no-wrap address premise is independent of native gas/capacity. -/
theorem store_hash_run (f : Backend.Environment.Frame) (address value : Roadmap.Word)
    (s : Backend.Environment.Slice) (fits : address.val+32≤2^256) :
    Backend.Environment.runSlice f (storeThenHash address value) s =
      some {s with
        memory := mstore s.memory address.val value
        stack := targetWord (keccak256 Roadmap.Evm.withKeccak
          (mstore s.memory address.val value) address.val 32) :: s.stack} := by
  have stored : Backend.Environment.runSlice f (PhysicalStore.wordCode address.val value) s =
      some {s with memory := mstore s.memory address.val value} := by
    rw [PhysicalStore.wordCode, Backend.Environment.runSlice_data f _ _
      (Backend.Environment.materialize_supported address.val (PhysicalStore.bytesOf value))]
    have actual := Backend.Environment.materialize_correct (PhysicalStore.bytesOf value)
      address.val s (by simpa only [PhysicalStore.bytesOf,List.length_ofFn] using fits)
    simpa only [PhysicalStore.wordCode,PhysicalStore.word_memory] using actual
  rw [storeThenHash, Backend.Environment.runSlice_append, stored, Option.bind_some]
  rw [hashCode, Backend.Environment.runSlice_crypto f _ _
    (Backend.Environment.keccak_supported address 32), Backend.Environment.keccak_correct]
  rw [digest_view]
  rfl

#print axioms store_hash_run
#print axioms digest_view
end Solidity.Yul.Compilation.PhysicalHash
