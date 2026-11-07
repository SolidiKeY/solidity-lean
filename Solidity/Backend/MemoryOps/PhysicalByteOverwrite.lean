import Solidity.Backend.MemoryOps.PhysicalByteStore

/-! Two actual byte stores and their reached REVERT payload. Destinations may
coincide; this is local slice execution, not Source rollback or a word update. -/
namespace Solidity.Backend.MemoryOps.Physical

theorem mstore8_pair_revert (bytes : Environment.Memory) (a v b w r n : Roadmap.Word)
    (tail : List Roadmap.Word) (suffix : Backend.Program) :
    let reached := Environment.writeByte (Environment.writeByte bytes a.val (UInt8.ofNat v.val))
      b.val (UInt8.ofNat w.val)
    Failure.Slice.run ([.op .MSTORE8,.op .MSTORE8,.op .REVERT] ++ suffix)
      ⟨a::v::b::w::r::n::tail,bytes⟩=
      some (⟨tail,reached⟩,some (.revert (Environment.readMemory reached r.val n.val))) := by
  first
  | rfl
  | simp only [readMemory_eq_getBytes]; rfl

/-- Arbitrary overlapping offsets update the entire observed payload twice. -/
theorem mstore8_pair_payload (bytes : Environment.Memory) (a n i j : Nat) (v w : UInt8) :
    Environment.readMemory
      (Environment.writeByte (Environment.writeByte bytes (a+i) v) (a+j) w) a n=
      ((Environment.readMemory bytes a n).set i v).set j w := by
  first
  | rfl
  | simp only [readMemory_writeByte_at]

/-- Only represented words disjoint from BOTH actual destinations are framed. -/
theorem WordFrame.mstore8_pair {m : Evm.Machine} {bytes : Environment.Memory} {live : Nat → Prop}
    (initial : WordFrame m bytes live) (a b : Nat) (v w : UInt8)
    (sepA : ∀ c,live c → a<32*c ∨ 32*c+32≤a)
    (sepB : ∀ c,live c → b<32*c ∨ 32*c+32≤b) :
    WordFrame m (Environment.writeByte (Environment.writeByte bytes a v) b w) live := by
  first
  | solve | rfl | simp only [] | omega
  | exact (initial.writeByte_outside a v sepA).writeByte_outside b w sepB

/-- The second instruction really fails with one operand; no suffix machine is returned. -/
theorem mstore8_pair_short (bytes : Environment.Memory) (a v b : Roadmap.Word) :
    Failure.Slice.step (.op .MSTORE8) ⟨[a,v,b],bytes⟩=
      some (⟨[b],Environment.writeByte bytes a.val (UInt8.ofNat v.val)⟩,none) ∧
    Failure.Slice.run [.op .MSTORE8,.op .MSTORE8] ⟨[a,v,b],bytes⟩=none := by
  first | rfl | exact ⟨rfl,rfl⟩

namespace ByteOverwriteControls
private def word (n : Nat) : Roadmap.Word := ⟨n % 2^256,Nat.mod_lt _ (by decide)⟩
private def bytes : Environment.Memory := fun _ => 9

/-- Nonzero offset, truncation, complete payload, saved stack, same-address overwrite. -/
theorem overwrite :
    Failure.Slice.run [.op .MSTORE8,.op .MSTORE8,.op .REVERT]
      ⟨[word 33,word 258,word 33,word 7,word 32,word 3,word 77],bytes⟩=
      some (⟨[word 77],Environment.writeByte (Environment.writeByte bytes 33 2) 33 7⟩,
        some (.revert [9,7,9])) := by
  first | rfl | decide

/-- Distinct destinations retain both writes and the untouched neighboring byte. -/
theorem distinct :
    Environment.readMemory (Environment.writeByte (Environment.writeByte bytes 33 2) 34 7) 32 4=
      [9,2,7,9] := by
  first | rfl | decide

theorem wrong_order :
    Environment.readMemory (Environment.writeByte (Environment.writeByte bytes 33 7) 33 2) 32 3 ≠
      [9,7,9] := by
  first | decide | simp only [Environment.readMemory,Environment.writeByte,bytes]; decide
end ByteOverwriteControls

/-- info: 'Solidity.Backend.MemoryOps.Physical.mstore8_pair_revert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mstore8_pair_revert
/-- info: 'Solidity.Backend.MemoryOps.Physical.mstore8_pair_payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mstore8_pair_payload
/-- info: 'Solidity.Backend.MemoryOps.Physical.WordFrame.mstore8_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WordFrame.mstore8_pair
/-- info: 'Solidity.Backend.MemoryOps.Physical.mstore8_pair_short' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms mstore8_pair_short
/-- info: 'Solidity.Backend.MemoryOps.Physical.ByteOverwriteControls.overwrite' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms ByteOverwriteControls.overwrite
/-- info: 'Solidity.Backend.MemoryOps.Physical.ByteOverwriteControls.distinct' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms ByteOverwriteControls.distinct
/-- info: 'Solidity.Backend.MemoryOps.Physical.ByteOverwriteControls.wrong_order' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms ByteOverwriteControls.wrong_order
end Solidity.Backend.MemoryOps.Physical
