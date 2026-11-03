import Solidity.Evm.Memory
import Solidity.Backend.Environment.Crypto

/-!
# P6 numeric word cells and physical byte spans

This relation connects the EXISTING word-addressed machine to the EXISTING
byte-addressed backend slice. A represented numeric cell c occupies bytes
[32*c,32*c+32), with an explicit no-wrap bound. Symbolic Slot words have no
implicit physical encoding. Nothing changes an instruction or source profile.
The scaling is an explicit refinement boundary, not identity of emitted code.
Gas, active-memory expansion, external EVM and general pointer layout remain open.
-/
namespace Solidity.Backend.MemoryOps.Physical

/-- One actual numeric word cell, with its complete physical byte image. -/
def CellAt (m : Evm.Machine) (bytes : Environment.Memory) (cell : Nat) : Prop :=
  ∃ w : Fin Evm.W, m.mem cell=Evm.Word.val w ∧
    Environment.readMemory bytes (32*cell) 32=Semantics.wordBytes w.val

/-- A local footprint, without global address injectivity or zero assumptions
for unrepresented cells. The bounds concern physical bytes, not word indices. -/
structure WordFrame (m : Evm.Machine) (bytes : Environment.Memory) (live : Nat → Prop) : Prop where
  fits : ∀ cell, live cell → 32*cell+32≤2^256
  cells : ∀ cell, live cell → CellAt m bytes cell

theorem word_bytes_length (w : Nat) : (Semantics.wordBytes w).length=32 := by
  simp only [Semantics.wordBytes,List.length_map,List.length_range]

/-- Byte reads respect pointwise equality on exactly their selected interval. -/
theorem readMemory_congr (a n : Nat) (bytes other : Environment.Memory)
    (h : ∀ j, j<n → bytes (a+j)=other (a+j)) :
    Environment.readMemory bytes a n=Environment.readMemory other a n := by
  apply List.map_congr_left
  intro j hj
  exact h j (List.mem_range.mp hj)

/-- Complete frame for a read interval disjoint from an actual write. -/
theorem readMemory_write_frame (bytes : Environment.Memory) (a n d : Nat) (bs : List UInt8)
    (sep : a+n≤d ∨ d+bs.length≤a) :
    Environment.readMemory (Environment.writeBytes bytes d bs) a n=Environment.readMemory bytes a n := by
  apply readMemory_congr
  intro j hj
  apply Environment.writeBytes_frame
  omega

/-- A full numeric word store reconstructs the overwritten cell relation. -/
theorem cell_write_same (m : Evm.Machine) (bytes : Environment.Memory) (cell : Nat) (w : Fin Evm.W) :
    CellAt (Evm.Memory.writeMachine m cell (.val w))
      (Environment.writeBytes bytes (32*cell) (Semantics.wordBytes w.val)) cell := by
  refine ⟨w,Evm.upd_same _ _ _,?_⟩
  simpa only [word_bytes_length] using Environment.read_written (Semantics.wordBytes w.val) (32*cell) bytes

/-- Distinct word cells have disjoint physical spans; shared logical object
references do not enter this arithmetic argument. -/
theorem cell_write_other (m : Evm.Machine) (bytes : Environment.Memory) (cell dst : Nat)
    (w : Fin Evm.W) (hne : cell≠dst) (h : CellAt m bytes cell) :
    CellAt (Evm.Memory.writeMachine m dst (.val w))
      (Environment.writeBytes bytes (32*dst) (Semantics.wordBytes w.val)) cell := by
  obtain ⟨v,hv,hb⟩ := h
  refine ⟨v,?_,?_⟩
  · exact (Evm.upd_other _ _ hne).trans hv
  · rw [readMemory_write_frame]
    · exact hb
    · rw [word_bytes_length]
      omega

/-- Update the live footprint from INITIAL representation and actual writes.
The output relation and unchanged-byte facts are conclusions. -/
theorem WordFrame.write {m : Evm.Machine} {bytes : Environment.Memory} {live : Nat → Prop}
    (h : WordFrame m bytes live) (dst : Nat) (w : Fin Evm.W)
    (fits : 32*dst+32≤2^256) :
    WordFrame (Evm.Memory.writeMachine m dst (.val w))
      (Environment.writeBytes bytes (32*dst) (Semantics.wordBytes w.val))
      (fun cell => live cell ∨ cell=dst) := by
  constructor
  · intro cell hc
    rcases hc with hc | rfl
    · exact h.fits cell hc
    · exact fits
  · intro cell hc
    by_cases he : cell=dst
    · subst cell
      exact cell_write_same m bytes dst w
    · rcases hc with hc | hc
      · exact cell_write_other m bytes cell dst w he (h.cells cell hc)
      · exact (he hc).elim

/-- Actual abstract-word MSTORE, preserving its caller stack tail and every
other machine field. This is not a physical-byte instruction identity. -/
theorem word_mstore (m : Evm.Machine) (cell w : Fin Evm.W) :
    Evm.run [.mstoreAt] ((m.push (.val w)).push (.val cell))=
      .ok (Evm.Memory.writeMachine m cell.val (.val w)) 0 := by
  rfl

/-- Actual published byte-slice MSTORE at the scaled physical offset. The
entire stack tail is retained; serialization is the existing wordBytes. -/
theorem byte_mstore (bytes : Environment.Memory) (tail : List Environment.Word) (cell w : Fin Evm.W)
    (fits : 32*cell.val+32≤2^256) :
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU (32*cell.val) (by change 32*cell.val<2^256;omega) ::
        lenU w.val w.isLt :: tail,bytes⟩=
      some ⟨tail,Environment.writeBytes bytes (32*cell.val) (Semantics.wordBytes w.val)⟩ := by
  simp only [Environment.cryptoStep,lenU,Int.toNat_natCast]

/-- Both real stores execute, and their reached outputs are related. -/
theorem WordFrame.mstore {m : Evm.Machine} {bytes : Environment.Memory} {live : Nat → Prop}
    (h : WordFrame m bytes live) (cell w : Fin Evm.W) (tail : List Environment.Word)
    (fits : 32*cell.val+32≤2^256) :
    Evm.run [.mstoreAt] ((m.push (.val w)).push (.val cell))=
      .ok (Evm.Memory.writeMachine m cell.val (.val w)) 0 ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU (32*cell.val) (by change 32*cell.val<2^256;omega) ::
        lenU w.val w.isLt :: tail,bytes⟩=
      some ⟨tail,Environment.writeBytes bytes (32*cell.val) (Semantics.wordBytes w.val)⟩ ∧
    WordFrame (Evm.Memory.writeMachine m cell.val (.val w))
      (Environment.writeBytes bytes (32*cell.val) (Semantics.wordBytes w.val))
      (fun c => live c ∨ c=cell.val) :=
  ⟨word_mstore m cell w,byte_mstore bytes tail cell w fits,h.write cell.val w fits⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.word_bytes_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms word_bytes_length
/-- info: 'Solidity.Backend.MemoryOps.Physical.readMemory_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readMemory_congr
/-- info: 'Solidity.Backend.MemoryOps.Physical.readMemory_write_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readMemory_write_frame
/-- info: 'Solidity.Backend.MemoryOps.Physical.cell_write_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cell_write_same
/-- info: 'Solidity.Backend.MemoryOps.Physical.cell_write_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cell_write_other
/-- info: 'Solidity.Backend.MemoryOps.Physical.WordFrame.write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WordFrame.write
/-- info: 'Solidity.Backend.MemoryOps.Physical.word_mstore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_mstore
/-- info: 'Solidity.Backend.MemoryOps.Physical.byte_mstore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byte_mstore
/-- info: 'Solidity.Backend.MemoryOps.Physical.WordFrame.mstore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WordFrame.mstore
end Solidity.Backend.MemoryOps.Physical
