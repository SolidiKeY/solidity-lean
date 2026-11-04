import Solidity.Backend.MemoryOps.PhysicalWorldUnwind
import Solidity.Backend.Environment.Composition

/-! P6 BYTE-WORLD dependency contract. Reuses the published WordFrame,
worldJournal and actual ABI-unwind producers. Only the numeric byte-load
program realization below is pending. No Producer instance is supplied.
loadCode is existing Backend syntax indexed ONLY by a word cell, never by
current memory, a desired value, a Source outcome or a future theorem.
An implementation must additionally bind its declaration/commit and emission
provenance; this contract alone is no Source compiler or world codec. -/
namespace Solidity.Backend.MemoryOps.Physical.ByteWorld

/-- Explicit pending producer interface over ACTUAL byte-target execution.
The complete 32-byte image and capacity are initial facts, not final oracles.
No code, interpreter or concrete inhabitant is defined by this structure. -/
structure Producer (loadCode : Nat → Backend.Program) : Prop where
  load : ∀ (frame : Environment.Frame) (bytes : Environment.Memory)
    (cell value : Fin Evm.W) (tail : List Environment.Word),
    32*cell.val+32≤2^256 → tail.length+1≤1024 →
    Environment.readMemory bytes (32*cell.val) 32=Semantics.wordBytes value.val →
    Environment.runSlice frame (loadCode cell.val) ⟨tail,bytes⟩=
      some ⟨lenU value.val value.isLt::tail,bytes⟩

/-- Conditional consumer of the EXPLICIT pending field. The value is obtained
from the initial published WordFrame; no final value or run is supplied. This
does not construct a Producer or discharge the byte-program dependency. -/
theorem Producer.load_at {code : Nat → Backend.Program} (producer : Producer code)
    (frame : Environment.Frame) (m : Evm.Machine) (bytes : Environment.Memory)
    (cells : Nat → Prop) (initial : WordFrame m bytes cells)
    (cell : Fin Evm.W) (selected : cells cell.val) (tail : List Environment.Word)
    (room : tail.length+1≤1024) :
    ∃ value : Fin Evm.W, m.mem cell.val=.val value ∧
      Evm.run [.mloadAt] (m.push (.val cell))=.ok (m.push (.val value)) 0 ∧
      Environment.runSlice frame (code cell.val) ⟨tail,bytes⟩=
        some ⟨lenU value.val value.isLt::tail,bytes⟩ ∧
      WordFrame (m.push (.val value)) bytes cells := by
  first
  | solve | rfl | simp only [] | omega
  | obtain ⟨value,word,image⟩ := initial.cells cell.val selected
    refine ⟨value,word,?_,producer.load frame bytes cell value tail (initial.fits _ selected) room image,
      initial.fits,initial.cells⟩
    change Evm.Out.ok (m.push (m.mem cell.val)) 0=_
    rw [word]

/-- Current literal MLOAD case is absent from the published combined slice.
This diagnostic is not an impossibility claim about every possible code, and
not evidence of an inhabitant of Producer. MSTORE/MSTORE8 already exist. -/
theorem current_mload_boundary (frame : Environment.Frame) (input : Environment.Slice) :
    Environment.sliceStep frame (.op .MLOAD) input=none := by
  first | rfl | simp only [Environment.sliceStep,Environment.cryptoStep]

/-- info: 'Solidity.Backend.MemoryOps.Physical.ByteWorld.Producer.load_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Producer.load_at
/-- info: 'Solidity.Backend.MemoryOps.Physical.ByteWorld.current_mload_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms current_mload_boundary
end Solidity.Backend.MemoryOps.Physical.ByteWorld
