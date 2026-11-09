import Solidity.Backend.MemoryOps.PhysicalByteWorldInterface
import Solidity.Backend.Environment.LoadV2
/-! R3 versioned point-load contract. Guards against weakening the
address, capacity or initial full32-byte image premises when versioning the
runtime endpoint. Frozen v1 is unchanged; no production adequacy is inferred. -/
namespace Solidity.Backend.MemoryOps.Physical.ByteWorldV2

structure Producer (loadCode : Nat → Backend.Program) : Prop where
  load : ∀ (frame : Environment.Frame) (bytes : Environment.Memory)
    (cell value : Fin Evm.W) (tail : List Environment.Word),
    32*cell.val+32≤2^256 → tail.length+1≤1024 →
    Environment.readMemory bytes (32*cell.val) 32=Semantics.wordBytes value.val →
    Environment.LoadV2.run frame (loadCode cell.val) ⟨tail,bytes⟩=
      some ⟨lenU value.val value.isLt::tail,bytes⟩

/-- Conditional point-load transport over the same reached WordFrame.
No desired final value or successful target run is assumed. -/
theorem Producer.load_at {code : Nat → Backend.Program} (producer : Producer code)
    (frame : Environment.Frame) (m : Evm.Machine) (bytes : Environment.Memory)
    (cells : Nat → Prop) (initial : WordFrame m bytes cells)
    (cell : Fin Evm.W) (selected : cells cell.val) (tail : List Environment.Word)
    (room : tail.length+1≤1024) :
    ∃ value : Fin Evm.W, m.mem cell.val=.val value ∧
      Evm.run [.mloadAt] (m.push (.val cell))=.ok (m.push (.val value)) 0 ∧
      Environment.LoadV2.run frame (code cell.val) ⟨tail,bytes⟩=
        some ⟨lenU value.val value.isLt::tail,bytes⟩ ∧
      WordFrame (m.push (.val value)) bytes cells := by
  obtain ⟨value,word,image⟩ := initial.cells cell.val selected
  refine ⟨value,word,?_,producer.load frame bytes cell value tail (initial.fits _ selected) room image,
    initial.fits,initial.cells⟩
  change Evm.Out.ok (m.push (m.mem cell.val)) 0=_
  rw [word]

/-- info: 'Solidity.Backend.MemoryOps.Physical.ByteWorldV2.Producer.load_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Producer.load_at
end Solidity.Backend.MemoryOps.Physical.ByteWorldV2
