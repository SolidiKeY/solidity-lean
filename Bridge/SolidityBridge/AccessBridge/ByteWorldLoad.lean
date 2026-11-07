import SolidityBridge.AccessBridge.ByteWorldInterface
import SolidityBridge.AccessBridge.MemoryLoad

/-! Consumer proof against the exact on-master P6 pending load field. The
intrinsic word, byte target and pinned read observe the same initial image.
No concrete Producer or Source/native origin is inferred from this transport. -/
namespace SolidityBridge.AccessBridge.ByteWorldLoad
open Solidity Solidity.Backend EvmYul
open Solidity.Evm.TryByteImage

/-- The word is obtained from the initial WordFrame, not supplied as a desired
result. Both stacks retain their tails; the complete native serialization and
physical bytes are preserved. Native post-active-word adequacy stays separate. -/
theorem paired_load {code : Nat → Backend.Program}
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
      (native.mload offset).1.toNat=ofBytesBE (Semantics.wordBytes value.val) ∧
      (toBytesBE 32 (native.mload offset).1.toNat).toList=Semantics.wordBytes value.val ∧
      (native.mload offset).2.memory=native.memory ∧
      MemoryOps.Physical.WordFrame (m.push (.val value))
        (MemoryOps.Physical.frameBytes frame) cells := by
  obtain ⟨value,word,intrinsic,byteRun,post⟩ := producer.load_at runtime m
    (MemoryOps.Physical.frameBytes frame) cells initial cell selected tail room
  have bytes : Environment.readMemory (MemoryOps.Physical.frameBytes frame) (32*cell.val) 32=
      Semantics.wordBytes value.val := by
    obtain ⟨other,otherWord,otherBytes⟩ := initial.cells cell.val selected
    have same : other=value := Evm.Word.val.inj (otherWord.symm.trans word)
    rw [same] at otherBytes
    exact otherBytes
  have read : (native.mload offset).1.toNat=ofBytesBE (Semantics.wordBytes value.val) := by
    have actual := MemoryLoad.payload frame native offset image
    rw [scaled,bytes] at actual
    exact actual
  have serialized : (toBytesBE 32 (native.mload offset).1.toNat).toList=
      Semantics.wordBytes value.val := by
    have exactBytes := RoadmapV15.bytes_encoding_roundtrip (Semantics.wordBytes value.val)
    rw [Environment.wordBytes_length,←read] at exactBytes
    exact exactBytes
  exact ⟨value,word,intrinsic,byteRun,read,serialized,
    MemoryLoad.unchanged_bytes native offset,post⟩

def certificate (code : Nat → Backend.Program) : ByteWorldLoadCertificate code where
  paired := paired_load

/-- info: 'SolidityBridge.AccessBridge.ByteWorldLoad.paired_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms paired_load
/-- info: 'SolidityBridge.AccessBridge.ByteWorldLoad.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end SolidityBridge.AccessBridge.ByteWorldLoad
