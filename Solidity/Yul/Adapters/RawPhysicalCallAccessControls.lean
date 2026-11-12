import Solidity.Yul.Adapters.RawPhysicalCallAccess
import Solidity.Yul.Adapters.RawPhysicalCallFrameControls

/-! An input-dependent synthetic answer overlaps the caller input/output.
The callee receives old bytes, not the later output. Independent empty-output
controls require input access to grow the frame beyond output-only accounting.
These are kernel controls, not a concrete invocation adequacy certificate. -/
namespace Solidity.Yul.Adapters.RawPhysicalCallAccess.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory RawPhysicalInventory.Controls
open Source.StateExamples

def input (pipeline : Pipeline) : ByteSpan (stored pipeline).capacity :=
  ⟨lenU 161 (by decide),lenU 2 (by decide),Or.inr (by change 161+2≤192;decide)⟩
def output (pipeline : Pipeline) : ByteSpan (stored pipeline).capacity :=
  ⟨lenU 161 (by decide),lenU 3 (by decide),Or.inr (by change 161+3≤192;decide)⟩
def entry := RawPhysicalCallFrame.Controls.entry
def parent := RawPhysicalCallFrame.Controls.parent
/-- Labelled synthetic producer whose answer depends on the actual input. -/
def invoke : World.WorldPort D₀ LW LW := fun _ _ _ _ _ bytes =>
  some ⟨World.Checks.havoc,[.log World.Checks.l4],.success (17::bytes)⟩
def answer (pipeline : Pipeline) : World.FrameAnswer D₀ LW LW :=
  ⟨World.Checks.havoc,[.log World.Checks.l4],.success (17::snapshot (stored pipeline) (input pipeline))⟩
def after (pipeline : Pipeline) := reached (stored pipeline) (input pipeline) (output pipeline)
  (17::snapshot (stored pipeline) (input pipeline))

theorem actual_run (pipeline : Pipeline) :
    World.callAdapter World.TargetMemory.port invoke entry (frameBytes (stored pipeline)) parent .call
      (addr 3) (Source.toWord 100) (Source.toWord 0)
      (P6ByteMemory.wireWord (input pipeline).offset) (P6ByteMemory.wireWord (input pipeline).length)
      (P6ByteMemory.wireWord (output pipeline).offset) (P6ByteMemory.wireWord (output pipeline).length)=
      some {RawPhysicalCallFrame.completed (stored pipeline) (output pipeline) entry
        (World.childContext entry.effects.execution parent .call (addr 3) (Source.toWord 0)
          (snapshot (stored pipeline) (input pipeline))) (answer pipeline) with
        copiedMemory:=some (frameBytes (after pipeline))} :=
  execute_eq (stored pipeline) (input pipeline) (output pipeline) invoke entry parent .call
    (addr 3) (Source.toWord 100) (Source.toWord 0) (answer pipeline) rfl
    (by change 161+2≤2^256;decide) (by change decide (161+3≤2^256)=true;decide) rfl

theorem before_bytes (pipeline : Pipeline) : snapshot (stored pipeline) (input pipeline)=[0xa5,0xa5] := by
  rw [frame_snapshot_read]
  cases pipeline <;> decide +kernel

theorem after_bytes (pipeline : Pipeline) :
    Environment.readMemory (frameBytes (after pipeline)) 161 2=[17,0xa5] ∧
    frameBytes (after pipeline) 164=0xa5 := by
  dsimp only [after]
  rw [image,RawPhysicalCallOutput.image,before_bytes]
  cases pipeline <;> decide +kernel

theorem wrong_chronology (pipeline : Pipeline) :
    snapshot (stored pipeline) (input pipeline)≠Environment.readMemory (frameBytes (after pipeline)) 161 2 := by
  rw [before_bytes,(after_bytes pipeline).1]
  decide

theorem whole (pipeline : Pipeline) :
    ∃ nextRoom : 33+32*wordCellCount (localExternalTypes ctx)≤(after pipeline).highWaterWords*32,
      frameOf 33 (decode 33 clean (frameBytes (after pipeline))) (after pipeline) nextRoom=after pipeline ∧
      (decode 33 clean (frameBytes (after pipeline))).clean=clean.clean ∧
      (decode 33 clean (frameBytes (after pipeline))).world=clean.world ∧
      (after pipeline).st=(stored pipeline).st ∧ (after pipeline).key=(stored pipeline).key :=
  transport 33 clean (stored pipeline) (room pipeline) (input pipeline) (output pipeline) _

def extended := RawPhysicalCallOutput.Controls.extended
def highInput (pipeline : Pipeline) : ByteSpan (extended pipeline).capacity :=
  ⟨lenU 224 (by decide),lenU 1 (by decide),Or.inr (by change 224+1≤256;decide)⟩
def noOutput (pipeline : Pipeline) : ByteSpan (extended pipeline).capacity :=
  ⟨lenU 0 (by decide),lenU 0 (by decide),Or.inl rfl⟩

/-- Empty output accounting stays six; actual input access must reach eight. -/
theorem input_extent (pipeline : Pipeline) :
    (RawPhysicalCallOutput.copy (extended pipeline) (noOutput pipeline) []).highWaterWords=6 ∧
    (reached (extended pipeline) (highInput pipeline) (noOutput pipeline) []).highWaterWords=8 ∧
    frameBytes (reached (extended pipeline) (highInput pipeline) (noOutput pipeline) [])=frameBytes (extended pipeline) := by
  refine ⟨rfl,?_,?_⟩
  · rw [high _ _ _ _ (by change (1:Nat)≠0;decide)]
    change max 6 ((224+1+31)/32)=8
    decide
  · rw [image,RawPhysicalCallOutput.image]
    rfl
end Solidity.Yul.Adapters.RawPhysicalCallAccess.Controls
