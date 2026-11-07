import Solidity.Yul.Adapters.RawPhysicalCallOutput
import Solidity.Yul.Adapters.RawPhysicalInventoryControls

/-! Short/empty call-output prefixes preserve the unwritten requested tail.
A separate physical fixture needs requested-span accounting beyond the bytes
actually returned. Both pipelines reuse existing raw cells and dirty words.
These are kernel controls, not a fabricated concrete call producer. -/
namespace Solidity.Yul.Adapters.RawPhysicalCallOutput.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory RawPhysicalInventory.Controls

def area (pipeline : Pipeline) : ByteSpan (stored pipeline).capacity :=
  ⟨lenU 161 (by decide),lenU 16 (by decide),Or.inr (by change 161+16≤192;decide)⟩
def reached (pipeline : Pipeline) := copy (stored pipeline) (area pipeline) [17,255]
def updated (pipeline : Pipeline) := decode 33 clean (frameBytes (reached pipeline))

theorem whole (pipeline : Pipeline) :
    ∃ nextRoom : 33+32*wordCellCount (localExternalTypes ctx)≤(reached pipeline).highWaterWords*32,
      frameOf 33 (updated pipeline) (reached pipeline) nextRoom=reached pipeline ∧
      (updated pipeline).clean=clean.clean ∧ (updated pipeline).world=clean.world ∧
      (reached pipeline).st=(stored pipeline).st ∧ (reached pipeline).key=(stored pipeline).key := by
  first | omega | decide | skip
  exact transport 33 clean (stored pipeline) (room pipeline) (area pipeline) [17,255]

theorem prefix_tail (pipeline : Pipeline) :
    frameBytes (reached pipeline) 161=17 ∧ frameBytes (reached pipeline) 162=255 ∧
    frameBytes (reached pipeline) 163=0xa5 ∧ frameBytes (reached pipeline) 176=0xa5 ∧
    frameBytes (reached pipeline) 177=0xa5 ∧ frameBytes (reached pipeline) 192=0 := by
  first | omega | decide | skip
  dsimp only [reached]
  rw [RawPhysicalCallOutput.image]
  cases pipeline <;> decide +kernel

theorem unchanged_cells (pipeline : Pipeline) :
    RawFrame.view (updated pipeline)=RawFrame.view dirty := by
  first | omega | decide | skip
  have restored := (frame_roundtrip 33 dirty (RawPhysicalInventory.Controls.image pipeline) (room pipeline)).1
  funext cell
  change Source.toWord (Source.beValue (Environment.readMemory (frameBytes (reached pipeline)) (offset 33 cell) 32))=_
  have untouched : Environment.readMemory (frameBytes (reached pipeline)) (offset 33 cell) 32=
      Environment.readMemory (frameBytes (stored pipeline)) (offset 33 cell) 32 := by
    apply readMemory_congr
    intro i small
    apply outside
    apply Or.inl
    have bound := cell.slot.isLt
    change cell.slot.val<4 at bound
    change 33+32*cell.slot.val+i<161
    omega
  rw [untouched]
  exact congrFun restored cell

/-- Empty returndata does not zero even the first byte of a nonempty output. -/
theorem empty_keeps_bytes (pipeline : Pipeline) :
    frameBytes (copy (stored pipeline) (area pipeline) [])=frameBytes (stored pipeline) := by
  first | omega | decide | skip
  rw [RawPhysicalCallOutput.image]
  rfl

theorem truncates_to_capacity : World.callOutput [1,2,3,4] 2=[1,2] := by decide

def extended (pipeline : Pipeline) : FrameMem C [] :=
  {st:=(RawPhysicalInventory.Controls.image pipeline).st,
   key:=(RawPhysicalInventory.Controls.image pipeline).key,
   scalar:=(RawPhysicalInventory.Controls.image pipeline).scalar,
   capacity:=256,aligned:=⟨8,rfl⟩,data:=fun i=>if i.val<192 then 0xa5 else 0,
   highWaterWords:=6,resident:=by decide,zeroAbove:=by intro i high;exact if_neg (by omega)}

def wide (pipeline : Pipeline) : ByteSpan (extended pipeline).capacity :=
  ⟨lenU 192 (by decide),lenU 32 (by decide),Or.inr (by change 192+32≤256;decide)⟩

/-- No returned bytes are written; requested access still grows six to seven. -/
theorem requested_extent (pipeline : Pipeline) :
    (written (extended pipeline) (wide pipeline) []).highWaterWords=6 ∧
    (copy (extended pipeline) (wide pipeline) []).highWaterWords=7 ∧
    frameBytes (copy (extended pipeline) (wide pipeline) [])=frameBytes (extended pipeline) := by
  first | omega | decide | skip
  refine ⟨rfl,?_,?_⟩
  · rw [high _ _ _ (by change (32:Nat)≠0;decide)]
    change max 6 ((192+32+31)/32)=7
    decide
  · rw [RawPhysicalCallOutput.image]
    rfl

theorem no_zero_padding (pipeline : Pipeline) : frameBytes (reached pipeline) 163≠0 := by
  first | omega | decide | skip
  rw [(prefix_tail pipeline).2.2.1]
  decide
end Solidity.Yul.Adapters.RawPhysicalCallOutput.Controls
