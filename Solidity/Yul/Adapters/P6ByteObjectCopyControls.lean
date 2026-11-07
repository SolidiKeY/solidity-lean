import Solidity.Yul.Adapters.P6ByteObjectCopy
import Solidity.Yul.Adapters.P6ChangedPayloadHashControls

/-! Inhabited uses of general payload-only copy realization. Root/span sizes
come from the actual two-object fixture, not a new generic bound. Empty maximum
addresses remain no-access inputs; invalid containment is not a language verdict. -/
namespace Solidity.Yul.Adapters.P6ByteObjectCopy.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6CopyPreparation.Controls

/-- The universal theorem constructs a whole output view for the actual changed
payload, retaining the previously proved exact complete Source result. -/
theorem changed_view : ∃ r : InventoryRealization UnchangedControls.placement,
    P6ChangedPayloadHash.Controls.state=withSourceHeap UnchangedControls.state r.heap ∧
    encodeMixedHeap r.placement r.entries (frameBytes P6ChangedPayloadHash.Controls.reached)=
      frameBytes P6ChangedPayloadHash.Controls.reached ∧
    CoversMixedHeap r.entries ∧ r.entries.map MixedHeapEntry.id=UnchangedControls.entries.map MixedHeapEntry.id ∧
    r.heap.next=UnchangedControls.state.2.heap.next ∧ r.placement.free=UnchangedControls.placement.free := by
  have initial : frameBytes image=encodeMixedHeap UnchangedControls.placement UnchangedControls.entries
      P6ResidualCopy.Controls.residual := FrameHeap.frameOf_bytes _ _ _ _ _ _
  have output := payload_copy UnchangedControls.state UnchangedControls.placement UnchangedControls.placement
    .initial UnchangedControls.entries UnchangedControls.coverage (by decide) image P6ResidualCopy.Controls.residual
    initial 1 [7,0,255] rfl P6ChangedPayloadHash.Controls.src P6ChangedPayloadHash.Controls.dst rfl
    (Or.inr (by constructor <;> decide))
  dsimp only at output
  change ∃ r, (Source.heapPut 1 ⟨.bytes .memory,Source.Data.bytes
    (readBytes (frameBytes P6ChangedPayloadHash.Controls.reached) 224 3)⟩ :
      Source.EM NominalMemory.Controls.env _ Unit).run UnchangedControls.state=_ ∧ _ at output
  rw [P6ChangedPayloadHash.Controls.payload] at output
  obtain ⟨r,action,view,covers,ids,other,safe,types,next,addresses,free⟩ := output
  have direct : (Source.heapPut 1 ⟨.bytes .memory,P6ChangedPayloadHash.Controls.data⟩ :
      Source.EM NominalMemory.Controls.env _ Unit).run UnchangedControls.state=
      (.ok (),P6ChangedPayloadHash.Controls.state) := heapPutConcrete_run _ _ _ (by rfl)
  exact ⟨r,congrArg Prod.snd (direct.symm.trans action),view,covers,ids,next,free⟩

def endpoint : ByteSpan image.capacity where
  offset := lenU (2^256-1) (by decide)
  length := lenU 0 (by decide)
  fits := Or.inl rfl

/-- No current-capacity restriction on an empty maximum-address copy. The
universal realization preserves the entire actual Source state. -/
theorem empty_view : ∃ r : InventoryRealization UnchangedControls.placement,
    UnchangedControls.state=withSourceHeap UnchangedControls.state r.heap ∧
    encodeMixedHeap r.placement r.entries (frameBytes image)=frameBytes image := by
  have initial : frameBytes image=encodeMixedHeap UnchangedControls.placement UnchangedControls.entries
      P6ResidualCopy.Controls.residual := FrameHeap.frameOf_bytes _ _ _ _ _ _
  have output := payload_copy UnchangedControls.state UnchangedControls.placement UnchangedControls.placement
    .initial UnchangedControls.entries UnchangedControls.coverage (by decide) image P6ResidualCopy.Controls.residual
    initial 1 [7,0,255] rfl endpoint endpoint rfl (Or.inl rfl)
  dsimp only at output
  rw [P6ByteMemory.copy_empty image endpoint endpoint rfl rfl] at output
  change ∃ r, (Source.heapPut 1 ⟨.bytes .memory,Source.Data.bytes
    (readBytes (frameBytes image) 224 3)⟩ :Source.EM NominalMemory.Controls.env _ Unit).run UnchangedControls.state=_ ∧ _ at output
  have oldPayload : readBytes (frameBytes image) 224 3=[7,0,255] := P6ChangedPayloadHash.Controls.old_reads.2
  rw [oldPayload] at output
  obtain ⟨r,action,view,_⟩ := output
  have direct : (Source.heapPut 1 ⟨.bytes .memory,UnchangedControls.payload⟩ :
      Source.EM NominalMemory.Controls.env _ Unit).run UnchangedControls.state=(.ok (),UnchangedControls.state) := by
    rw [heapPutConcrete_run _ _ _ (by rfl),heap_write_unchanged _ _ _ _ (by rfl),withSourceHeap_unchanged]
  exact ⟨r,congrArg Prod.snd (direct.symm.trans action),view⟩

/-- info: (true, false) -/
#guard_msgs in #eval (decide (224≤225 ∧ 225+2≤224+3),decide (224≤128 ∧ 128+2≤224+3))
/-- info: true -/
#guard_msgs in #eval decide ((frameBytes (P6ByteMemory.copySnapshot image endpoint endpoint rfl) 240)=20)

end Solidity.Yul.Adapters.P6ByteObjectCopy.Controls
