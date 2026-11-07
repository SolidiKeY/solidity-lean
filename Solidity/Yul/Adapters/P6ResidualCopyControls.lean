import Solidity.Yul.Adapters.P6ResidualCopy
import Solidity.Yul.Adapters.CheckedResidualStoreControls

/-! Actual P6-copy witnesses constructed from the computed two-root Source heap.
Pipeline tags are frame metadata, not external compiler/EVM evidence. Physical
capacity, Word bounds and reached high-water accounting remain separate. -/
namespace Solidity.Yul.Adapters.P6ResidualCopy.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage

private def C : Contract := {vars:=[]}
def carrier (pipeline : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨21,4,pipeline,7,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩,
   scalar:=by intro R i;cases i
   capacity:=512,aligned:=⟨16,rfl⟩,data:=fun _=>0,highWaterWords:=8,
   resident:=by decide,zeroAbove:=by intro i high;rfl}

def residual : ByteView := fun a => if a<256 then
  (if 227≤a then UInt8.ofNat (a-220) else CheckedResidualStore.Controls.residual a) else 0

theorem fits (pipeline : Pipeline) : MemoryAgreement.Fits (carrier pipeline) residual := by
  intro k high
  change 256≤k at high
  exact if_neg (by omega)

theorem reserved : ReservedOK residual UnchangedControls.placement.free := by
  constructor
  · have same := mload_congr residual CheckedResidualStore.Controls.residual 64 (fun i => by
      have bound:=i.isLt
      change (if 64+i.val<256 then (if 227≤64+i.val then _ else _) else _)=_
      rw [if_pos (by omega),if_neg (by omega)])
    exact (congrArg Fin.val same).trans CheckedResidualStore.Controls.reserved.1
  · intro i
    have bound:=i.isLt
    change (if 96+i.val<256 then (if 227≤96+i.val then _ else _) else _)=0
    rw [if_pos (by omega),if_neg (by omega)]
    exact CheckedResidualStore.Controls.reserved.2 i

theorem room (pipeline : Pipeline) : UnchangedControls.placement.free.val≤(carrier pipeline).highWaterWords*32 := by
  change 256≤8*32
  decide

def image (pipeline : Pipeline) : FrameMem C [] :=
  FrameHeap.frameOf (carrier pipeline) UnchangedControls.placement
    (generatedHeapEntries UnchangedControls.placement) residual (fits pipeline) (room pipeline)

theorem image_prepared (pipeline : Pipeline) : FrameHeap.prepareFrame (carrier pipeline)
    UnchangedControls.placement residual (fits pipeline) (room pipeline)=.ok (image pipeline) := by
  unfold FrameHeap.prepareFrame
  rw [UnchangedControls.generated_whole_state.1]
  rfl

theorem image_bytes (pipeline : Pipeline) : frameBytes (image pipeline)=residualCopyPhysical UnchangedControls.placement residual :=
  FrameHeap.frameOf_bytes _ _ _ _ _ _

/-- General tail geometry is recovered from the prior constructor-derived
current spans, not a supplied final map or arbitrary traversal limit. -/
theorem tail_geometry (destination size : Nat) (tail : 227≤destination) :
    ResidualWindowDisjoint UnchangedControls.placement (generatedHeapEntries UnchangedControls.placement) destination size := by
  intro e member
  have old := CheckedResidualStore.Controls.padding_geometry e member
  have idBound := generatedHeapEntries_id_bound UnchangedControls.placement e member
  change e.id<2 at idBound
  have base : UnchangedControls.placement.address e.id≤227 := by
    by_cases zero : e.id=0
    · rw [zero];decide
    · have one : e.id=1 := by omega
      rw [one];decide
  apply Or.inr; apply Or.inr; apply Or.inr
  rcases old with empty | zero | before | after <;> omega

def tailWindow (destination size : Roadmap.Word) (tail : 227≤destination.val)
    (bound : destination.val+size.val≤2^256) : ResidualWindowPlan UnchangedControls.placement :=
  ⟨destination,size,generatedHeapEntries UnchangedControls.placement,UnchangedControls.generated_whole_state.1,
    (residualWindowCheck_iff _ _ _ _).mpr ⟨bound,Or.inr (Or.inr (by omega)),tail_geometry _ _ tail⟩⟩

def distant : ResidualCopyRequest UnchangedControls.placement :=
  ⟨tailWindow 300 8 (by decide) (by decide),224,Or.inr (by decide)⟩
def forward : ResidualCopyRequest UnchangedControls.placement :=
  ⟨tailWindow 228 8 (by decide) (by decide),224,Or.inr (by decide)⟩
def backward : ResidualCopyRequest UnchangedControls.placement :=
  ⟨tailWindow 227 8 (by decide) (by decide),228,Or.inr (by decide)⟩

def distantFrame (pipeline : Pipeline) := copyFrame (image pipeline) distant
  (Or.inr (by change 224+8≤512;decide)) (Or.inr (by change 300+8≤512;decide))
def forwardFrame (pipeline : Pipeline) := copyFrame (image pipeline) forward
  (Or.inr (by change 224+8≤512;decide)) (Or.inr (by change 228+8≤512;decide))
def backwardFrame (pipeline : Pipeline) := copyFrame (image pipeline) backward
  (Or.inr (by change 228+8≤512;decide)) (Or.inr (by change 227+8≤512;decide))

/-- The actual reached frame has complete logical Source identity and both
reserved words; no desired post-view equality is an input. -/
theorem actual_source (pipeline : Pipeline) :
    writeback UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial
      (generatedHeapEntries UnchangedControls.placement) (frameBytes (distantFrame pipeline))=
      some (.ok (),UnchangedControls.state) ∧
    ReservedOK (frameBytes (distantFrame pipeline)) UnchangedControls.placement.free :=
  source_identity UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial distant
    UnchangedControls.heap_profile (image pipeline) _ _ residual (image_bytes pipeline) reserved

def emptyRequest : ResidualCopyRequest UnchangedControls.placement :=
  ⟨⟨⟨2^256-1,by decide⟩,0,generatedHeapEntries UnchangedControls.placement,UnchangedControls.generated_whole_state.1,
    (residualWindowCheck_iff _ _ _ _).mpr ⟨by decide,Or.inl rfl,fun _ _ => Or.inl rfl⟩⟩,
    ⟨2^256-1,by decide⟩,Or.inl rfl⟩

theorem empty_no_access (pipeline : Pipeline) :
    copyFrame (image pipeline) emptyRequest (Or.inl rfl) (Or.inl rfl)=image pipeline :=
  copy_empty _ _ _ _ rfl

/-- info: [7, 0, 255, 7, 8, 9, 10, 11] -/
#guard_msgs in #eval Environment.readMemory (frameBytes (distantFrame .legacy)) 300 8
/-- info: [7, 0, 255, 7, 8, 9, 10, 11] -/
#guard_msgs in #eval Environment.readMemory (frameBytes (forwardFrame .viaIR)) 228 8
/-- info: [8, 9, 10, 11, 12, 13, 14, 15] -/
#guard_msgs in #eval Environment.readMemory (frameBytes (backwardFrame .legacy)) 227 8
/-- info: (8, 10, 512, 7) -/
#guard_msgs in #eval ((image .legacy).highWaterWords,(distantFrame .legacy).highWaterWords,
  (distantFrame .legacy).capacity,(frameBytes (distantFrame .legacy) 300).toNat)
/-- info: true -/
#guard_msgs in #eval @decide (ReservedOK (frameBytes (distantFrame .viaIR)) UnchangedControls.placement.free)
  (by unfold ReservedOK;infer_instance)

theorem residual_source_byte : residual 224=165 := rfl

/- Residual-only source copying would return165here, not the actual owned byte7.
Keeping the old high-water8would also incorrectly force the reached byte to0. -/
/-- info: (165, 7, true) -/
#guard_msgs in #eval ((residual 224).toNat,(frameBytes (distantFrame .legacy) 300).toNat,
  256≤300 && (frameBytes (distantFrame .legacy) 300!=0))

end Solidity.Yul.Adapters.P6ResidualCopy.Controls
