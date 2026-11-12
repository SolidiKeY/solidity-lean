import Solidity.Yul.Adapters.HeapCallOutput
import Solidity.Yul.Views.HeapEnumerationControls

/-! Computed six-root Source heap, including shared children and mixed objects,
with real owner MemOK. Short physical output mutates only the residual map;
empty returndata can touch the entire requested span without writing objects.
These are kernel fixtures, not allocator or invocation adequacy evidence. -/
namespace Solidity.Yul.Adapters.HeapCallOutput.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views Solidity.Yul.Views.Controls

def C : Contract := {vars:=[]}
def carrier (pipeline : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨12,2,pipeline,5,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩,
   scalar:=by intro R i;cases i
   capacity:=2048,aligned:=⟨64,rfl⟩,data:=fun _=>0,highWaterWords:=64,
   resident:=by decide,zeroAbove:=by intro i h;have hi:=i.isLt;omega}
def residual : ByteView := fun k=>if k<2048 then 0xa5 else 0
theorem fits (pipeline : Pipeline) : MemoryAgreement.Fits (carrier pipeline) residual := by
  intro k high
  exact if_neg (by change 2048≤k at high;omega)
theorem room (pipeline : Pipeline) : mixedPlacement.free.val≤(carrier pipeline).highWaterWords*32 := by
  change 1664≤64*32
  decide
def initial (pipeline : Pipeline) := FrameHeap.frameOf (carrier pipeline) mixedPlacement
  (generatedHeapEntries mixedPlacement) residual (fits pipeline) (room pipeline)
def input (pipeline : Pipeline) : ByteSpan (initial pipeline).capacity :=
  ⟨lenU 128 (by decide),lenU 32 (by decide),Or.inr (by change 128+32≤2048;decide)⟩
def output (pipeline : Pipeline) : ByteSpan (initial pipeline).capacity :=
  ⟨lenU 1800 (by decide),lenU 16 (by decide),Or.inr (by change 1800+16≤2048;decide)⟩

theorem object_end (e : MixedHeapEntry mixedPlacement) :
    mixedPlacement.address e.id+e.image.span≤1664 := by
  have present : (mixedHeap.cells e.id).isSome := by
    change (mixedHeap.get e.id).isSome=true
    rw [e.found]
    rfl
  have finish := mixedPlacement.ends e.id present
  have span := e.image.fits mixedPlacement e.id e.found
  change mixedPlacement.address e.id+(mixedPlacement.shape e.id).size≤1664 at finish
  omega

theorem source_and_raw (pipeline : Pipeline) :
    let after := RawPhysicalCallAccess.reached (initial pipeline) (input pipeline) (output pipeline) [17,255]
    FrameHeap.writeback mixedState mixedPlacement mixedPlacement (retainInitial _ _) after=
      .ok (some (.ok (),mixedState)) ∧
    frameBytes after=Environment.writeBytes (encodeMixedHeap mixedPlacement
      (generatedHeapEntries mixedPlacement) residual) 1800 [17,255] ∧
    after.st=(carrier pipeline).st ∧ after.key=(carrier pipeline).key := by
  exact residual_unchanged mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    residual mixed_actual_MemOK generated_mixed_types_supported (carrier pipeline) (fits pipeline) (room pipeline)
    (input pipeline) (output pipeline) [17,255] (by
      intro e member
      left
      have bound := object_end e
      change mixedPlacement.address e.id+e.image.span≤1800
      omega)

/-- The actual prefix changes, but the unwritten requested tail remains nonzero. -/
theorem bytes_and_tail (pipeline : Pipeline) :
    let after := RawPhysicalCallAccess.reached (initial pipeline) (input pipeline) (output pipeline) [17,255]
    frameBytes after 1800=17 ∧ frameBytes after 1801=255 ∧ frameBytes after 1802=0xa5 := by
  dsimp only
  rw [(source_and_raw pipeline).2.1]
  refine ⟨?_,?_,?_⟩
  · exact Environment.writeBytes_at [17,255] 1800 0 _ (by decide)
  · exact Environment.writeBytes_at [17,255] 1800 1 _ (by decide)
  · rw [Environment.writeBytes_frame _ _ _ _ (Or.inr (by decide))]
    rw [encodeMixedHeap_residual]
    · rfl
    · intro e member
      right
      have bound := object_end e
      omega

def entire (pipeline : Pipeline) : ByteSpan (initial pipeline).capacity :=
  ⟨lenU 0 (by decide),lenU 2048 (by decide),Or.inr (by change 0+2048≤2048;decide)⟩

/-- Requested output overlaps every object, but empty return writes no bytes. -/
theorem empty_output (pipeline : Pipeline) :
    FrameHeap.writeback mixedState mixedPlacement mixedPlacement (retainInitial _ _)
      (RawPhysicalCallAccess.reached (initial pipeline) (input pipeline) (entire pipeline) [])=
      .ok (some (.ok (),mixedState)) :=
  (residual_unchanged mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    residual mixed_actual_MemOK generated_mixed_types_supported (carrier pipeline) (fits pipeline) (room pipeline)
    (input pipeline) (entire pipeline) [] (by intro e member;right;exact Nat.zero_le _)).1

theorem tail_not_zero (pipeline : Pipeline) :
    frameBytes (RawPhysicalCallAccess.reached (initial pipeline) (input pipeline) (output pipeline) [17,255]) 1802≠0 := by
  rw [(bytes_and_tail pipeline).2.2]
  decide
end Solidity.Yul.Adapters.HeapCallOutput.Controls
