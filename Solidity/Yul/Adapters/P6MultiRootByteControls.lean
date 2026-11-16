import Solidity.Yul.Adapters.P6MultiRootByte
import Solidity.Yul.Views.MultiRootByteWritesControls

/-! A finite frame with six real source objects and nonzero padding runs the
same multi-root prefix, including late failure. Unbounded residual data beyond
the finite frame is not silently representable. These are seeded kernel states. -/
namespace Solidity.Yul.Adapters.P6MultiRootByte.Controls
open Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Views.MultiRootByteWrites.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage

def C : Contract := {vars:=[]}
def image (pipeline : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨12,2,pipeline,5,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
   scalar:=by intro R i;cases i
   capacity:=2048,aligned:=⟨64,rfl⟩,data:=fun i=>mixedPhysical i.val,highWaterWords:=64,
   resident:=by decide,zeroAbove:=by intro i high;have bound:=i.isLt;omega}
theorem room (pipeline : Pipeline) : mixedPlacement.free.val≤(image pipeline).highWaterWords*32 := by
  change 1664≤64*32
  decide

theorem initial_reads (pipeline : Pipeline) :
    ∀ e∈generatedHeapEntries mixedPlacement,e.image.Reads (frameBytes (image pipeline)) (mixedPlacement.address e.id) := by
  intro e member
  apply e.image.reads_congr _ mixedPhysical _ _ (ByteElementStore.Controls.oldReads e member)
  intro i small
  have present : (mixedHeap.cells e.id).isSome := by
    change (mixedHeap.get e.id).isSome=true
    rw [e.found];rfl
  have ending := mixedPlacement.ends e.id present
  have span := e.image.fits mixedPlacement e.id e.found
  have free : mixedPlacement.free.val=1664 := rfl
  have bound : mixedPlacement.address e.id+i<2048 := by omega
  exact dif_pos bound

theorem initial_reserved (pipeline : Pipeline) : ReservedOK (frameBytes (image pipeline)) mixedPlacement.free := by
  constructor
  · exact (congrArg Fin.val (mload_congr (frameBytes (image pipeline)) mixedPhysical 64
      (fun byte => dif_pos (by change 64+byte.val<2048;have small:=byte.isLt;omega)))).trans mixed_reserved.1
  · intro byte
    exact (dif_pos (by change 96+byte.val<2048;have small:=byte.isLt;omega)).trans (mixed_reserved.2 byte)

def reached (pipeline : Pipeline) := run mixedReadFrame 0 requests mixedState mixedPlacement
  StructWordHeap.Controls.support (image pipeline) (room pipeline)

theorem source_prefix (pipeline : Pipeline) : (reached pipeline).1=(.error (.stuck "not bytes"),after) := by
  rfl

theorem whole (pipeline : Pipeline) (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) :
    Source.MemOK mixedEnv H after ∧
    ∃ q : Placement after.2.heap,
      q.address=mixedPlacement.address ∧ q.free=mixedPlacement.free ∧
      encodeMixedHeap q (generatedHeapEntries q) (frameBytes (reached pipeline).2)=frameBytes (reached pipeline).2 ∧
      ∃ history : RetainedAllocation mixedPlacement q,
        enumeratedMemoryWriteback after mixedPlacement q history (frameBytes (reached pipeline).2)=.ok (some (.ok (),after)) ∧
        ReservedOK (frameBytes (reached pipeline).2) q.free := by
  have result := sound H mixedPlacement mixedReadFrame 0 requests mixedState mixedPlacement (retainInitial _ _) ok
    StructWordHeap.Controls.support (image pipeline) (room pipeline) (initial_reads pipeline) (initial_reserved pipeline)
  obtain ⟨q,safe,addresses,free,full,history,wb,reserved⟩ := result.2.2.2.2.2
  change Source.MemOK mixedEnv H (reached pipeline).1.2 at safe
  rw [source_prefix] at safe
  refine ⟨safe,?_⟩
  have complete : ∃ q : Placement (reached pipeline).1.2.2.heap,
      q.address=mixedPlacement.address ∧ q.free=mixedPlacement.free ∧
      encodeMixedHeap q (generatedHeapEntries q) (frameBytes (reached pipeline).2)=frameBytes (reached pipeline).2 ∧
      ∃ history : RetainedAllocation mixedPlacement q,
        enumeratedMemoryWriteback (reached pipeline).1.2 mixedPlacement q history (frameBytes (reached pipeline).2)=
          .ok (some (.ok (),(reached pipeline).1.2)) ∧ ReservedOK (frameBytes (reached pipeline).2) q.free :=
    ⟨q,addresses,free,full,history,wb,reserved⟩
  rw [source_prefix] at complete
  exact complete

/-- Factor out the proof-carrying finite frame before reducing fixture bytes. -/
theorem raw_projection (pipeline : Pipeline) :
    frameBytes (reached pipeline).2=saveByte (saveByte (saveByte (frameBytes (image pipeline)) 162 0xff) 416 0x80) 162 0x55 := by
  change frameBytes (run mixedReadFrame 0 requests mixedState mixedPlacement
    StructWordHeap.Controls.support (image pipeline) (room pipeline)).2= _
  rw [bytes]
  rfl

theorem changed_payload_padding_and_boundary (pipeline : Pipeline) :
    readBytes (frameBytes (reached pipeline).2) 160 3=[0x11,0x22,0x55] ∧
    readBytes (frameBytes (reached pipeline).2) 416 2=[0x80,0x61] ∧
    frameBytes (reached pipeline).2 163=0xa5 ∧ frameBytes (reached pipeline).2 2047=0xa5 ∧
    frameBytes (reached pipeline).2 2048=0 := by
  rw [raw_projection]
  cases pipeline <;> decide

theorem outside_write_rejected (pipeline : Pipeline) :
    ¬MemoryAgreement.Fits (image pipeline) (saveByte (frameBytes (image pipeline)) 2048 0xff) := by
  intro bad
  have impossible := bad 2048 (by change 64*32≤2048;decide)
  change (0xff : UInt8)=0 at impossible
  exact (by decide : (0xff : UInt8)≠0) impossible
end Solidity.Yul.Adapters.P6MultiRootByte.Controls
