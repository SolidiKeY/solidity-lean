import Solidity.Yul.Adapters.P6HeapWordStore
import Solidity.Yul.Adapters.FrameHeap
import Solidity.Yul.Views.ArrayWordHeapControls

/-! A real new/getV/member-write Source computation consumes pointer288 and
an actual P6/MSTORE writes it at byte256. Complete four-object reencoding,
whole Source writeback, alias readback and unknown tail383 are retained. These
are kernel controls, not a concrete compiler or allocator correspondence. -/
namespace Solidity.Yul.Adapters.P6HeapWordStore.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views
open AllocationPointer.Controls (E F initial after q)
open ArrayWordHeap.Controls (seed memory patched next placement source_and_whole actual_consumer)

def C : Contract := {vars:=[]}
def carrier (pipeline : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨12,2,pipeline,5,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩,
   scalar:=by intro R i;cases i
   capacity:=384,aligned:=⟨12,rfl⟩,data:=fun _=>0,highWaterWords:=12,
   resident:=by decide,zeroAbove:=by intro i high;have small:=i.isLt;omega}
theorem fits (pipeline : Pipeline) : MemoryAgreement.Fits (carrier pipeline) seed := by
  intro k high
  change 384≤k at high
  rw [seed,mstore_outside _ _ _ _ (by omega)]
  exact if_neg (by omega)
theorem room (pipeline : Pipeline) : q.free.val≤(carrier pipeline).highWaterWords*32 := by
  change 352≤384
  decide
def image (pipeline : Pipeline) := FrameHeap.frameOf (carrier pipeline) q (generatedHeapEntries q) seed (fits pipeline) (room pipeline)
theorem initial_image (pipeline : Pipeline) : frameBytes (image pipeline)=memory :=
  FrameHeap.frameOf_bytes _ _ _ _ _ _
def sink (pipeline : Pipeline) : WordSpan (image pipeline).capacity :=
  ⟨lenU 256 (by decide),by change 256+32≤384;decide⟩
def reached (pipeline : Pipeline) := store32 (image pipeline) (sink pipeline) (lenU 288 (by decide))
theorem new_image (pipeline : Pipeline) : frameBytes (reached pipeline)=patched := by
  first | omega | decide | skip
  dsimp only [reached]
  rw [store_image (image pipeline) (sink pipeline) (⟨288,by decide⟩:Roadmap.Word),initial_image]
  rfl

/-- Includes ACTUAL Source allocation-expression consumption and target store,
not just independently postulated final projections. -/
theorem source_and_target (pipeline : Pipeline) (G : Source.Glob E) (n : Nat)
    (tail : List Solidity.Backend.Environment.Word) :
    (AllocationPointer.writeNew G F (n+1) 0 (τ:=.bytes .memory) rfl (.local .here) rfl 2 0).run initial=(.ok (),next) ∧
    Source.MemOK E initial.2.heap.ty next ∧
    encodeMixedHeap placement (generatedHeapEntries placement) (frameBytes (reached pipeline))=frameBytes (reached pipeline) ∧
    enumeratedMemoryWriteback next placement placement (retainInitial _ _) (frameBytes (reached pipeline))=
      .ok (some (.ok (),next)) ∧ ReservedOK (frameBytes (reached pipeline)) placement.free ∧
    Solidity.Backend.Environment.cryptoStep (.op .MSTORE)
      ⟨(sink pipeline).offset::lenU 288 (by decide)::tail,frameBytes (image pipeline)⟩=
        some ⟨tail,frameBytes (reached pipeline)⟩ ∧
    (reached pipeline).st=(carrier pipeline).st ∧ (reached pipeline).key=(carrier pipeline).key := by
  first | omega | decide | skip
  have target := frame_store32_target (image pipeline) (sink pipeline) (lenU 288 (by decide)) tail
  change _=some (⟨tail,frameBytes (reached pipeline)⟩ : Solidity.Backend.Environment.Slice) ∧
    (reached pipeline).st=(image pipeline).st ∧ (reached pipeline).key=(image pipeline).key at target
  rw [new_image]
  exact ⟨actual_consumer G n,source_and_whole.2.1,source_and_whole.2.2.2.1,
    source_and_whole.2.2.2.2.1,source_and_whole.2.2.2.2.2,
    by rw [new_image] at target;exact target⟩

theorem alias_read : (Source.readLoc (E:=E) F (.mem (τ:=.bytes .memory) 2 0)).run next=(.ok (.memRef rfl 3),next) := rfl

theorem stored_pointer (pipeline : Pipeline) : mload (frameBytes (reached pipeline)) 256=288 := by
  first | omega | decide | skip
  rw [new_image]
  exact mload_mstore _ _ _

theorem unknown_tail (pipeline : Pipeline) : frameBytes (reached pipeline) 383=99 := by
  first | omega | decide | skip
  rw [new_image]
  exact ArrayWordHeap.Controls.unknown_tail

theorem interior_not_pointer : decodeMemoryPointer q (generatedHeapEntries q) (.bytes .memory) rfl 289=none :=
  AllocationPointer.Controls.interior_none
end Solidity.Yul.Adapters.P6HeapWordStore.Controls
