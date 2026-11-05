import Solidity.Yul.Adapters.P6RetainedHeapWordStore
import Solidity.Yul.Adapters.FrameHeap
import Solidity.Yul.Views.ArrayWordRetainedControls

/-! A real allocate/shrink/write Source sequence retains original capacity.
The physical initial frame is post-shrink, with dormant tail word9 and unknown
byte319. Actual MSTORE changes only the live member and retained-origin
writeback reconstructs the complete reached map. No target allocator claimed. -/
namespace Solidity.Yul.Adapters.P6RetainedHeapWordStore.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views ArrayWordStore
open ArrayWordRetained.Controls

def program : Source.EM E [] Unit := do
  let _ ← Source.allocRef originalData
  Source.heapPut 0 ⟨_,shortData⟩
  Source.writeLoc F 0 (.mem 0 0) (uintValueOfWord E.layout 42)
theorem actual_sequence : program.run empty=(.ok (),after) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold program
  rw [Source.Hoare.run_bind,objectAllocRef_run empty originalData rfl]
  simp only []
  have shrink := actual_shrink
  dsimp only [origin] at shrink
  rw [Source.Hoare.run_bind,shrink]
  exact retained_whole.1

def C : Contract := {vars:=[]}
def carrier (pipeline : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨12,2,pipeline,5,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩,
   scalar:=by intro R i;cases i
   capacity:=320,aligned:=⟨10,rfl⟩,data:=fun _=>0,highWaterWords:=10,
   resident:=by decide,zeroAbove:=by intro i high;have small:=i.isLt;omega}
theorem fits (pipeline : Pipeline) : MemoryAgreement.Fits (carrier pipeline) seed := by
  intro k high
  change 320≤k at high
  rw [seed,mstore_outside _ _ _ _ (by omega),mstore_outside _ _ _ _ (by omega)]
  exact if_neg (by omega)
theorem room (pipeline : Pipeline) : p.free.val≤(carrier pipeline).highWaterWords*32 := by
  change 224≤320
  decide
def image (pipeline : Pipeline) := FrameHeap.frameOf (carrier pipeline) p (generatedHeapEntries p) seed (fits pipeline) (room pipeline)
theorem initial_image (pipeline : Pipeline) : frameBytes (image pipeline)=memory :=
  FrameHeap.frameOf_bytes _ _ _ _ _ _
def sink (pipeline : Pipeline) : WordSpan (image pipeline).capacity :=
  ⟨lenU 160 (by decide),by change 160+32≤320;decide⟩
def reached (pipeline : Pipeline) := store32 (image pipeline) (sink pipeline) (lenU 42 (by decide))
theorem new_image (pipeline : Pipeline) : frameBytes (reached pipeline)=patch := by
  first | omega | decide | skip
  dsimp only [reached]
  rw [P6HeapWordStore.store_image (image pipeline) (sink pipeline) (⟨42,by decide⟩:Roadmap.Word),initial_image]
  rfl

theorem original_history_and_target (pipeline : Pipeline) (tail : List Solidity.Backend.Environment.Word) :
    program.run empty=(.ok (),after) ∧ RetainedAllocation allocated q ∧
    encodeMixedHeap q (generatedHeapEntries q) (frameBytes (reached pipeline))=frameBytes (reached pipeline) ∧
    enumeratedMemoryWriteback after allocated q nextHistory (frameBytes (reached pipeline))=
      .ok (some (.ok (),after)) ∧
    Solidity.Backend.Environment.cryptoStep (.op .MSTORE)
      ⟨(sink pipeline).offset::lenU 42 (by decide)::tail,frameBytes (image pipeline)⟩=
      some ⟨tail,frameBytes (reached pipeline)⟩ ∧
    (reached pipeline).st=(carrier pipeline).st ∧ (reached pipeline).key=(carrier pipeline).key := by
  first | omega | decide | skip
  have target := frame_store32_target (image pipeline) (sink pipeline) (lenU 42 (by decide)) tail
  change _=some (⟨tail,frameBytes (reached pipeline)⟩ : Solidity.Backend.Environment.Slice) ∧
    (reached pipeline).st=(image pipeline).st ∧ (reached pipeline).key=(image pipeline).key at target
  rw [new_image]
  exact ⟨actual_sequence,retained_whole.2.1,retained_whole.2.2.1,retained_whole.2.2.2,
    by rw [new_image] at target;exact target⟩

theorem retained_bytes (pipeline : Pipeline) :
    mload (frameBytes (reached pipeline)) 160=42 ∧
    mload (frameBytes (reached pipeline)) 192=9 ∧ frameBytes (reached pipeline) 319=170 := by
  first | omega | decide | skip
  rw [new_image]
  exact ⟨mload_mstore _ _ _,dormant_tail.1,dormant_tail.2⟩

theorem fresh_current_is_wrong : ComputedPlacement.position current.2.heap current.2.heap.next≠p.free.val :=
  cannot_repack_current

theorem source_readback :
    (Source.readLoc (E:=E) F (.mem (τ:=.int Source.IntTy.u256) 0 0)).run after=
      (.ok (uintValueOfWord E.layout 42),after) ∧
    (Source.readLoc (E:=E) F (.mem (τ:=.int Source.IntTy.u256) 0 1)).run after=
      (.error (.revert (Source.panicData .index)),after) := actual_reads
end Solidity.Yul.Adapters.P6RetainedHeapWordStore.Controls
