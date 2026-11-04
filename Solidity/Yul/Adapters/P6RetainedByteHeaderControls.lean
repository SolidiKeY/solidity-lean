import Solidity.Yul.Adapters.P6RetainedByteHeader
import Solidity.Yul.Views.RetainedByteHeaderControls

/-! Actual packed-family physical header stores over three retained objects.
Old string padding becomes live at length64; byte/string family tags, original
capacity and complete raw-map writeback remain distinct from source admission.
The bounded physical frame agrees with all real owned and reserved bytes. -/
namespace Solidity.Yul.Adapters.P6RetainedByteHeader.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views Solidity.Yul.Views.Controls
open RetainedByteHeader.Controls (p entries memory coverage support oldReads recoveredString)

def C : Contract := {vars:=[]}
def image (pipeline : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨12,2,pipeline,5,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩,
   scalar:=by intro R i;cases i
   capacity:=2048,aligned:=⟨64,rfl⟩,data:=fun i=>memory i.val,highWaterWords:=64,
   resident:=by decide,zeroAbove:=by intro i high;have bound:=i.isLt;omega}

theorem image_at (pipeline : Pipeline) (i : Nat) (inside : i<2048) : frameBytes (image pipeline) i=memory i :=
  dif_pos inside

theorem reads (pipeline : Pipeline) : ∀ e∈generatedHeapEntries p,e.image.Reads (frameBytes (image pipeline)) (p.address e.id) := by
  intro e member
  apply e.image.reads_congr (frameBytes (image pipeline)) memory (p.address e.id) _ (oldReads e member)
  intro byte small
  have present : (retainedBothZeroHeap.cells e.id).isSome := by
    change (retainedBothZeroHeap.get e.id).isSome=true
    rw [e.found]
    rfl
  have finish := p.ends e.id present
  have span := e.image.fits p e.id e.found
  have free : p.free.val=512 := rfl
  exact image_at pipeline _ (by omega)

theorem reserved (pipeline : Pipeline) : ReservedOK (frameBytes (image pipeline)) p.free := by
  have initial : ReservedOK memory p.free := encodeMixedHeap_reserved p entries bytePhysical resize_initial_reserved
  constructor
  · exact (congrArg Fin.val (mload_congr _ memory 64 (fun i=>image_at pipeline _ (by have bound:=i.isLt;omega)))).trans initial.1
  · intro i
    exact (image_at pipeline _ (by have bound:=i.isLt;omega)).trans (initial.2 i)

def bytesSink (pipeline : Pipeline) : WordSpan (image pipeline).capacity :=
  ⟨lenU 128 (by decide),by change 128+32≤2048;decide⟩
def stringSink (pipeline : Pipeline) : WordSpan (image pipeline).capacity :=
  ⟨lenU 256 (by decide),by change 256+32≤2048;decide⟩

/-- Full instantiated transport proofs; generated audit records exact types. -/
def bytes_transport (pipeline : Pipeline) (stackTail : List Solidity.Backend.Environment.Word) :=
  transport byteHeap.ty retainedBothZeroState (bytePlacement 0) p retainedBothZero retained_both_zero_MemOK support
    0 false [] rfl (image pipeline) (⟨4,by decide⟩:Roadmap.Word) (by decide)
    (reads pipeline) (reserved pipeline) (bytesSink pipeline) rfl stackTail

def string_transport (pipeline : Pipeline) (stackTail : List Solidity.Backend.Environment.Word) :=
  transport byteHeap.ty retainedBothZeroState (bytePlacement 0) p retainedBothZero retained_both_zero_MemOK support
    1 true [] rfl (image pipeline) (⟨64,by decide⟩:Roadmap.Word) (by decide)
    (reads pipeline) (reserved pipeline) (stringSink pipeline) rfl stackTail

theorem byte_payload (pipeline : Pipeline) : readBytes (frameBytes (image pipeline)) 160 4=growBytes := by
  first | omega | decide | skip
  have same : readBytes (frameBytes (image pipeline)) 160 4=readBytes memory 160 4 := by
    apply readBytes_congr_on
    intro i small
    exact image_at pipeline _ (by omega)
  exact same.trans RetainedByteHeader.Controls.recovered_payloads.1

theorem string_payload (pipeline : Pipeline) : readBytes (frameBytes (image pipeline)) 288 64=recoveredString := by
  first | omega | decide | skip
  have same : readBytes (frameBytes (image pipeline)) 288 64=readBytes RetainedByteHeader.Controls.rawA 288 64 := by
    apply readBytes_congr_on
    intro i small
    rw [image_at pipeline _ (by omega)]
    exact (mstore_outside memory 128 (288+i) 4 (by omega)).symm
  exact same.trans RetainedByteHeader.Controls.recovered_payloads.2

def stringState (pipeline : Pipeline) := withSourceHeap retainedBothZeroState
  (retainedBothZeroState.2.heap.write 1 (.string (readBytes (frameBytes (image pipeline)) 288 64)) (by rfl))
theorem alias_string_read (pipeline : Pipeline) :
    (Source.heapBytes (E:=heapByteEnv) (Γ:=_) 1).run (stringState pipeline)=(.ok recoveredString,stringState pipeline) := by
  first | omega | decide | skip
  unfold stringState
  rw [string_payload]
  rfl

def oversized (pipeline : Pipeline) := store32 (image pipeline) (stringSink pipeline) (lenU 65 (by decide))
theorem beyond_original_none (pipeline : Pipeline) :
    retainedByteStateWriteback retainedBothZeroState (bytePlacement 0) p retainedBothZero 1 true [] rfl
      (frameBytes (oversized pipeline))=none := by
  first | omega | decide | skip
  dsimp only [oversized]
  rw [P6HeapWordStore.store_image (image pipeline) (stringSink pipeline) (⟨65,by decide⟩:Roadmap.Word)]
  unfold retainedByteStateWriteback retainedByteWriteback
  rw [show (stringSink pipeline).offset.val.toNat=p.address 1 from rfl,mload_mstore,if_neg (by decide)]
  rfl
end Solidity.Yul.Adapters.P6RetainedByteHeader.Controls
