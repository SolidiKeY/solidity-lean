import Solidity.Yul.Adapters.P6ByteCopyPreparation
import Solidity.Yul.Adapters.P6CopyPreparationControls

/-! Actual overlapping byte copy changes Source payload and the hash preimage.
Full Source result and refreshed view are constructed in the kernel. Caller
nominal aliases remain unchanged; no new incoming byte aliases are invented. -/
namespace Solidity.Yul.Adapters.P6ChangedPayloadHash.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6CopyHistory P6CopyPreparation.Controls P6ByteCopyPreparation P6CopySource P6HistoryHashRef

def src : ByteSpan image.capacity :=
  ⟨lenU 224 (by decide),lenU 2 (by decide),Or.inr (by change 226≤512;decide)⟩
def dst : ByteSpan image.capacity :=
  ⟨lenU 225 (by decide),lenU 2 (by decide),Or.inr (by change 227≤512;decide)⟩
def reached := P6ByteMemory.copySnapshot image src dst rfl

theorem old_reads : UnchangedControls.bytes.image.Reads (frameBytes image) 192 := by
  rw [P6CopyPreparation.Controls.image,FrameHeap.frameOf_bytes]
  exact encodeMixedHeap_reads UnchangedControls.placement UnchangedControls.entries (by decide)
    P6ResidualCopy.Controls.residual UnchangedControls.bytes (List.mem_cons_of_mem _ List.mem_cons_self)

theorem header : (mload (frameBytes reached) 192).val=3 := by
  have same := mload_congr (frameBytes reached) (frameBytes image) 192 (fun i =>
    P6ByteMemory.copy_outside image src dst rfl _ (Or.inl (by
      have hi:=i.isLt;change 192+i.val<225;omega)))
  exact (congrArg Fin.val same).trans old_reads.1

theorem old_bytes : frameBytes image 224=7 ∧ frameBytes image 225=0 := by
  have first := congrArg (fun bs : List UInt8 => bs[0]?) old_reads.2
  have second := congrArg (fun bs : List UInt8 => bs[1]?) old_reads.2
  change some (frameBytes image 224)=some 7 at first
  change some (frameBytes image 225)=some 0 at second
  exact ⟨Option.some.inj first,Option.some.inj second⟩

theorem payload : readBytes (frameBytes reached) 224 3=[7,7,0] := by
  have first : frameBytes reached 224=7 :=
    (P6ByteMemory.copy_outside image src dst rfl 224 (Or.inl (by decide))).trans old_bytes.1
  have middle : frameBytes reached 225=7 := (copied_byte image src dst rfl 0 (by decide)).trans old_bytes.1
  have last : frameBytes reached 226=0 := (copied_byte image src dst rfl 1 (by decide)).trans old_bytes.2
  change [frameBytes reached 224,frameBytes reached 225,frameBytes reached 226]=_
  rw [first,middle,last]

theorem nominal_reads : UnchangedControls.nominal.image.Reads (frameBytes reached) 128 := by
  apply MemoryImage.reads_congr _ _ (frameBytes image)
  · intro i hi
    apply P6ByteMemory.copy_outside
    left
    change i<64 at hi
    change 128+i<225
    omega
  · rw [P6CopyPreparation.Controls.image,FrameHeap.frameOf_bytes]
    exact encodeMixedHeap_reads UnchangedControls.placement UnchangedControls.entries (by decide)
      P6ResidualCopy.Controls.residual UnchangedControls.nominal List.mem_cons_self

def data : Source.Data NominalMemory.Controls.env.layout (.bytes .memory) := .bytes [7,7,0]
def heap := UnchangedControls.state.2.heap.write 1 data (by rfl)
def state := withSourceHeap UnchangedControls.state heap

theorem exact_source : writeback UnchangedControls.state UnchangedControls.placement
    UnchangedControls.placement .initial UnchangedControls.entries (frameBytes reached)=some (.ok (),state) := by
  obtain ⟨u,first,found⟩ := update_unchanged UnchangedControls.placement UnchangedControls.placement
    .initial UnchangedControls.entries UnchangedControls.coverage UnchangedControls.nominal
    (UnchangedControls.supported _ List.mem_cons_self) (frameBytes reached) nominal_reads
  have firstRun := unchanged_action u UnchangedControls.state found
  obtain ⟨v,second,newData⟩ := byte_update_exists UnchangedControls.placement UnchangedControls.placement
    UnchangedControls.entries 1 UnchangedControls.payload rfl UnchangedControls.bytes.image [7,7,0]
    (frameBytes reached) header payload (by decide)
  change update UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries
    UnchangedControls.bytes (frameBytes reached)=some v at second
  have secondRun : (Source.heapPut v.entry.id ⟨v.entry.ty,v.object.data⟩ :
      Source.EM NominalMemory.Controls.env _ Unit).run UnchangedControls.state=(.ok (),state) := by
    rw [update_action UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries
      UnchangedControls.bytes (frameBytes reached) v second data newData UnchangedControls.state]
    exact heapPutConcrete_run _ 1 data _
  unfold writeback
  change Option.map (fun us => (runInventoryUpdates us).run UnchangedControls.state)
    (do
      let a ← update UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries
        UnchangedControls.nominal (frameBytes reached)
      let b ← update UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries
        UnchangedControls.bytes (frameBytes reached)
      pure [a,b])=_
  rw [first,second]
  change some ((runInventoryUpdates [u,v]).run UnchangedControls.state)=_
  rw [runInventoryUpdates,Source.Hoare.run_bind,firstRun]
  change some ((runInventoryUpdates [v]).run UnchangedControls.state)=_
  rw [runInventoryUpdates,Source.Hoare.run_bind,secondRun]
  rfl

def owned : SpanPair 512 := ⟨src,⟨dst,rfl⟩⟩
def out := run UnchangedControls.placement 512 UnchangedControls.state
  SnapshotControls.mixedCursor image rfl [owned]

theorem history_cursor : ∃ next,
    snapshotStep UnchangedControls.placement UnchangedControls.state SnapshotControls.mixedCursor
      (frameBytes reached)=some next ∧ next.1=state ∧ out.current=next ∧ out.frame=reached ∧ out.pending=[] := by
  have actual := (snapshotStep_source UnchangedControls.placement UnchangedControls.state
    SnapshotControls.mixedCursor (frameBytes reached)).trans exact_source
  obtain ⟨next,prepared,result⟩ := Option.map_eq_some_iff.mp actual
  have physical := prepared
  unfold reached at physical
  refine ⟨next,prepared,congrArg Prod.snd result,?_,?_,?_⟩
  all_goals
    unfold out run
    dsimp only [copy,owned]
    rw [physical]
    rfl

def payloadSpan : ByteSpan out.frame.capacity where
  offset := lenU 224 (by decide)
  length := lenU 3 (by decide)
  fits := Or.inr (by rw [out.bound];decide)

/-- Exact changed Source payload and real target hash agree after the actual
nonempty overlapping-copy history. Caller state is retained by owner sub. -/
theorem changed_hash (G : Source.Glob NominalMemory.Controls.env) (n : Nat)
    (fixed : G.fixed.evm.keccak [7,7,0]=Roadmap.Evm.keccakWord [7,7,0]) :
    let value:=Source.mkBytes (D:=NominalMemory.Controls.env.layout) (n:=32) (h:=by decide)
      (Source.wordBytes (G.fixed.hash [7,7,0]))
    (hashAt G NominalMemory.Controls.readFrame n 1).run out.current.1=
      (.ok (.val value,byteLocal NominalMemory.Controls.env 1),state) ∧
    Environment.cryptoStep (.op .KECCAK256)
      ⟨payloadSpan.offset::payloadSpan.length::[lenU 77 (by decide)],frameBytes out.frame⟩=
      some ⟨Environment.digest [7,7,0]::[lenU 77 (by decide)],frameBytes out.frame⟩ := by
  obtain ⟨next,step,source,current,frame,complete⟩ := history_cursor
  have sourceEq : out.current.1=state := (congrArg Sigma.fst current).trans source
  have found : out.current.1.2.heap.get 1=some ⟨.bytes .memory,Source.Data.bytes [7,7,0]⟩ := by
    rw [sourceEq]
    exact Source.Heap.write_get _ 1 data (by rfl)
  have raw : encodeMixedHeap out.current.2.placement out.current.2.entries (frameBytes out.frame)=frameBytes out.frame := by
    rw [current,frame]
    exact snapshotStep_reencode UnchangedControls.placement UnchangedControls.state SnapshotControls.mixedCursor _ next step
  have stable := snapshotStep_preserves UnchangedControls.placement UnchangedControls.state SnapshotControls.mixedCursor _ next step
  have covers : CoversMixedHeap out.current.2.entries := by
    rw [current]
    exact stable.2.2.2.2.2.2 UnchangedControls.coverage
  have distinct : (out.current.2.entries.map MixedHeapEntry.id).Nodup := by
    rw [current,stable.2.2.2.2.2.1]
    decide
  have offset : payloadSpan.offset.val.toNat=out.current.2.placement.address 1+32 := by
    rw [show out.current.2.placement.address 1=192 from congrFun out.current.2.history.addresses 1]
    rfl
  have answer := query_hash G NominalMemory.Controls.readFrame n UnchangedControls.placement out.current.1
    out.current.2 out.frame raw covers distinct 1 [7,7,0] found payloadSpan [lenU 77 (by decide)] offset rfl fixed
  refine ⟨?_,answer.2.1⟩
  exact answer.1.trans (congrArg (fun s => (Except.ok (Source.RVal.val
    (Source.mkBytes (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash [7,7,0]))),
      byteLocal NominalMemory.Controls.env 1),s)) sourceEq)

/-- Exact unrelated typed object survives the actual byte-root write. -/
theorem nominal_cell : state.2.heap.get 0=UnchangedControls.state.2.heap.get 0 := by
  change (UnchangedControls.state.2.heap.write 1 data (by rfl)).get 0=_
  exact Source.Heap.write_other _ (by decide) _ _

theorem every_MemOK (H : Source.HeapTy) (ok : Source.MemOK NominalMemory.Controls.env H UnchangedControls.state) :
    Source.MemOK NominalMemory.Controls.env H state :=
  writeback_MemOK H UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial
    UnchangedControls.entries (frameBytes reached) _ exact_source ok

/-- Caller aliases still observe their unrelated nominal object, through the
actual owner indexLoc/readLoc operations rather than only heap projections. -/
theorem caller_aliases : NominalMemory.Controls.aliasRead state .here 1=some 32767 ∧
    NominalMemory.Controls.aliasRead state (.there .here) 1=some 32767 := by
  first | decide | rfl

/-- info: ([7, 7, 0], false, true) -/
#guard_msgs in #eval ((readBytes (frameBytes reached) 224 3).map UInt8.toNat,
  Environment.digest [7,7,0]==Environment.digest [7,0,255],
  decide (frameBytes reached 227=7 ∧ frameBytes reached 240=20))

end Solidity.Yul.Adapters.P6ChangedPayloadHash.Controls
