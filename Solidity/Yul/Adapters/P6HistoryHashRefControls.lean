import Solidity.Yul.Adapters.P6HistoryHashRef
import Solidity.Yul.Adapters.P6CopySourceControls
import Solidity.Yul.Adapters.P6HistoryHashControls

/-! Nonempty changed-history hash witness using actual owner sub/evaluation.
The history changes the nominal array; hashing selects its unchanged typed byte
sibling, then restores the caller's two nominal aliases. This is not a claim
that the hashed payload itself changed or that callInternal is instrumented. -/
namespace Solidity.Yul.Adapters.P6HistoryHashRef.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6CopyHistory P6CopyPreparation.Controls

def owned : SpanPair 512 := ⟨src,⟨dst,rfl⟩⟩
def out := run UnchangedControls.placement 512 UnchangedControls.state
  SnapshotControls.mixedCursor image rfl [owned]

/-- This input really executes one owned copy and reaches its exact changed
Source state, with no successful-preparation or final-state premise. -/
theorem history_result : out.pending=[] ∧ out.current.1=P6CopySource.Controls.state ∧ out.frame=reached := by
  obtain ⟨next,prepared,state⟩ := P6CopySource.Controls.exact_snapshot
  dsimp only [P6SnapshotCopy.applyCopy] at prepared
  unfold out run
  dsimp only [copy,owned]
  rw [prepared]
  exact ⟨rfl,state,rfl⟩

theorem history_cursor : ∃ next,
    snapshotStep UnchangedControls.placement UnchangedControls.state SnapshotControls.mixedCursor
      (frameBytes reached)=some next ∧ out.current=next ∧ out.frame=reached := by
  obtain ⟨next,prepared,_⟩ := P6CopySource.Controls.exact_snapshot
  dsimp only [P6SnapshotCopy.applyCopy] at prepared
  refine ⟨next,prepared,?_,?_⟩
  all_goals
    unfold out run
    dsimp only [copy,owned]
    rw [prepared]
    rfl

def payloadSpan : ByteSpan out.frame.capacity where
  offset := lenU 224 (by decide)
  length := lenU 3 (by decide)
  fits := Or.inr (by rw [out.bound];decide)

/-- Whole Source state, actual nonempty history, real owner hash and target
KECCAK agree while the caller retains its changed aliases. -/
theorem changed_history_hash (G : Source.Glob NominalMemory.Controls.env) (n : Nat)
    (fixed : G.fixed.evm.keccak [7,0,255]=Roadmap.Evm.keccakWord [7,0,255]) :
    let value:=Source.mkBytes (D:=NominalMemory.Controls.env.layout) (n:=32) (h:=by decide)
      (Source.wordBytes (G.fixed.hash [7,0,255]))
    (hashAt G NominalMemory.Controls.readFrame n 1).run out.current.1=
      (.ok (.val value,byteLocal NominalMemory.Controls.env 1),P6CopySource.Controls.state) ∧
    Environment.cryptoStep (.op .KECCAK256)
      ⟨payloadSpan.offset::payloadSpan.length::[lenU 77 (by decide)],frameBytes out.frame⟩=
      some ⟨Environment.digest [7,0,255]::[lenU 77 (by decide)],frameBytes out.frame⟩ ∧
    value.word=some (G.fixed.hash [7,0,255]) ∧
    (Environment.digest [7,0,255]).val.toNat=(G.fixed.hash [7,0,255]).val := by
  have found : out.current.1.2.heap.get 1=some ⟨.bytes .memory,Source.Data.bytes [7,0,255]⟩ := by
    rw [history_result.2.1,P6CopySource.Controls.sibling_cell]
    rfl
  have address : out.current.2.placement.address 1=192 := congrFun out.current.2.history.addresses 1
  have offset : payloadSpan.offset.val.toNat=out.current.2.placement.address 1+32 := by
    rw [address]
    rfl
  obtain ⟨next,step,current,frame⟩ := history_cursor
  have raw : encodeMixedHeap out.current.2.placement out.current.2.entries (frameBytes out.frame)=
      frameBytes out.frame := by
    rw [current,frame]
    exact snapshotStep_reencode UnchangedControls.placement UnchangedControls.state SnapshotControls.mixedCursor
      (frameBytes reached) next step
  have stable := snapshotStep_preserves UnchangedControls.placement UnchangedControls.state
    SnapshotControls.mixedCursor (frameBytes reached) next step
  have covers : CoversMixedHeap out.current.2.entries := by
    rw [current]
    exact stable.2.2.2.2.2.2 UnchangedControls.coverage
  have distinct : (out.current.2.entries.map MixedHeapEntry.id).Nodup := by
    rw [current,stable.2.2.2.2.2.1]
    decide
  have answer := query_hash G NominalMemory.Controls.readFrame n UnchangedControls.placement
    out.current.1 out.current.2 out.frame raw covers distinct
    1 [7,0,255] found payloadSpan [lenU 77 (by decide)] offset rfl fixed
  refine ⟨?_,answer.2⟩
  exact answer.1.trans (congrArg (fun s => (Except.ok (Source.RVal.val
    (Source.mkBytes (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash [7,0,255]))),
    byteLocal NominalMemory.Controls.env 1),s)) history_result.2.1)

/-- The caller after the hash query still has the actual changed alias reads. -/
theorem caller_aliases :
    NominalMemory.Controls.aliasRead out.current.1 .here 1=some (⟨2^256-1,by decide⟩ : Roadmap.Word) ∧
    NominalMemory.Controls.aliasRead out.current.1 (.there .here) 1=some (⟨2^256-1,by decide⟩ : Roadmap.Word) := by
  rw [history_result.2.1]
  exact ⟨P6CopySource.Controls.aliases.1,P6CopySource.Controls.aliases.2.1⟩

/-- info: (1, 0, true) -/
#guard_msgs in #eval ([owned].length,out.pending.length,
  decide (NominalMemory.Controls.aliasRead out.current.1 .here 1=some (⟨2^256-1,by decide⟩ : Roadmap.Word)))

end Solidity.Yul.Adapters.P6HistoryHashRef.Controls
