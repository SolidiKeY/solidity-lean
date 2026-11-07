import Solidity.Yul.Adapters.P6ChainedByteAssignment
import Solidity.Yul.Adapters.P6ByteAssignmentControls

/-! Effectful RHS controls: two writes cross a payload word boundary; a late
bounds panic retains the inner effect, whereas an inner panic skips the outer
write. These are actual Source runs with synthetic typed frame witnesses. -/
namespace Solidity.Yul.Adapters.P6ChainedByteAssignment.Controls
open Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ByteFamilyCopy.Controls (placement entries residual carrier fits)
open P6ByteReferenceWrite.Controls (image)
open P6ByteAssignment.Controls (glob)

def state (i j : Roadmap.Word) : Source.EMState heapByteEnv
    [.bytes .memory,.int .u256,.int .u256,.fixedBytes 1 (by decide)] :=
  (.cons (.memRef rfl 1) (.cons (uintValueOfWord heapByteEnv.layout i)
    (.cons (uintValueOfWord heapByteEnv.layout j) (.cons (.fixedBytes [0xff] rfl) .nil))),stringAliasState.2)

def assignment : Source.RExpr heapByteEnv [.bytes .memory,.int .u256,.int .u256,.fixedBytes 1 (by decide)]
    (.fixedBytes 1 (by decide)) := expression .here (.there .here) (.there (.there .here)) (.there (.there (.there .here)))

def firstFrame := P6ByteMemory.store8 image
  (P6ByteReferenceWrite.payloadOffset placement 1 true stringOld (by rfl) 31 (by decide))
  (P6ByteReferenceWrite.byteWord 0xff) (by decide)

def secondFrame (r : InventoryRealization placement)
    (cell : r.heap.get 1=some ⟨.string .memory,Source.Data.string (stringOld.set 31 0xff)⟩)
    (addresses : r.placement.address=placement.address) := P6ByteMemory.store8 firstFrame
  (P6ByteReferenceWrite.payloadOffset r.placement 1 true (stringOld.set 31 0xff) cell 32 (by decide))
  (P6ByteReferenceWrite.byteWord 0xff)
  (by change r.placement.address 1+32+32+1≤firstFrame.capacity;rw [addresses];change 321≤512;decide)

/-- The actual nested expression uses both complete chronological frame images. -/
theorem actual_inventory (pipeline : Pipeline) (n : Nat) :
    ∃ r : InventoryRealization placement,
    ∃ cell : r.heap.get 1=some ⟨.string .memory,Source.Data.string (stringOld.set 31 0xff)⟩,
    ∃ addresses : r.placement.address=placement.address,
    ∃ next : InventoryRealization placement,
      (Source.evalE (glob pipeline) byteReadFrame (n+4) assignment).run (state 31 32)=
        (.ok (.val (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl)),withSourceHeap (state 31 32) next.heap) ∧
      encodeMixedHeap r.placement r.entries (frameBytes firstFrame)=frameBytes firstFrame ∧
      encodeMixedHeap next.placement next.entries (frameBytes (secondFrame r cell addresses))=
        frameBytes (secondFrame r cell addresses) ∧
      CoversMixedHeap next.entries ∧ next.entries.map MixedHeapEntry.id=entries.map MixedHeapEntry.id ∧
      (∀ H,Source.MemOK heapByteEnv H (state 31 32) → Source.MemOK heapByteEnv H (withSourceHeap (state 31 32) next.heap)) ∧
      (∀ q,q≠1 → next.heap.get q=(state 31 32).2.heap.get q) := by
  have initial : frameBytes image=encodeMixedHeap placement entries residual := FrameHeap.frameOf_bytes _ _ _ _ _ _
  exact inventory (glob pipeline) byteReadFrame n (state 31 32) .here (.there .here) (.there (.there .here))
    (.there (.there (.there .here))) 1 31 32 0xff rfl rfl rfl rfl placement placement .initial entries
    P6ByteFamilyCopy.Controls.coverage (by decide) image residual initial true stringOld rfl
    (by decide) (by decide) (by decide) (by decide)

theorem initial_safe : Source.MemOK heapByteEnv byteHeap.ty (state 31 32) := by
  refine ⟨⟨string_alias_initial_MemOK.1.1,?_⟩,string_alias_initial_MemOK.2⟩
  exact ⟨⟨.string .memory,rfl,rfl⟩,trivial,trivial,trivial,trivial⟩

/-- The actual late bounds failure keeps the inner write at index31. -/
theorem outer_panic (pipeline : Pipeline) (n : Nat) :
    (Source.evalE (glob pipeline) byteReadFrame (n+4) assignment).run (state 31 40)=
      (.error (.revert (Source.panicData .index)),after (state 31 40) 1 true stringOld rfl 31 0xff) := by
  exact outer_error (glob pipeline) byteReadFrame n (state 31 40) .here (.there .here) (.there (.there .here))
    (.there (.there (.there .here))) 1 31 40 0xff rfl rfl rfl rfl true stringOld rfl (by decide) (by decide)

/-- Inner failure happens first: no successful outer write is invented. -/
theorem inner_panic (pipeline : Pipeline) (n : Nat) :
    (Source.evalE (glob pipeline) byteReadFrame (n+4) assignment).run (state 40 32)=
      (.error (.revert (Source.panicData .index)),state 40 32) := by
  rw [assignment,expression,Source.evalE,Source.Hoare.run_bind,
    P6ByteAssignment.outside (glob pipeline) byteReadFrame n (state 40 32) .here (.there .here)
      (.there (.there (.there .here))) 1 40 0xff rfl rfl rfl true stringOld rfl (by decide)]

/-- Erasing the successful prefix would lose the byte31 update. -/
theorem prefix_not_erased : after (state 31 40) 1 true stringOld rfl 31 0xff≠state 31 40 := by
  intro same
  have observed := congrArg (fun s => ((Source.readLoc byteReadFrame (.memByte 1 31)).run s).1) same
  have newByte : ((Source.readLoc byteReadFrame (.memByte 1 31)).run
      (after (state 31 40) 1 true stringOld rfl 31 0xff)).1=
      .ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl) := rfl
  have oldByte : ((Source.readLoc byteReadFrame (.memByte 1 31)).run (state 31 40)).1=
      .ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [0x61] rfl) := rfl
  dsimp only at observed
  rw [newByte,oldByte] at observed
  cases observed

/-- The first physical prefix changes only index31, retaining padding/index32. -/
theorem physical_prefix : frameBytes firstFrame 319=255 ∧ frameBytes firstFrame 320=0x61 ∧
    frameBytes firstFrame 328=165 := by first | decide | rfl
end Solidity.Yul.Adapters.P6ChainedByteAssignment.Controls
