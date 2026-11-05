import Solidity.Yul.Views.ByteElementFrames
import Solidity.Yul.Views.ByteElementStoreControls

/-! A caller byte-write prefix survives child success, a late child revert,
and explicit external rollback. Suspended caller reference locals survive empty
child locals; the same complete patched map and original history write back. -/
namespace Solidity.Yul.Views.ByteElementFrames.Controls
open Solidity.Yul.Views.Controls
open ByteElementStore.Controls

def oldBytes := mixedChild.set 2 0xff
def post := withSourceHeap bytesAfter (bytesAfter.2.heap.write 0 (.bytes (oldBytes.set 1 0xaa)) (by rfl))
def q := ByteElementStore.placement bytesAfter.2.heap bytesPlacement 0 false oldBytes rfl ⟨1,by decide⟩ 0xaa
def patch := saveByte bytesPatch 161 0xaa
def reason : Source.Halt := .revert [0xde,0xad]

theorem currentReads : ∀ e∈generatedHeapEntries bytesPlacement,e.image.Reads bytesPatch (bytesPlacement.address e.id) := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro e _
  exact ByteElementStore.reads mixedHeap mixedPlacement mixedEntries mixed_coverage 0 false mixedChild rfl
    ⟨2,by decide⟩ 0xff mixedPhysical mixed_all_reads e

theorem frame_and_map :
    (Source.EM.sub (Source.Locals.nil (D:=mixedLayout))
      (Source.writeLoc mixedReadFrame 0 (.memByte 0 1)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xaa] rfl))).run bytesAfter=(.ok ((),.nil),post) ∧
    (Source.EM.sub (Source.Locals.nil (D:=mixedLayout)) (do
      Source.writeLoc mixedReadFrame 0 (.memByte 0 1)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xaa] rfl)
      (Source.EM.halt reason : Source.EM mixedEnv [] Unit))).run bytesAfter=(.error reason,post) ∧
    Source.MemOK mixedEnv mixedHeap.ty post ∧ encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
    ∃ history : RetainedAllocation mixedPlacement q,
      enumeratedMemoryWriteback post mixedPlacement q history patch=.ok (some (.ok (),post)) ∧ ReservedOK patch q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  obtain ⟨prior,_,reserved⟩ := bytes_whole.2.2.2
  have supported := heapWrite_inventory_supported mixedHeap 0 (.bytes (mixedChild.set 2 0xff))
    (by rfl) StructWordHeap.Controls.support
  exact whole mixedHeap.ty bytesAfter .nil reason mixedPlacement bytesPlacement prior bytes_whole.2.1
    supported mixedReadFrame 0 0 false oldBytes rfl ⟨1,by decide⟩ 0xaa bytesPatch currentReads reserved

theorem actual_prefix_child_halt :
    ((do
      Source.writeLoc mixedReadFrame 0 (.memByte 0 2)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl)
      Source.EM.sub (Source.Locals.nil (D:=mixedLayout)) (do
        Source.writeLoc mixedReadFrame 0 (.memByte 0 1)
          (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xaa] rfl)
        (Source.EM.halt reason : Source.EM mixedEnv [] Unit))) : Source.EM mixedEnv _ (Unit × Source.Locals mixedLayout [])).run mixedState=
      (.error reason,post) := by rfl

theorem nested_empty_contexts :
    (Source.EM.sub (Source.Locals.nil (D:=mixedLayout)) (do
      let _ ← Source.EM.sub (Source.Locals.nil (D:=mixedLayout))
        (Source.writeLoc mixedReadFrame 0 (.memByte 0 1)
          (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xaa] rfl))
      (Source.EM.halt reason : Source.EM mixedEnv [] Unit))).run bytesAfter=(.error reason,post) := by rfl

theorem explicit_rollback_keeps_heap :
    ((do let checkpoint ← Source.mark
         Source.writeLoc mixedReadFrame 0 (.memByte 0 1)
           (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xaa] rfl)
         Source.rollbackTo checkpoint) : Source.EM mixedEnv _ Unit).run bytesAfter=(.ok (),post) :=
  explicit_rollback bytesAfter mixedReadFrame 0 0 false oldBytes rfl ⟨1,by decide⟩ 0xaa

theorem suspended_aliases : post.1=mixedState.1 ∧
    (Source.bytesOfRV mixedReadFrame 0 (.val (post.1.get .here))).run post=(.ok [0x11,0xaa,0xff],post) ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 2)).run post=(.ok (.memRef rfl 0),post) ∧
    post.2.ex=mixedState.2.ex ∧ post.2.logs=mixedState.2.logs := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem exact_patch : patch 160=0x11 ∧ patch 161=0xaa ∧ patch 162=0xff ∧ patch 163=0xa5 ∧
    (mload patch 128).val=3 ∧ patch 1443=0xa5 := by decide

theorem erased_child_write_negative : patch 161≠bytesPatch 161 := by decide

theorem erased_prefix_negative : patch 162≠mixedPhysical 162 := by decide

theorem bounds_failure_after_prefix :
    (Source.EM.sub (Source.Locals.nil (D:=mixedLayout))
      (Source.writeLoc mixedReadFrame 0 (.memByte 0 3)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xaa] rfl))).run bytesAfter=
      (.error (.revert (Source.panicData .index)),bytesAfter) := rfl
end Solidity.Yul.Views.ByteElementFrames.Controls
