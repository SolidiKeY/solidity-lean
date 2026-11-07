import Solidity.Yul.Views.MultiRootByteFrames
import Solidity.Yul.Views.MultiRootByteWritesControls

/-! Distinct nonempty child/caller locals share the actual heap mutation.
The caller's aliases restore on success and halt; one callee run supplies the
physical prefix and unchanged whole caller Source writeback. -/
namespace Solidity.Yul.Views.MultiRootByteFrames.Controls
open Solidity.Yul.Views.Controls
open MultiRootByteWrites
open MultiRootByteWrites.Controls

def child : Source.Locals mixedLayout [.bytes .memory,.string .memory] :=
  .cons (.memRef rfl 5) (.cons (.memRef rfl 1) .nil)

theorem child_OK : Source.LocalsOK mixedEnv mixedHeap.ty child :=
  ⟨⟨.bytes .memory,rfl,rfl⟩,⟨⟨.string .memory,rfl,rfl⟩,trivial⟩⟩

theorem actual_child : coupled mixedReadFrame 0 mixedPlacement.address requests
    (⟨child,mixedState.2⟩ : Source.EMState mixedEnv [.bytes .memory,.string .memory]) mixedPhysical=
    ((.error (.stuck "not bytes"),(child,after.2)),raw) := rfl

theorem caller_frame_whole :
    (Source.EM.sub child (program mixedReadFrame 0 requests)).run mixedState=(.error (.stuck "not bytes"),after) ∧
    (∃ heap,after=withSourceHeap mixedState heap ∧ heap.ty=mixedHeap.ty) ∧ Source.MemOK mixedEnv mixedHeap.ty after ∧
    ∃ q : Placement after.2.heap,
      q.address=mixedPlacement.address ∧ q.free=mixedPlacement.free ∧ encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
      ∃ history : RetainedAllocation mixedPlacement q,
        enumeratedMemoryWriteback after mixedPlacement q history raw=.ok (some (.ok (),after)) ∧ ReservedOK raw q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  have result := sub_physical mixedHeap.ty mixedPlacement mixedReadFrame 0 requests mixedState child child_OK mixedPlacement
    (retainInitial _ _) mixed_actual_MemOK StructWordHeap.Controls.support mixedPhysical ByteElementStore.Controls.oldReads mixed_reserved
  rw [actual_child] at result
  exact result

theorem success_restores_caller :
    (Source.EM.sub child (program mixedReadFrame 0 (requests.take 3))).run mixedState=(.ok ((),child),after) := rfl

theorem suspended_aliases_and_child :
    (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame 0 (.val (after.1.get .here))).run after=(.ok [0x11,0x22,0x55],after) ∧
    (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame 0 (.val (after.1.get (.there .here)))).run after=(.ok [0x11,0x22,0x55],after) ∧
    (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame 0 (.val (child.get .here))).run
      (⟨child,after.2⟩ : Source.EMState mixedEnv [.bytes .memory,.string .memory])=
        (.ok mixedOther,(child,after.2)) ∧
    (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame 0 (.val (child.get (.there .here)))).run
      (⟨child,after.2⟩ : Source.EMState mixedEnv [.bytes .memory,.string .memory])=
        (.ok [0x80,0x61],(child,after.2)) := ⟨rfl,rfl,rfl,rfl⟩

theorem caller_locals_not_child : child.get .here≠after.1.get .here := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro wrong
  cases wrong

theorem actual_source_heap_only :
    ∃ result heap,(program mixedReadFrame 0 requests).run mixedState=(result,withSourceHeap mixedState heap) ∧
      heap.ty=mixedHeap.ty ∧ ∀ a τ d,heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported mixedEnv τ :=
  program_store mixedReadFrame 0 requests mixedState StructWordHeap.Controls.support

theorem prefix_and_unrelated_raw : raw 162=0x55 ∧ raw 416=0x80 ∧ raw 1440=0xee ∧ raw 1443=0xa5 ∧
    after.2.heap.get 2=mixedHeap.get 2 ∧ after.2.ex=mixedState.2.ex ∧ after.2.logs=mixedState.2.logs := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact ⟨by decide,by decide,by decide,by decide,rfl,rfl,rfl⟩
end Solidity.Yul.Views.MultiRootByteFrames.Controls
