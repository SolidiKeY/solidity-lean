import Solidity.Yul.Views.MultiRootByteWrites
import Solidity.Yul.Views.ByteElementStoreControls

/-! Actual heap lookup selects alternating byte/string roots and preserves
completed prefixes at non-byte, dangling and bounds failures. The raw map has
six objects, real aliases and unrelated nonzero padding. -/
namespace Solidity.Yul.Views.MultiRootByteWrites.Controls
open Solidity.Yul.Views.Controls

def requests : List Request := [(0,2,0xff),(1,0,0x80),(0,2,0x55),(2,0,0x99),(5,0,0xaa)]
def state1 := withSourceHeap mixedState (mixedHeap.write 0 (.bytes [0x11,0x22,0xff]) (by rfl))
def state2 := withSourceHeap state1 (state1.2.heap.write 1 (.string [0x80,0x61]) (by rfl))
def after := withSourceHeap state2 (state2.2.heap.write 0 (.bytes [0x11,0x22,0x55]) (by rfl))
def raw := saveByte (saveByte (saveByte mixedPhysical 162 0xff) 416 0x80) 162 0x55

theorem actual_coupled : coupled mixedReadFrame 0 mixedPlacement.address requests mixedState mixedPhysical=
    ((.error (.stuck "not bytes"),after),raw) := rfl

theorem actual_source : (program mixedReadFrame 0 requests).run mixedState=(.error (.stuck "not bytes"),after) :=
  (source mixedReadFrame 0 mixedPlacement.address requests mixedState mixedPhysical).symm.trans
    (congrArg Prod.fst actual_coupled)

theorem whole_nonbyte_prefix :
    ∃ q : Placement after.2.heap,
      Source.MemOK mixedEnv mixedHeap.ty after ∧ q.address=mixedPlacement.address ∧ q.free=mixedPlacement.free ∧
      encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
      ∃ history : RetainedAllocation mixedPlacement q,
        enumeratedMemoryWriteback after mixedPlacement q history raw=.ok (some (.ok (),after)) ∧ ReservedOK raw q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  have result := sound mixedHeap.ty mixedPlacement mixedReadFrame 0 requests mixedState mixedPlacement (retainInitial _ _)
    mixed_actual_MemOK StructWordHeap.Controls.support mixedPhysical ByteElementStore.Controls.oldReads mixed_reserved
  rw [actual_coupled] at result
  exact result.2

def missingRequests : List Request := [(5,0,0xaa),(99,0,0x77),(0,0,0x42)]
def missingAfter := withSourceHeap mixedState (mixedHeap.write 5 (.bytes [0xaa,0xdd,0xcc]) (by rfl))
def missingRaw := saveByte mixedPhysical 1440 0xaa

theorem actual_missing : coupled mixedReadFrame 0 mixedPlacement.address missingRequests mixedState mixedPhysical=
    ((.error (.stuck "dangling memory reference"),missingAfter),missingRaw) := rfl

theorem whole_missing_prefix :
    ∃ q : Placement missingAfter.2.heap,
      Source.MemOK mixedEnv mixedHeap.ty missingAfter ∧ q.address=mixedPlacement.address ∧ q.free=mixedPlacement.free ∧
      encodeMixedHeap q (generatedHeapEntries q) missingRaw=missingRaw ∧
      ∃ history : RetainedAllocation mixedPlacement q,
        enumeratedMemoryWriteback missingAfter mixedPlacement q history missingRaw=.ok (some (.ok (),missingAfter)) ∧
        ReservedOK missingRaw q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  have result := sound mixedHeap.ty mixedPlacement mixedReadFrame 0 missingRequests mixedState mixedPlacement (retainInitial _ _)
    mixed_actual_MemOK StructWordHeap.Controls.support mixedPhysical ByteElementStore.Controls.oldReads mixed_reserved
  rw [actual_missing] at result
  exact result.2

def boundsRequests : List Request := [(1,1,0x44),(0,3,0x88),(5,0,0xaa)]
def boundsAfter := withSourceHeap mixedState (mixedHeap.write 1 (.string [0xff,0x44]) (by rfl))
def boundsRaw := saveByte mixedPhysical 417 0x44

theorem actual_bounds : coupled mixedReadFrame 0 mixedPlacement.address boundsRequests mixedState mixedPhysical=
    ((.error (.revert (Source.panicData .index)),boundsAfter),boundsRaw) := rfl

theorem actual_aliases :
    (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame 0 (.val (after.1.get .here))).run after=(.ok [0x11,0x22,0x55],after) ∧
    (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame 0 (.val (after.1.get (.there .here)))).run after=(.ok [0x11,0x22,0x55],after) ∧
    (Source.heapBytes (E:=mixedEnv) (Γ:=_) 1).run after=(.ok [0x80,0x61],after) ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 2)).run after=(.ok (.memRef rfl 0),after) ∧
    after.2.ex=mixedState.2.ex ∧ after.2.logs=mixedState.2.logs ∧ after.1=mixedState.1 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem exact_raw_and_negatives : raw 162=0x55 ∧ raw 416=0x80 ∧ (mload raw 672).val=9 ∧ raw 1440=0xee ∧
    raw 163=0xa5 ∧ raw 1443=0xa5 ∧ raw 672≠0x99 ∧ raw 1440≠0xaa ∧ raw 162≠0xff ∧
    missingRaw 160=0x11 ∧ missingRaw 1440=0xaa := by decide

theorem empty_child_context :
    (Source.EM.sub (Source.Locals.nil (D:=mixedLayout)) (program mixedReadFrame 0 requests : Source.EM mixedEnv [] Unit)).run
      mixedState=(.error (.stuck "not bytes"),after) := rfl
end Solidity.Yul.Views.MultiRootByteWrites.Controls
