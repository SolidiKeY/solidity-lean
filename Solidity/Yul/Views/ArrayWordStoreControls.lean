import Solidity.Yul.Views.ArrayWordStore
import Solidity.Yul.Views.AllocationPointerControls

/-! The new-reference pointer sink executes an actual raw mstore. The entire
selected array/complement reencodes that same byte map; source aliases observe
the update. Wrong logical-ID and byte-offset stores fail preparation only. -/
namespace Solidity.Yul.Views.ArrayWordStore.Controls
open AllocationPointer.Controls

def prior := mstore
  (bytesObjectView [17] (by decide)
    (bytesObjectView [255,0,128] (by decide) (mstore (fun i=>if i=383 then 99 else 0) 64 288) 128) 192) 256 128

def allocationRaw := byteAllocationView [0,0,0] 288 352 (by decide) prior
def patched := mstore allocationRaw 256 288

theorem allocation_prepared : ComputedAllocationWrite.prepare initial.2.heap p rfl data (.bytes 3) rfl
    (by decide) prior=some allocationRaw := rfl
def old : Fin 1 → Source.Val E.layout (.bytes .memory) := fun _ => .memRef rfl 0
def words : Fin 1 → Roadmap.Word := fun _ => 128

theorem old_encoded (j : Fin 1) : MemoryElement q (old j) (words j) :=
  .pointer rfl 0 (.bytes .memory) rfl rfl

theorem next_encoded : MemoryElement q (Source.Val.memRef (τ:=.bytes .memory) rfl 3) 288 :=
  .pointer rfl 3 (.bytes .memory) rfl rfl

theorem raw_writeback : memberArrayStateWriteback after q (generatedHeapEntries q) 2 (.bytes .memory)
    (some 1) 1 (fun _ equal => (Option.some.inj equal).symm) patched=some (.ok (),written) := by
  have bridge := writeback after q (generatedHeapEntries q)
    (prepareHeapInventory_ok q _ rfl).2.1 F 0 2 (.bytes .memory) (Or.inr (Or.inr rfl))
    (some 1) 1 (fun _ equal => (Option.some.inj equal).symm) old words old_encoded rfl allocationRaw rfl
    (fun j => by have index : j=0 := Fin.ext (by have bound:=j.isLt;omega);subst j;decide)
    ⟨0,by decide⟩ (.memRef rfl 3) 288 next_encoded
  have actual : (Source.writeLoc F 0 (.mem 2 0) (Source.Val.memRef (τ:=.bytes .memory) rfl 3)).run after=(.ok (),written) := rfl
  exact bridge.trans (congrArg some actual)

theorem actual_new_write (G : Source.Glob E) (n : Nat) :
    memberArrayStateWriteback after q (generatedHeapEntries q) 2 (.bytes .memory)
      (some 1) 1 (fun _ equal => (Option.some.inj equal).symm) patched=
        some ((AllocationPointer.writeNew G F (n+1) 0 (τ:=.bytes .memory) rfl (.local .here) rfl 2 0).run initial) := by
  rw [AllocationPointer.Controls.actual_success G n]
  exact raw_writeback

theorem complete_map :
    memberArrayView (some 1) 1 (by decide) (replace words ⟨0,by decide⟩ 288) patched 256=patched := by
  apply reencode (some 1) 1 (by decide) allocationRaw 256 words rfl
    (fun j => by have index : j=0 := Fin.ext (by have bound:=j.isLt;omega);subst j;decide)

theorem exact_bytes : (mload patched 256).val=288 ∧ (mload patched 288).val=3 ∧
    readBytes patched 160 3=[255,0,128] ∧ readBytes patched 320 3=[0,0,0] ∧ patched 383=99 := by decide

theorem wrong_logical_id : memberArrayStateWriteback after q (generatedHeapEntries q) 2 (.bytes .memory)
    (some 1) 1 (fun _ equal => (Option.some.inj equal).symm) (mstore allocationRaw 256 3)=none := rfl

theorem wrong_byte_offset : memberArrayStateWriteback after q (generatedHeapEntries q) 2 (.bytes .memory)
    (some 1) 1 (fun _ equal => (Option.some.inj equal).symm) (mstore allocationRaw 257 288)=none := rfl
def dynamicWords (j : Fin 2) : Roadmap.Word := if j.val=0 then 7 else 9
def dynamicMemory := dynamicUintView 2 (by decide) dynamicWords (fun _ => 99) 128
def dynamicPatched := mstore dynamicMemory 192 42

theorem dynamic_reencode : memberArrayView none 2 (by decide)
    (replace dynamicWords ⟨1,by decide⟩ 42) dynamicPatched 128=dynamicPatched := by
  apply reencode none 2 (by decide) dynamicMemory 128 dynamicWords
    (congrArg Fin.val (dynamicUint_header 2 (by decide) dynamicWords (fun _ => 99) 128))
    (fun j => dynamicUint_element 2 (by decide) dynamicWords (fun _ => 99) 128 j)

theorem dynamic_header_and_residual : (mload dynamicPatched 128).val=2 ∧
    (mload dynamicPatched 160).val=7 ∧ (mload dynamicPatched 192).val=42 ∧ dynamicPatched 256=99 := by decide
end Solidity.Yul.Views.ArrayWordStore.Controls
