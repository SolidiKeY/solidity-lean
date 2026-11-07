import Solidity.Yul.Views.CellHashMemory
import Solidity.Yul.Views.CellWritesCalldataHashControls

/-! A mixed-write/clipped-hash execution has a complete physical allocation:
length header, FMP, payload, nonzero padding and unknown tail. The computed
placement is a mathematical witness, not a claimed target allocator selection. -/
namespace Solidity.Yul.Views.Controls
open TransientSlotControls

def chmCurrent := CellWritesCalldataHash.afterWrites cwhFrame cwhState fcwRequests
def chmPlacement : Placement chmCurrent.2.heap := ComputedPlacement.build _ rfl (by decide)
def chmInput : ByteView := mstore (fun i => if i=191 then 99 else if i=319 then 170 else 0) 64 128
def chmRaw := CellHashMemory.image chmPlacement cwhFrame 1 5 (by decide) chmInput

theorem chm_prepared :
    ComputedAllocationWrite.prepare chmCurrent.2.heap chmPlacement rfl
      (CellHashMemory.data (E:=rootEnv) cwhFrame 1 5) (CellHashMemory.shape cwhFrame 1 5) rfl
      (by decide) chmInput=some chmRaw := rfl

theorem chm_bytes : (mload chmRaw 64).val=192 ∧ (mload chmRaw 128).val=3 ∧
    readBytes chmRaw 160 3=[255,0,128] ∧ chmRaw 191=99 ∧ chmRaw 319=170 := by decide

theorem chm_hash (G : Source.Glob rootEnv) :
    keccak256 G.fixed.evm chmRaw 160 3=G.fixed.hash [255,0,128] :=
  CellHashMemory.image_hash chmPlacement G cwhFrame 1 5 (by decide) chmInput

theorem chm_whole (G : Source.Glob rootEnv) (n : Nat) :
    let q := ComputedAllocationWrite.placement chmCurrent.2.heap chmPlacement rfl
      (CellHashMemory.data (E:=rootEnv) cwhFrame 1 5) (CellHashMemory.shape cwhFrame 1 5) rfl (by decide)
    let after := objectAllocatedState chmCurrent (CellHashMemory.data (E:=rootEnv) cwhFrame 1 5)
    encodeMixedHeap q (generatedHeapEntries q) chmRaw=chmRaw ∧
    enumeratedMemoryWriteback after q q (retainInitial _ _) chmRaw=.ok (some (.ok (),after)) := by
  have oldSupported : ∀ a τ d,chmCurrent.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported rootEnv τ := by
    intro a τ d found
    cases found
  have reads : ∀ e∈generatedHeapEntries chmPlacement,e.image.Reads chmInput (chmPlacement.address e.id) := by
    intro e member
    cases member
  have start : ReservedOK chmInput chmPlacement.free := by
    constructor
    · exact congrArg Fin.val (mload_mstore (fun i=>if i=191 then 99 else if i=319 then 170 else 0) 64 128)
    · intro i
      rw [chmInput,mstore_outside _ _ _ _ (by have hi:=i.isLt;omega)]
      have hi:=i.isLt
      rw [if_neg (by omega),if_neg (by omega)]
  obtain ⟨raw,step,actual,safe,covers,encoded,writeback,reserved⟩ :=
    CellHashMemory.realize G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl chmPlacement rfl
      (by decide) _ cwh_initial_safe chmInput oldSupported reads start
  have same : raw=chmRaw := Option.some.inj (step.symm.trans chm_prepared)
  subst raw
  exact ⟨encoded,writeback⟩
/-- A payload-only copy does not realize the newly allocated length header. -/
theorem chm_not_payload_only :
    mload chmRaw 128≠mload (calldatacopy chmInput cwhFrame.cd 160 1 3) 128 := by decide

theorem chm_observed (G : Source.Glob rootEnv) (n : Nat) :
    (((CellWritesCalldataHash.program G cwhFrame (n+4) .here fcwRequests >>= Source.getV).run cwhState).1.map Source.Val.word)=
      .ok (some (keccak256 G.fixed.evm chmRaw 160 3)) :=
  CellHashMemory.observed G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl chmPlacement (by decide) chmInput
end Solidity.Yul.Views.Controls
