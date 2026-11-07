import Solidity.Yul.Views.CellHashFrames
import Solidity.Yul.Views.LinkedCellHashControls

/-! Real repeated mixed-bank writes and clipped hashes run before external
rollback. A second successful hash allocates again, while restoring the
external/residual carriers keeps the caller prefix exactly. Heap rollback and
full call admission are not claimed by these frame laws. -/
namespace Solidity.Yul.Views.Controls
open TransientSlotControls

def chfCaller (G : Source.Glob rootEnv) (n : Nat) :=
  ((CellWritesCalldataHash.program G cwhFrame (n+4) .here fcwRequests).run cwhState).2

def chfChild (G : Source.Glob rootEnv) (n k : Nat) :=
  ((CellWritesCalldataHash.program G cwhFrame (k+4) .here fcwRequests.reverse).run (chfCaller G n)).2

theorem chf_caller_alias (G : Source.Glob rootEnv) (n : Nat) :
    (chfCaller G n).1.get (.there .here)=Source.Val.cdRef rfl 1 5 := by
  rw [chfCaller,CellHashFrames.locals G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl]
  rfl

theorem chf_child_rollback (G : Source.Glob rootEnv) (n k : Nat) :
    companionRollback
      (companionEnter (CellHashFrames.paired (chfCaller G n) lchPrepared)
        cwhFrame.this cwhFrame.sender cwhFrame.value cwhFrame.cd cwhFrame.static)
      (CellHashFrames.paired (chfChild G n k) lchPrepared)=
        CellHashFrames.paired (chfCaller G n) lchPrepared := by
  apply CellHashFrames.child_rollback G cwhFrame k (chfCaller G n) .here 1 5 fcwRequests.reverse rfl
  rw [chfCaller,CellHashFrames.locals G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl]
  rfl

theorem chf_outer_rollback (G : Source.Glob rootEnv) (n k : Nat) :
    companionRollback
      (companionEnter (CellHashFrames.paired cwhState lchPrepared)
        cwhFrame.this cwhFrame.sender cwhFrame.value cwhFrame.cd cwhFrame.static)
      (companionCommit
        (companionEnter (CellHashFrames.paired (chfCaller G n) lchPrepared)
          cwhFrame.this cwhFrame.sender cwhFrame.value cwhFrame.cd cwhFrame.static)
        (CellHashFrames.paired (chfChild G n k) lchPrepared))=
      CellHashFrames.paired cwhState lchPrepared :=
  CellHashFrames.outer_rollback G cwhFrame n k cwhState .here 1 5 fcwRequests fcwRequests.reverse rfl rfl lchPrepared

theorem chf_restored_map (G : Source.Glob rootEnv) (n : Nat) :
    let initial := CellHashFrames.paired cwhState lchPrepared
    let restored := companionRollback
      (companionEnter initial cwhFrame.this cwhFrame.sender cwhFrame.value cwhFrame.cd cwhFrame.static)
      (CellHashFrames.paired (chfCaller G n) lchPrepared)
    finiteEncode mcsPaths (restored.source.world.accounts account).storage
      (fun slot => restored.residual.cells (complementKey false account slot))=some mcsRaw :=
  CellHashFrames.rollback_reencode G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl
    mcsPaths (rootTempRegistry account) (selectedSlotPaths_separated _ _ root_separation)
    fcwMaps mcs_view lchResidual
/-- A committed child really changed the same path; dropping rollback would
leave 2 instead of the caller's 3. Both successful hashes really allocated. -/
theorem chf_not_identity (G : Source.Glob rootEnv) (n k : Nat) :
    ((chfChild G n k).2.ex.world.accounts account).storage.read (rootPath "a")=
      some (Source.intWrap rootU8 2) ∧
    ((chfCaller G n).2.ex.world.accounts account).storage.read (rootPath "a")=
      some (Source.intWrap rootU8 3) ∧ (chfChild G n k).2.heap.next=2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  have retained : (chfCaller G n).1.get (.here : Source.Idx _ (.bytes .calldata))=
      Source.Val.cdRef rfl 1 5 := by
    rw [chfCaller,CellHashFrames.locals G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl]
    rfl
  rw [chfChild,CellWritesCalldataHash.run G cwhFrame k (chfCaller G n) .here 1 5 fcwRequests.reverse rfl retained]
  unfold CellWritesCalldataHash.afterWrites
  rw [FiniteCellWrites.run _ _ _ rfl]
  unfold chfCaller
  rw [CellWritesCalldataHash.run G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl]
  unfold CellWritesCalldataHash.afterWrites
  rw [FiniteCellWrites.run _ _ _ rfl]
  exact ⟨rfl,rfl,rfl⟩
end Solidity.Yul.Views.Controls
