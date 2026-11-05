import Solidity.Yul.Views.CellHashRollback
import Solidity.Yul.Views.LinkedCellHashControls

/-! Actual mark/rollbackTo controls distinguish restored external writes from
retained hash allocation, and distinguish a late halt before rollbackTo from
successful execution of rollbackTo. No automatic call/revert policy is asserted. -/
namespace Solidity.Yul.Views.Controls
open TransientSlotControls

theorem chr_actual (G : Source.Glob rootEnv) (n : Nat) :
    let reached := (CellHashRollback.program G cwhFrame (n+4) .here fcwRequests).run cwhState
    reached.2.2.ex=cwhState.2.ex ∧ reached.2.2.logs=cwhState.2.logs ∧
    reached.2.1=cwhState.1 ∧ reached.2.2.heap.next=1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  rw [CellHashRollback.run G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem chr_map (G : Source.Glob rootEnv) (n : Nat) :
    let reached := (CellHashRollback.program G cwhFrame (n+4) .here fcwRequests).run cwhState
    finiteEncode mcsPaths (reached.2.2.ex.world.accounts account).storage
      (fun slot => lchPrepared.cells (complementKey false account slot))=some mcsRaw :=
  CellHashRollback.reconstructed G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl
    mcsPaths (rootTempRegistry account) (selectedSlotPaths_separated _ _ root_separation)
    fcwMaps mcs_view lchResidual

/-- A timeout bypasses the subsequent rollback operation; successful setter
prefixes remain, so treating this wrapper as an unconditional undo is false. -/
theorem chr_timeout_prefix (G : Source.Glob rootEnv) :
    let reached := (CellHashRollback.program G cwhFrame 3 .here fcwRequests).run cwhState
    reached.1=.error .timeout ∧ reached.2.2.heap.next=0 ∧
    (reached.2.2.ex.world.accounts account).storage.read (rootPath "a")=some (Source.intWrap rootU8 3) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  rw [CellHashRollback.low G cwhFrame 3 cwhState .here fcwRequests rfl (by decide)]
  unfold CellWritesCalldataHash.afterWrites
  rw [FiniteCellWrites.run _ _ _ rfl]
  exact ⟨rfl,rfl,rfl⟩
end Solidity.Yul.Views.Controls
