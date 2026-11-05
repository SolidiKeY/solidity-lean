import Solidity.Yul.Views.LinkedCellHash
import Solidity.Yul.Views.CellHashFinalizationControls

/-! Computed persistent/transient complements replace only the selected account's
initial journal cells. Unknown persistent slots survive endTx with nonzero full
words; transient cells at the same slot reset. These are seeded kernel controls,
not ABI-entry or compiler correspondence claims. -/
namespace Solidity.Yul.Views.Controls
open TransientSlotControls

def lchResidual : ResidualJournal complementCarrierOwnership := {cells:=fun _ => 99,journal:=[]}
def lchPrepared := LinkedCellHash.prepare account mcsPaths (rootTempRegistry account) fcwMaps lchResidual

theorem lch_unknown_nonzero :
    lchPrepared.cells (complementKey false account 9)=777 ∧
    lchPrepared.cells (complementKey false 2 9)=99 := by decide

theorem lch_final_banks (G : Source.Glob rootEnv) (n : Nat) :
    let reached := (CellWritesCalldataHash.program G cwhFrame (n+4) .here fcwRequests).run cwhState
    let final := CellHashFinalization.finish reached.2 lchPrepared
    final.residual.cells (complementKey false account 9)=777 ∧
    final.residual.cells (complementKey true account 9)=0 ∧
    final.residual.cells (complementKey false 2 9)=99 ∧
    final.residual.cells (complementKey false account 9)≠0 := by
  first | (simp only;done) | decide | omega | rfl | skip
  change lchPrepared.cells (complementKey false account 9)=777 ∧
    (0 : Roadmap.Word)=0 ∧ lchPrepared.cells (complementKey false 2 9)=99 ∧
    lchPrepared.cells (complementKey false account 9)≠0
  decide

theorem lch_reconstructed (G : Source.Glob rootEnv) (n : Nat) :
    let reached := (CellWritesCalldataHash.program G cwhFrame (n+4) .here fcwRequests).run cwhState
    let final := CellHashFinalization.finish reached.2 lchPrepared
    finiteEncode mcsPaths (final.source.world.accounts account).storage
      (fun slot => final.residual.cells (complementKey false account slot))=
        some (FiniteCellWrites.raw fcwRequests fcwMaps).1 :=
  LinkedCellHash.reencode G cwhFrame n cwhState .here 1 5 fcwRequests mcsPaths _
    (selectedSlotPaths_separated _ _ root_separation) rootTempChecked.separated
    fcw_registered fcwMaps ⟨mcs_view,tcu_before⟩ rfl rfl lchResidual
end Solidity.Yul.Views.Controls
