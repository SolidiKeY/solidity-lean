import Solidity.Yul.Views.CellHashFinalization
import Solidity.Yul.Views.CellWritesCalldataHashControls

/-! Same reached execution is finalized after interleaved persistent/transient
writes and clipped calldata hashing. Timeout retains the successful write
prefix; explicitly applying endTx then resets its transient cell without
undoing persistence. This is not automatic timeout transaction behavior. -/
namespace Solidity.Yul.Views.Controls
open TransientSlotControls

theorem cwh_final_persistent (G : Source.Glob rootEnv) (n : Nat)
    (residual : ResidualJournal complementCarrierOwnership) :
    let reached := (CellWritesCalldataHash.program G cwhFrame (n+4) .here fcwRequests).run cwhState
    finiteEncode mcsPaths ((CellHashFinalization.finish reached.2 residual).source.world.accounts account).storage
      (packedMask mcsPaths mcsRaw)=some (FiniteCellWrites.raw fcwRequests fcwMaps).1 :=
  CellHashFinalization.persistent_reencode G cwhFrame n cwhState .here 1 5 fcwRequests mcsPaths _
    (selectedSlotPaths_separated _ _ root_separation) rootTempChecked.separated
    fcw_registered fcwMaps ⟨mcs_view,tcu_before⟩ rfl rfl residual

theorem cwh_timeout_final (G : Source.Glob rootEnv)
    (residual : ResidualJournal complementCarrierOwnership) :
    let reached := (CellWritesCalldataHash.program G cwhFrame 3 .here fcwRequests).run cwhState
    let final := CellHashFinalization.finish reached.2 residual
    reached.1=.error .timeout ∧
    (final.source.world.accounts account).storage.read (rootPath "a")=some (Source.intWrap rootU8 3) ∧
    (final.source.transient.cells account).read (rootPath "temp")=some (Source.intWrap unsigned16 0) ∧
    final.source.journal=[] ∧ final.residual.journal=[] := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  rw [CellWritesCalldataHash.low_horizon G cwhFrame 3 cwhState .here fcwRequests rfl (by decide)]
  unfold CellWritesCalldataHash.afterWrites
  rw [FiniteCellWrites.run _ _ _ rfl]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩
end Solidity.Yul.Views.Controls
