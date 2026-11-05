import Solidity.Yul.World.CreationReturnWindow
import Solidity.Backend.Executable.CreationReturnInterfaceV1Controls

/-! Reuse the published real nonempty constructor witness. These additional
controls inspect its runtime windows; they do not construct a Producer. -/
namespace Solidity.Yul.World.CreationReturnWindowControls
open Solidity.Backend Solidity.Backend.Creation
open Solidity.Backend.Executable.CreationReturnInterfaceV1
open Solidity.Backend.Executable.CreationPatchOrder.Controls

def runtime := (combinedArtifact artifact links imms addresses compatible_tables).runtime

theorem actual_constructor :
    let b := combinedArtifact artifact links imms addresses compatible_tables
    Exec b.payload b.payload [] [] (.returned runtime) :=
  combined_installs artifact links imms addresses compatible_tables

theorem exact_windows :
    returnWindow runtime 33 20 = some (addresses false).toList ∧
    returnWindow runtime 85 20 = some (addresses true).toList := by
  rw [show runtime=expected from exact_runtime]
  first | decide | rfl | omega

theorem wrong_offset_refused : returnWindow runtime 34 20 ≠ some (addresses false).toList := by
  rw [show runtime=expected from exact_runtime]
  first | decide | rfl | omega

theorem no_argument_window : returnWindow runtime 105 2 = none := by
  rw [show runtime=expected from exact_runtime]
  first | decide | rfl | omega

theorem exact_end_zero : returnWindow runtime 105 0 = some [] := by
  rw [show runtime=expected from exact_runtime]
  first | decide | rfl | omega

theorem out_of_source_zero : returnWindow runtime 106 0 = none := by
  rw [show runtime=expected from exact_runtime]
  first | decide | rfl | omega

def conditional (producer : Producer) := CreationReturnWindow.witnessed producer
end Solidity.Yul.World.CreationReturnWindowControls
