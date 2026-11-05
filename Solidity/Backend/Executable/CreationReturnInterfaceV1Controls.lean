import Solidity.Backend.Executable.CreationReturnInterfaceV1
import Solidity.Backend.Executable.CreationPatchOrderControls

/-! A real input witness, not an instance of the pending H26 producer. -/
namespace Solidity.Backend.Executable.CreationReturnInterfaceV1.Controls
open Solidity.Backend Solidity.Backend.Creation
open CreationPatchOrder.Controls (artifact links imms addresses compatible_tables s)

def witness : Witness where
  artifact := artifact
  links := links
  table := imms
  addresses := addresses
  compatible := compatible_tables
  site := s
  present := List.mem_cons_self
  runtime_nonempty := by intro h; cases h
  args_nonempty := by intro h; cases h
  immutable_nonempty := by intro h; cases h
  executed := combined_installs artifact links imms addresses compatible_tables

/-- The exact required membership forbids an empty link domain. -/
theorem no_empty_links (w : Witness) : w.links.sites ≠ [] := by
  intro empty
  have member := w.present
  rw [empty] at member
  cases member

/-- The witness executes RETURN, and cannot be relabelled a constructor revert. -/
theorem not_reverted (bytes : List UInt8) :
    let b := combinedArtifact witness.artifact witness.links witness.table
      witness.addresses witness.compatible
    ¬ Exec b.payload b.payload [] [] (.reverted bytes) := by
  dsimp only
  intro bad
  cases witness.executed.deterministic bad

end Solidity.Backend.Executable.CreationReturnInterfaceV1.Controls
