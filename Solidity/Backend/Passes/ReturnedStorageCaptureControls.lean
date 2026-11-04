import Solidity.Backend.Passes.ReturnedStorageCapture
import Solidity.Backend.Passes.RelatedStorageCaptureControls

namespace Solidity.Backend.Passes.ReturnedStorageCapture.Controls
open Evm Evm.Compiler Solidity.Lowering.V07
open RelatedStorageCapture.Controls

theorem public_selection : Compiler.compile 0 F program = some checked := rfl

theorem source_run : program.run state =
    .ok ⟨state.push (t := .alias bytesR) (some live),List.prefix_refl _⟩ :=
  storage_capture_run state .here live rfl

def application := readback checked public_selection input (by rfl) source_run live rfl rfl

/-- Complete existing old/new-alias cells plus saved tail remain unchanged. -/
def complete_observation := RelatedStorageCapture.Controls.complete_vector
/-- Choosing the other root and collapsing symbolic slots to numeric zero are
both refuted by the complete existing observation, not a single-cell test. -/
def wrong_root := RelatedStorageCapture.Controls.wrong_alias_refused
def skipped := RelatedStorageCapture.Controls.skipped_capture_refused
def numeric_collapse := RelatedStorageCapture.Controls.numeric_slot_collapse_refused

/-- info: 'Solidity.Backend.Passes.ReturnedStorageCapture.Controls.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms application
end Solidity.Backend.Passes.ReturnedStorageCapture.Controls
