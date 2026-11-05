import Solidity.Backend.Executable.CreationLinkIdentity
import Solidity.Backend.Executable.CreationPatchOrderControls

namespace Solidity.Backend.Executable.CreationLinkIdentity.Controls
open Solidity.Backend Solidity.Backend.Creation
open CreationPatchOrder.Controls (artifact links imms addresses compatible_tables expected s t)

theorem observed_addresses :
    (expected.drop 33).take 20 = (Vector.replicate 20 (51 : UInt8)).toList ∧
    (expected.drop 85).take 20 = (Vector.replicate 20 (68 : UInt8)).toList := by
  exact ⟨returned_address artifact links imms addresses compatible_tables s List.mem_cons_self
      expected CreationPatchOrder.Controls.constructor_returns,
    returned_address artifact links imms addresses compatible_tables t
      (List.mem_cons_of_mem _ List.mem_cons_self) expected CreationPatchOrder.Controls.constructor_returns⟩

def swapped (b : Bool) : Vector UInt8 20 := addresses (!b)
def alternate : Artifact Bool := combinedArtifact artifact links imms swapped compatible_tables

theorem alternate_installs : Exec alternate.payload alternate.payload [] [] (.returned alternate.runtime) :=
  combined_installs artifact links imms swapped compatible_tables

/-- This negative compares equal-length complete runtimes, not just sizes. -/
theorem same_length_distinct_runtime :
    alternate.runtime.length = expected.length ∧ alternate.runtime ≠ expected := by
  constructor
  · first | rfl | decide | omega
  · intro same
    have read := runtime_address artifact links imms swapped compatible_tables s List.mem_cons_self
    change (alternate.runtime.drop 33).take 20 = (Vector.replicate 20 (68 : UInt8)).toList at read
    rw [same,observed_addresses.1] at read
    have different : (Vector.replicate 20 (51 : UInt8)).toList ≠
        (Vector.replicate 20 (68 : UInt8)).toList := by decide
    exact different read

/-- Actual constructor determinism and link recovery exclude the old returned
bytes after swapping the referenced addresses. -/
theorem wrong_link_return : ¬ Exec alternate.payload alternate.payload [] [] (.returned expected) := by
  intro actual
  have bytes := same_returns artifact links imms addresses swapped compatible_tables s List.mem_cons_self
    expected CreationPatchOrder.Controls.constructor_returns actual
  change (Vector.replicate 20 (51 : UInt8)).toList = (Vector.replicate 20 (68 : UInt8)).toList at bytes
  have different : (Vector.replicate 20 (51 : UInt8)).toList ≠
      (Vector.replicate 20 (68 : UInt8)).toList := by decide
  exact different bytes

/-- With no referenced site, even unequal library maps may return the same
empty runtime. The generic recovery theorem requires actual site membership. -/
theorem unreferenced_boundary :
    (combinedArtifact (CreationPatchOrder.Controls.emptyArtifact [202,254])
      (CreationPatchOrder.Controls.emptyLinks [202,254]) CreationPatchOrder.Controls.emptyImms
      addresses rfl).runtime =
    (combinedArtifact (CreationPatchOrder.Controls.emptyArtifact [202,254])
      (CreationPatchOrder.Controls.emptyLinks [202,254]) CreationPatchOrder.Controls.emptyImms
      swapped rfl).runtime ∧ addresses false ≠ swapped false := by
  constructor
  · rfl
  · first | decide | omega

end Solidity.Backend.Executable.CreationLinkIdentity.Controls
