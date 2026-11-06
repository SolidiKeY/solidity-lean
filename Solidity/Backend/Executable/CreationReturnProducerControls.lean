import Solidity.Backend.Executable.CreationReturnProducer
import Solidity.Backend.Executable.CreationLinkIdentityControls

/-! Inhabited one-site and two-site clients of the complete return observation.
An unused library can change; a referenced one cannot. -/
namespace Solidity.Backend.Executable.CreationReturnProducer.Controls
open Solidity.Backend Solidity.Backend.Creation
open CreationPatchOrder.Controls (artifact imms addresses compatible_tables links s)

def oneArtifact : Artifact Bool := { artifact with runtimeLinks := [(40,false)] }
def oneLinks : LinkTable oneArtifact := ⟨[s],rfl,by decide +kernel⟩
def changedUnused (b : Bool) : Vector UInt8 20 :=
  if b then Vector.replicate 20 99 else addresses false

theorem one_compatible : compatible imms oneLinks.sites = true := by decide +kernel

def first : Artifact Bool := combinedArtifact oneArtifact oneLinks imms addresses one_compatible
def second : Artifact Bool := combinedArtifact oneArtifact oneLinks imms changedUnused one_compatible

theorem first_returns : Exec first.payload first.payload [] [] (.returned first.runtime) :=
  combined_installs oneArtifact oneLinks imms addresses one_compatible

theorem second_returns : Exec second.payload second.payload [] [] (.returned second.runtime) :=
  combined_installs oneArtifact oneLinks imms changedUnused one_compatible

/-- A nonempty runtime with immutable patches and a real referenced address
returns identically despite changing an unreferenced library. -/
theorem unused_same_return : first.runtime = second.runtime := by
  apply (returned_equal_iff oneArtifact oneLinks imms addresses changedUnused
    one_compatible first.runtime second.runtime first_returns second_returns).mpr
  intro site member
  have sameSite : site = s := List.mem_singleton.mp member
  subst site
  rfl

theorem inputs_distinct : addresses true ≠ changedUnused true := by decide +kernel

theorem populated : first.runtime.length = 105 ∧ first.args = [202,254] ∧
    (first.runtime.drop 33).take 20 = (addresses false).toList := by
  exact ⟨by decide +kernel,rfl,
    producer.returned_address oneArtifact oneLinks imms addresses
      one_compatible s List.mem_cons_self first.runtime first_returns⟩

/-- The same complete equivalence rejects the equal-length two-site swap. -/
theorem referenced_difference : ¬ ∀ site ∈ links.sites,
    (addresses site.library).toList =
      (CreationLinkIdentity.Controls.swapped site.library).toList := by
  intro all
  have equal := (runtime_equal_iff artifact links imms addresses
    CreationLinkIdentity.Controls.swapped compatible_tables).mpr all
  exact CreationLinkIdentity.Controls.same_length_distinct_runtime.2
    (equal.symm.trans CreationPatchOrder.Controls.exact_runtime)

end Solidity.Backend.Executable.CreationReturnProducer.Controls
