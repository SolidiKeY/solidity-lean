import Solidity.Backend.Executable.CreationPatchOrder

namespace Solidity.Backend.Executable.CreationPatchOrder.Controls
open Solidity.Backend Solidity.Backend.Creation

def artifact : Artifact Bool :=
  ⟨List.replicate 105 0, [202,254], by decide, 7, [(40,false),(92,true)]⟩
def p : ImmutablePatch 105 Bool := ⟨false, ⟨1, by decide⟩, Vector.replicate 32 17⟩
def q : ImmutablePatch 105 Bool := ⟨true, ⟨53, by decide⟩, Vector.replicate 32 34⟩
def s : LinkSite 105 Bool := ⟨⟨33, by decide⟩, false⟩
def t : LinkSite 105 Bool := ⟨⟨85, by decide⟩, true⟩
def imms : ImmutableTable 105 Bool := ⟨[p,q], by decide⟩
def links : LinkTable artifact := ⟨[s,t], rfl, by decide⟩
def addresses (b : Bool) : Vector UInt8 20 := Vector.replicate 20 (if b then 68 else 51)
def expected : List UInt8 := [0] ++ List.replicate 32 17 ++ List.replicate 20 51 ++
  List.replicate 32 34 ++ List.replicate 20 68

theorem compatible_tables : compatible imms links.sites = true := by decide

theorem exact_runtime :
    (combinedArtifact artifact links imms addresses compatible_tables).runtime = expected := by decide

theorem opposite_runtime :
    linkBytes (patchImmutables artifact.runtime imms.patches)
      (localRefs links.sites) addresses = expected := by
  calc
    _ = patchImmutables (linkBytes artifact.runtime (localRefs links.sites) addresses)
      imms.patches := (tables artifact.runtime rfl imms.patches links.sites addresses
        ((compatible_iff imms links.sites).mp compatible_tables)).symm
    _ = expected := exact_runtime

theorem constructor_returns :
    let b := combinedArtifact artifact links imms addresses compatible_tables
    Exec b.payload b.payload [] [] (.returned expected) := by
  simpa only [opposite_runtime] using installs artifact links imms addresses compatible_tables

theorem no_argument_leak :
    (combinedArtifact artifact links imms addresses compatible_tables).runtime ≠ expected ++ artifact.args := by decide

theorem nonzero_prefix_matters : expected ≠ expected.drop 1 := by decide

def overlapping : LinkSite 105 Bool := ⟨⟨2, by decide⟩, false⟩
theorem overlap_refused : compatible imms [overlapping] = false := by decide

def emptyArtifact (args : List UInt8) : Artifact Bool := ⟨[], args, by decide, 0, []⟩
def emptyLinks (args : List UInt8) : LinkTable (emptyArtifact args) := ⟨[], rfl, .nil⟩
def emptyImms : ImmutableTable 0 Bool := ⟨[], .nil⟩
theorem empty_runtime (args : List UInt8) :
    let b := combinedArtifact (emptyArtifact args) (emptyLinks args) emptyImms addresses rfl
    Exec b.payload b.payload [] [] (.returned []) :=
  combined_installs (emptyArtifact args) (emptyLinks args) emptyImms addresses rfl

end Solidity.Backend.Executable.CreationPatchOrder.Controls
