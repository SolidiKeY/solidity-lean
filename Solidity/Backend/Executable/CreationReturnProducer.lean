import Solidity.Backend.Executable.CreationReturnInterfaceV1Controls
import Solidity.Backend.Executable.CreationLinkIdentity

/-! Concrete inhabitant of the frozen kernel-return interface, and complete
referenced-library observations. The relation is finite creation-slice execution,
not Source constructor lowering, account identity or fetched CREATE execution. -/
namespace Solidity.Backend.Executable.CreationReturnProducer
open Solidity.Backend Solidity.Backend.Creation

/-- Discharges both existing laws with their original concrete proofs and a real
nonempty constructor witness. No new admission or preservation field is assumed. -/
def producer : CreationReturnInterfaceV1.Producer where
  witness := CreationReturnInterfaceV1.Controls.witness
  returned_address := CreationLinkIdentity.returned_address
  same_returns := CreationLinkIdentity.same_returns

/-- Unreferenced address-map entries cannot change the patched bytes. This does
not require bounds; bounds/disjointness remain in the typed artifact consumer. -/
theorem link_congr (code : List UInt8) (sites : List (LinkSite total Lib))
    (left right : Lib → Vector UInt8 20)
    (same : ∀ s ∈ sites, (left s.library).toList = (right s.library).toList) :
    linkBytes code (localRefs sites) left = linkBytes code (localRefs sites) right := by
  induction sites generalizing code with
  | nil => rfl
  | cons s rest ih =>
    change linkBytes (patchAt code s.location.offset (left s.library).toList)
      (localRefs rest) left =
      linkBytes (patchAt code s.location.offset (right s.library).toList)
        (localRefs rest) right
    rw [same s List.mem_cons_self]
    exact ih _ (fun t ht => same t (List.mem_cons_of_mem _ ht))

/-- Exact observational domain: all and only referenced library bytes. -/
theorem runtime_equal_iff (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (left right : Lib → Vector UInt8 20)
    (h : compatible table links.sites = true) :
    (combinedArtifact a links table left h).runtime =
      (combinedArtifact a links table right h).runtime ↔
    ∀ s ∈ links.sites, (left s.library).toList = (right s.library).toList := by
  constructor
  · intro equal s hs
    exact (CreationLinkIdentity.runtime_address a links table left h s hs).symm.trans
      ((congrArg (fun bytes : List UInt8 => (bytes.drop s.location.offset).take 20) equal).trans
        (CreationLinkIdentity.runtime_address a links table right h s hs))
  · intro same
    exact congrArg (fun bytes => patchImmutables bytes table.patches)
      (link_congr a.runtime links.sites left right same)

/-- Both outputs come from actual constructor executions. Determinism derives
runtime identity before applying the complete library-observation law. -/
theorem returned_equal_iff (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (left right : Lib → Vector UInt8 20)
    (h : compatible table links.sites = true) (outLeft outRight : List UInt8)
    (first : let b := combinedArtifact a links table left h
      Exec b.payload b.payload [] [] (.returned outLeft))
    (second : let b := combinedArtifact a links table right h
      Exec b.payload b.payload [] [] (.returned outRight)) :
    outLeft = outRight ↔
    ∀ s ∈ links.sites, (left s.library).toList = (right s.library).toList := by
  have hl : (combinedArtifact a links table left h).runtime = outLeft :=
    Outcome.returned.inj ((combined_installs a links table left h).deterministic first)
  have hr : (combinedArtifact a links table right h).runtime = outRight :=
    Outcome.returned.inj ((combined_installs a links table right h).deterministic second)
  rw [← hl,← hr]
  exact runtime_equal_iff a links table left right h

end Solidity.Backend.Executable.CreationReturnProducer
