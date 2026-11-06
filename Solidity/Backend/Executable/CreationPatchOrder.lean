import Solidity.Backend.Creation.Immutables

/-! Table-level constructor patch ordering. These are byte-layout and constructor-copy
results; they do not execute the installed runtime or evaluate source initializers. -/
namespace Solidity.Backend.Executable.CreationPatchOrder
open Solidity.Backend Solidity.Backend.Creation

/-- One bounded immutable overwrite commutes past all disjoint library sites. -/
theorem patch_links (code : List UInt8) (hc : code.length = total)
    (p : ImmutablePatch total Key) (sites : List (LinkSite total Lib))
    (addresses : Lib → Vector UInt8 20)
    (hd : ∀ s ∈ sites, p.location.Disjoint s.location) :
    patchAt (linkBytes code (localRefs sites) addresses) p.location.offset p.value.toList =
      linkBytes (patchAt code p.location.offset p.value.toList) (localRefs sites) addresses := by
  induction sites generalizing code with
  | nil => rfl
  | cons s rest ih =>
    have hs : s.location.offset + (addresses s.library).toList.length ≤ code.length := by
      simpa only [Vector.length_toList, hc] using s.location.bounds
    have hp : p.location.offset + p.value.toList.length ≤ code.length := by
      simpa only [Vector.length_toList, hc] using p.location.bounds
    change patchAt (linkBytes (patchAt code s.location.offset (addresses s.library).toList)
      (localRefs rest) addresses) p.location.offset p.value.toList = _
    rw [ih _ (by rw [patchAt_length _ _ _ hs]; exact hc)
      (fun t ht => hd t (List.mem_cons_of_mem _ ht))]
    have comm := patchAt_commute code (addresses s.library).toList p.value.toList
      s.location.offset p.location.offset hs hp (by
        have h := hd s List.mem_cons_self
        simpa only [Location.Disjoint, Vector.length_toList, or_comm] using h)
    rw [comm]
    rfl

/-- The two complete checked tables yield identical runtime bytes in either order. -/
theorem tables (code : List UInt8) (hc : code.length = total)
    (patches : List (ImmutablePatch total Key)) (sites : List (LinkSite total Lib))
    (addresses : Lib → Vector UInt8 20)
    (hd : ∀ p ∈ patches, ∀ s ∈ sites, p.location.Disjoint s.location) :
    patchImmutables (linkBytes code (localRefs sites) addresses) patches =
      linkBytes (patchImmutables code patches) (localRefs sites) addresses := by
  induction patches generalizing code with
  | nil => rfl
  | cons p rest ih =>
    have hp : p.location.offset + p.value.toList.length ≤ code.length := by
      simpa only [Vector.length_toList, hc] using p.location.bounds
    change patchImmutables
      (patchAt (linkBytes code (localRefs sites) addresses) p.location.offset p.value.toList)
      rest = _
    rw [patch_links code hc p sites addresses (hd p List.mem_cons_self)]
    exact ih _ (by rw [patchAt_length _ _ _ hp]; exact hc)
      (fun q hq => hd q (List.mem_cons_of_mem _ hq))

/-- The published constructor returns the same complete runtime when consumers
choose the opposite table order. The compatibility check is discharged, not replaced
by an assumed runtime equality. -/
theorem installs (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (addresses : Lib → Vector UInt8 20)
    (h : compatible table links.sites = true) :
    let b := combinedArtifact a links table addresses h
    Exec b.payload b.payload [] []
      (.returned (linkBytes (patchImmutables a.runtime table.patches)
        (localRefs links.sites) addresses)) := by
  have eq := tables a.runtime rfl table.patches links.sites addresses
    ((compatible_iff table links.sites).mp h)
  simpa only [← eq] using combined_installs a links table addresses h

end Solidity.Backend.Executable.CreationPatchOrder
