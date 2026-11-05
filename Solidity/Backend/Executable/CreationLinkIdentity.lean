import Solidity.Backend.Executable.CreationPatchOrder

/-! Library-address observations of actual combined constructor returns.
Only referenced certified sites are recovered. This is byte-layout and the
published creation slice, not account identity or fetched CREATE execution. -/
namespace Solidity.Backend.Executable.CreationLinkIdentity
open Solidity.Backend Solidity.Backend.Creation

theorem sites_frame (code : List UInt8) (hc : code.length = total)
    (sites : List (LinkSite total Lib)) (addresses : Lib → Vector UInt8 20) (i : Nat)
    (outside : ∀ s ∈ sites, i < s.location.offset ∨ s.location.offset + 20 ≤ i) :
    (linkBytes code (localRefs sites) addresses)[i]? = code[i]? := by
  induction sites generalizing code with
  | nil => rfl
  | cons s rest ih =>
    have hb : s.location.offset + (addresses s.library).toList.length ≤ code.length := by
      rw [Vector.length_toList,hc]; exact s.location.bounds
    change (linkBytes (patchAt code s.location.offset (addresses s.library).toList)
      (localRefs rest) addresses)[i]? = _
    rw [ih _ (by rw [patchAt_length _ _ _ hb]; exact hc)
      (fun t ht => outside t (List.mem_cons_of_mem _ ht))]
    exact patchAt_frame _ _ _ _ hb (by
      simpa only [Vector.length_toList] using outside s List.mem_cons_self)

/-- Every byte at a checked library site survives the other disjoint links. -/
theorem sites_read (code : List UInt8) (hc : code.length = total)
    (sites : List (LinkSite total Lib)) (addresses : Lib → Vector UInt8 20)
    (hd : sites.Pairwise (fun s t => s.location.Disjoint t.location))
    (s : LinkSite total Lib) (hs : s ∈ sites) (j : Nat) (hj : j < 20) :
    (linkBytes code (localRefs sites) addresses)[s.location.offset+j]? =
      (addresses s.library).toList[j]? := by
  induction sites generalizing code with
  | nil => cases hs
  | cons t rest ih =>
    have hb : t.location.offset + (addresses t.library).toList.length ≤ code.length := by
      rw [Vector.length_toList,hc]; exact t.location.bounds
    have length : (patchAt code t.location.offset (addresses t.library).toList).length = total := by
      rw [patchAt_length _ _ _ hb]; exact hc
    rcases List.mem_cons.mp hs with same | later
    · subst t
      change (linkBytes (patchAt code s.location.offset (addresses s.library).toList)
        (localRefs rest) addresses)[s.location.offset+j]? = _
      rw [sites_frame _ length rest addresses _ (by
        intro t ht
        have disjoint := (List.pairwise_cons.mp hd).1 t ht
        rcases disjoint with left | right
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))]
      rw [patchAt_get _ _ _ _ hb]
      have lo : ¬s.location.offset+j < s.location.offset := by omega
      have hi : s.location.offset+j < s.location.offset+20 := by omega
      simp only [Vector.length_toList,lo,hi,if_false,if_true,Nat.add_sub_cancel_left]
    · exact ih _ length (List.pairwise_cons.mp hd).2 later

/-- The table-order consumer makes library bytes the final disjoint writes;
no desired linked-runtime equality is a premise. -/
theorem runtime_byte (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (addresses : Lib → Vector UInt8 20)
    (h : compatible table links.sites = true)
    (s : LinkSite a.runtime.length Lib) (hs : s ∈ links.sites) (j : Nat) (hj : j < 20) :
    (combinedArtifact a links table addresses h).runtime[s.location.offset+j]? =
      (addresses s.library).toList[j]? := by
  change (patchImmutables (linkBytes a.runtime (localRefs links.sites) addresses)
    table.patches)[s.location.offset+j]? = _
  rw [CreationPatchOrder.tables a.runtime rfl table.patches links.sites addresses
    ((compatible_iff table links.sites).mp h)]
  exact sites_read _ (patchImmutables_length table.patches a.runtime rfl) links.sites
    addresses links.disjoint s hs j hj

theorem runtime_address (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (addresses : Lib → Vector UInt8 20)
    (h : compatible table links.sites = true)
    (s : LinkSite a.runtime.length Lib) (hs : s ∈ links.sites) :
    ((combinedArtifact a links table addresses h).runtime.drop s.location.offset).take 20 =
      (addresses s.library).toList := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 20
  · rw [List.getElem?_take_of_lt hj,List.getElem?_drop]
    exact runtime_byte a links table addresses h s hs j hj
  · have hl : (((combinedArtifact a links table addresses h).runtime.drop s.location.offset).take 20).length ≤ j := by
      rw [List.length_take]; omega
    rw [List.getElem?_eq_none hl,List.getElem?_eq_none (by rw [Vector.length_toList]; omega)]

/-- Recover the complete address bytes from the actual constructor result. -/
theorem returned_address (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (addresses : Lib → Vector UInt8 20)
    (h : compatible table links.sites = true)
    (s : LinkSite a.runtime.length Lib) (hs : s ∈ links.sites) (output : List UInt8)
    (actual : let b := combinedArtifact a links table addresses h
      Exec b.payload b.payload [] [] (.returned output)) :
    (output.drop s.location.offset).take 20 = (addresses s.library).toList := by
  have same : (combinedArtifact a links table addresses h).runtime = output :=
    Outcome.returned.inj ((combined_installs a links table addresses h).deterministic actual)
  rw [←same]
  exact runtime_address a links table addresses h s hs

/-- Equality of actual returned bytes determines each referenced address.
Unreferenced library identities are deliberately not constrained. -/
theorem same_returns (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (left right : Lib → Vector UInt8 20)
    (h : compatible table links.sites = true)
    (s : LinkSite a.runtime.length Lib) (hs : s ∈ links.sites) (output : List UInt8)
    (first : let b := combinedArtifact a links table left h
      Exec b.payload b.payload [] [] (.returned output))
    (second : let b := combinedArtifact a links table right h
      Exec b.payload b.payload [] [] (.returned output)) :
    (left s.library).toList = (right s.library).toList :=
  (returned_address a links table left h s hs output first).symm.trans
    (returned_address a links table right h s hs output second)

end Solidity.Backend.Executable.CreationLinkIdentity
