import Solidity.Backend.Executable.CreationReturnProducer

/-! Complete byte observations of actual finite constructor RETURN. This is a
consumer of typed linking/immutable tables, not Source provenance or CREATE. -/
namespace Solidity.Backend.Executable.CreationReturnPartition
open Solidity.Backend Solidity.Backend.Creation
variable (a : Artifact Lib) (links : LinkTable a)
  (table : ImmutableTable a.runtime.length Key) (addresses : Lib → Vector UInt8 20)
  (h : compatible table links.sites = true) (output : List UInt8)
  (actual : let b := combinedArtifact a links table addresses h
    Exec b.payload b.payload [] [] (.returned output))

include actual in
theorem immutable (p : ImmutablePatch a.runtime.length Key) (hp : p ∈ table.patches)
    (j : Nat) (hj : j < 32) :
    output[p.location.offset+j]? = p.value.toList[j]? := by
  have same : (combinedArtifact a links table addresses h).runtime = output :=
    Outcome.returned.inj ((combined_installs a links table addresses h).deterministic actual)
  rw [←same]
  exact patchImmutables_read table.patches _ (linkSites_length links.sites a.runtime rfl addresses)
    table.disjoint p hp j hj

include actual in
theorem frame (i : Nat)
    (noImm : ∀ p ∈ table.patches, i < p.location.offset ∨ p.location.offset+32 ≤ i)
    (noLink : ∀ s ∈ links.sites, i < s.location.offset ∨ s.location.offset+20 ≤ i) :
    output[i]? = a.runtime[i]? := by
  have same : (combinedArtifact a links table addresses h).runtime = output :=
    Outcome.returned.inj ((combined_installs a links table addresses h).deterministic actual)
  rw [←same]
  change (patchImmutables (linkBytes a.runtime (localRefs links.sites) addresses) table.patches)[i]? = _
  rw [patchImmutables_frame table.patches _ (linkSites_length links.sites a.runtime rfl addresses) i noImm]
  exact CreationLinkIdentity.sites_frame a.runtime rfl links.sites addresses i noLink

include h in
/-- No immutable byte and referenced library byte can claim the same position. -/
theorem cross_exclusive (p : ImmutablePatch a.runtime.length Key) (hp : p ∈ table.patches)
    (s : LinkSite a.runtime.length Lib) (hs : s ∈ links.sites)
    (j k : Nat) (hj : j < 32) (hk : k < 20) :
    p.location.offset+j ≠ s.location.offset+k := by
  have disjoint := (compatible_iff table links.sites).mp h p hp s hs
  rcases disjoint with left | right <;> omega

include actual in
/-- Every position in the actual output is explained by a certified immutable,
a certified library address, or unchanged input. Outside the runtime the last
alternative compares the actual absent bytes; arguments are never added. -/
theorem partition (i : Nat) :
    (∃ p ∈ table.patches, ∃ j, j < 32 ∧ i = p.location.offset+j ∧
      output[i]? = p.value.toList[j]?) ∨
    (∃ s ∈ links.sites, ∃ j, j < 20 ∧ i = s.location.offset+j ∧
      output[i]? = (addresses s.library).toList[j]?) ∨
    ((∀ p ∈ table.patches, i < p.location.offset ∨ p.location.offset+32 ≤ i) ∧
      (∀ s ∈ links.sites, i < s.location.offset ∨ s.location.offset+20 ≤ i) ∧
      output[i]? = a.runtime[i]?) := by
  classical
  by_cases hi : ∃ p ∈ table.patches, p.location.offset ≤ i ∧ i < p.location.offset+32
  · obtain ⟨p,hp,lo,upper⟩ := hi
    have pos : i = p.location.offset+(i-p.location.offset) := by omega
    refine Or.inl ⟨p,hp,i-p.location.offset,by omega,pos,?_⟩
    exact (congrArg (fun n => output[n]?) pos).trans
      (immutable a links table addresses h output actual p hp (i-p.location.offset) (by omega))
  · by_cases hl : ∃ s ∈ links.sites, s.location.offset ≤ i ∧ i < s.location.offset+20
    · obtain ⟨s,hs,lo,upper⟩ := hl
      have pos : i = s.location.offset+(i-s.location.offset) := by omega
      refine Or.inr (Or.inl ⟨s,hs,i-s.location.offset,by omega,pos,?_⟩)
      have same : (combinedArtifact a links table addresses h).runtime = output :=
        Outcome.returned.inj ((combined_installs a links table addresses h).deterministic actual)
      have read : output[s.location.offset+(i-s.location.offset)]? =
          (addresses s.library).toList[i-s.location.offset]? := by
        rw [←same]
        exact CreationLinkIdentity.runtime_byte a links table addresses h s hs
          (i-s.location.offset) (by omega)
      exact (congrArg (fun n => output[n]?) pos).trans read
    · have noImm : ∀ p ∈ table.patches,
          i < p.location.offset ∨ p.location.offset+32 ≤ i := by
        intro p hp
        by_cases lo : i < p.location.offset
        · exact Or.inl lo
        · right
          apply Nat.le_of_not_gt
          intro upper
          exact hi ⟨p,hp,by omega,by omega⟩
      have noLink : ∀ s ∈ links.sites,
          i < s.location.offset ∨ s.location.offset+20 ≤ i := by
        intro s hs
        by_cases lo : i < s.location.offset
        · exact Or.inl lo
        · right
          apply Nat.le_of_not_gt
          intro upper
          exact hl ⟨s,hs,by omega,by omega⟩
      exact Or.inr (Or.inr ⟨noImm,noLink,
        frame a links table addresses h output actual i noImm noLink⟩)

end Solidity.Backend.Executable.CreationReturnPartition
