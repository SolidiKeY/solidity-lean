import Solidity.Backend.Creation.Linking

/-! Typed immutable patch locations and executable bounds/disjointness checks.
A constructor provides an encoded 32-byte value; this layer neither evaluates
source initializers nor permits postdeployment source writes to an immutable. -/
namespace Solidity.Backend.Creation

/-- Every immutable slot is exactly one encoded stack word (including padding). -/
structure ImmutablePatch (total : Nat) (Key : Type) where
  key : Key
  location : Location total 32
  value : Vector UInt8 32

/-- Bounds are intrinsic to each patch; this checks cross-patch overlap. -/
structure ImmutableTable (total : Nat) (Key : Type) where
  patches : List (ImmutablePatch total Key)
  disjoint : patches.Pairwise (fun p q => p.location.Disjoint q.location)

def checkImmutableTable (patches : List (ImmutablePatch total Key)) : Option (ImmutableTable total Key) :=
  if h : patches.Pairwise (fun p q => p.location.Disjoint q.location) then
    some ⟨patches, h⟩ else none

/-- A raw offset is accepted only after its complete word fits in the runtime. -/
def immutablePatch? (total : Nat) (key : Key) (offset : Nat) (value : Vector UInt8 32) :
    Option (ImmutablePatch total Key) :=
  if h : offset + 32 ≤ total then some ⟨key, ⟨offset, h⟩, value⟩ else none

def patchImmutables (code : List UInt8) (patches : List (ImmutablePatch total Key)) : List UInt8 :=
  patches.foldl (fun bytes p => patchAt bytes p.location.offset p.value.toList) code

theorem patchImmutables_length (patches : List (ImmutablePatch total Key))
    (code : List UInt8) (hc : code.length = total) :
    (patchImmutables code patches).length = total := by
  induction patches generalizing code with
  | nil => exact hc
  | cons p rest ih =>
    have hb : p.location.offset + p.value.toList.length ≤ code.length := by
      rw [Vector.length_toList, hc]; exact p.location.bounds
    exact ih _ (by rw [patchAt_length _ _ _ hb]; exact hc)

/-- No byte outside all certified immutable regions changes. -/
theorem patchImmutables_frame (patches : List (ImmutablePatch total Key))
    (code : List UInt8) (hc : code.length = total) (i : Nat)
    (outside : ∀ p ∈ patches, i < p.location.offset ∨ p.location.offset + 32 ≤ i) :
    (patchImmutables code patches)[i]? = code[i]? := by
  induction patches generalizing code with
  | nil => rfl
  | cons p rest ih =>
    have hb : p.location.offset + p.value.toList.length ≤ code.length := by
      rw [Vector.length_toList, hc]; exact p.location.bounds
    have hp : i < p.location.offset ∨ p.location.offset + p.value.toList.length ≤ i := by
      simpa only [Vector.length_toList] using outside p List.mem_cons_self
    change (patchImmutables (patchAt code p.location.offset p.value.toList) rest)[i]? = code[i]?
    rw [ih _ (by rw [patchAt_length _ _ _ hb]; exact hc)
      (fun q hq => outside q (List.mem_cons_of_mem _ hq))]
    exact patchAt_frame _ _ _ _ hb hp

/-- Every certified patch survives all later disjoint writes, at every byte. -/
theorem patchImmutables_read (patches : List (ImmutablePatch total Key))
    (code : List UInt8) (hc : code.length = total)
    (hd : patches.Pairwise (fun p q => p.location.Disjoint q.location))
    (p : ImmutablePatch total Key) (hp : p ∈ patches) (j : Nat) (hj : j < 32) :
    (patchImmutables code patches)[p.location.offset + j]? = p.value.toList[j]? := by
  induction patches generalizing code with
  | nil => cases hp
  | cons q rest ih =>
    have hb : q.location.offset + q.value.toList.length ≤ code.length := by
      rw [Vector.length_toList, hc]; exact q.location.bounds
    have hc' : (patchAt code q.location.offset q.value.toList).length = total := by
      rw [patchAt_length _ _ _ hb]; exact hc
    rcases List.mem_cons.mp hp with he | hr
    · subst q
      change (patchImmutables (patchAt code p.location.offset p.value.toList) rest)[p.location.offset + j]? = _
      rw [patchImmutables_frame rest _ hc' _ (by
        intro q hq
        have hsep : p.location.Disjoint q.location := (List.pairwise_cons.mp hd).1 q hq
        rcases hsep with hsep | hsep
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))]
      rw [patchAt_get _ _ _ _ hb]
      simp only [Vector.length_toList]
      have hlo : ¬ p.location.offset + j < p.location.offset := by omega
      have hhi : p.location.offset + j < p.location.offset + 32 := by omega
      simp only [hlo, hhi, if_false, if_true, Nat.add_sub_cancel_left]
    · exact ih _ hc' (List.pairwise_cons.mp hd).2 hr

/-- Each exact word, not just its byte count, is preserved in the final runtime. -/
theorem ImmutableTable.read (table : ImmutableTable total Key) (code : List UInt8)
    (hc : code.length = total) (p : ImmutablePatch total Key) (hp : p ∈ table.patches) :
    ((patchImmutables code table.patches).drop p.location.offset).take 32 = p.value.toList := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 32
  · rw [List.getElem?_take_of_lt hj, List.getElem?_drop]
    exact patchImmutables_read _ _ hc table.disjoint p hp j hj
  · have hl : ((patchImmutables code table.patches).drop p.location.offset |>.take 32).length ≤ j := by
      rw [List.length_take]; omega
    rw [List.getElem?_eq_none (by exact hl), List.getElem?_eq_none (by rw [Vector.length_toList]; omega)]

/-- All immutable regions must also avoid all library-address regions. -/
def compatible (table : ImmutableTable total Key) (sites : List (LinkSite total Lib)) : Bool :=
  table.patches.all (fun p => sites.all (fun s => decide (p.location.Disjoint s.location)))

theorem compatible_iff (table : ImmutableTable total Key) (sites : List (LinkSite total Lib)) :
    compatible table sites = true ↔
      ∀ p ∈ table.patches, ∀ s ∈ sites, p.location.Disjoint s.location := by
  simp only [compatible, List.all_eq_true, decide_eq_true_eq]

/-- Combined operation requires a checked cross-table certificate. Keys are
provenance labels; source-level repeated-reference value agreement is separate. -/
def combinedArtifact (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (addresses : Lib → Vector UInt8 20)
    (_compatible : compatible table links.sites = true) : Artifact Lib where
  runtime := patchImmutables (linkBytes a.runtime (localRefs links.sites) addresses) table.patches
  args := a.args
  runtimeFits := by
    rw [patchImmutables_length _ _ (linkSites_length _ _ rfl addresses)]
    exact a.runtimeFits
  linkBase := 0
  runtimeLinks := []

theorem combined_installs (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (addresses : Lib → Vector UInt8 20)
    (h : compatible table links.sites = true) :
    let b := combinedArtifact a links table addresses h
    Exec b.payload b.payload [] [] (.returned b.runtime) := installs_runtime _


def patchedArtifact (a : Artifact Lib) (table : ImmutableTable a.runtime.length Key) : Artifact Lib where
  runtime := patchImmutables a.runtime table.patches
  args := a.args
  runtimeFits := by rw [patchImmutables_length _ _ rfl]; exact a.runtimeFits
  linkBase := a.linkBase
  runtimeLinks := a.runtimeLinks

theorem patched_installs (a : Artifact Lib) (table : ImmutableTable a.runtime.length Key) :
    let b := patchedArtifact a table
    Exec b.payload b.payload [] [] (.returned (patchImmutables a.runtime table.patches)) :=
  installs_runtime _

theorem patched_frame (a : Artifact Lib) (table : ImmutableTable a.runtime.length Key) (i : Nat)
    (outside : ∀ p ∈ table.patches, i < p.location.offset ∨ p.location.offset + 32 ≤ i) :
    (patchedArtifact a table).runtime[i]? = a.runtime[i]? :=
  patchImmutables_frame _ _ rfl i outside

/-- A typed immutable and library reference commute when their complete intervals
are disjoint. This is an encoding fact, not source constructor evaluation. -/
theorem immutable_link_commute (code : List UInt8) (p : ImmutablePatch code.length Key)
    (s : LinkSite code.length Lib) (address : Vector UInt8 20)
    (disjoint : p.location.Disjoint s.location) :
    patchAt (patchAt code p.location.offset p.value.toList) s.location.offset address.toList =
      patchAt (patchAt code s.location.offset address.toList) p.location.offset p.value.toList := by
  apply patchAt_commute
  · simpa only [Vector.length_toList] using p.location.bounds
  · simpa only [Vector.length_toList] using s.location.bounds
  · simpa only [Vector.length_toList] using disjoint

end Solidity.Backend.Creation
