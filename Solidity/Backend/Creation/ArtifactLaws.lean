import Solidity.Backend.Creation.LinkLayout

/-! Determinism, encoding/layout uniqueness and disjoint linking permutations. -/
namespace Solidity.Backend.Creation

private abbrev BoundedCode (total : Nat) : Type := { bytes : List UInt8 // bytes.length = total }

private def linkStep (addresses : Lib → Vector UInt8 20)
    (code : BoundedCode total) (site : LinkSite total Lib) : BoundedCode total :=
  ⟨patchAt code.val site.location.offset (addresses site.library).toList, by
    rw [patchAt_length]
    · exact code.property
    · rw [Vector.length_toList, code.property]; exact site.location.bounds⟩

private theorem fold_bytes (sites : List (LinkSite total Lib)) (code : BoundedCode total)
    (addresses : Lib → Vector UInt8 20) :
    (sites.foldl (linkStep addresses) code).val = linkBytes code.val (localRefs sites) addresses := by
  induction sites generalizing code with
  | nil => rfl
  | cons s rest ih => exact ih (linkStep addresses code s)

private theorem separated_members (sites : List (LinkSite total Lib))
    (hd : sites.Pairwise (fun s t => s.location.Disjoint t.location))
    (s t : LinkSite total Lib) (hs : s ∈ sites) (ht : t ∈ sites) :
    s = t ∨ s.location.Disjoint t.location := by
  induction sites with
  | nil => cases hs
  | cons x rest ih =>
    rcases List.mem_cons.mp hs with hsEq | hsTail
    · rcases List.mem_cons.mp ht with htEq | htTail
      · exact Or.inl (hsEq.trans htEq.symm)
      · apply Or.inr
        rw [hsEq]
        exact (List.pairwise_cons.mp hd).1 t htTail
    · rcases List.mem_cons.mp ht with htEq | htTail
      · apply Or.inr
        rw [htEq]
        have hsep : x.location.Disjoint s.location := (List.pairwise_cons.mp hd).1 s hsTail
        exact hsep.symm
      · exact ih (List.pairwise_cons.mp hd).2 hsTail htTail

/-- Any permutation of disjoint address sites produces exactly the same bytes. -/
theorem link_permutation (code : List UInt8) (sites other : List (LinkSite code.length Lib))
    (hd : sites.Pairwise (fun s t => s.location.Disjoint t.location))
    (permutation : sites.Perm other) (addresses : Lib → Vector UInt8 20) :
    linkBytes code (localRefs sites) addresses = linkBytes code (localRefs other) addresses := by
  have hfold : sites.foldl (linkStep addresses) (⟨code, rfl⟩ : BoundedCode code.length) =
      other.foldl (linkStep addresses) (⟨code, rfl⟩ : BoundedCode code.length) := by
    apply permutation.foldl_eq'
    intro s hs t ht state
    rcases separated_members sites hd s t hs ht with he | hsep
    · subst t; rfl
    · apply Subtype.ext
      apply patchAt_commute
      · rw [Vector.length_toList, state.property]; exact s.location.bounds
      · rw [Vector.length_toList, state.property]; exact t.location.bounds
      · simpa only [Vector.length_toList] using hsep
  simpa only [fold_bytes] using congrArg Subtype.val hfold

theorem Artifact.payload_deterministic (a b : Artifact Lib)
    (hr : a.runtime = b.runtime) (ha : a.args = b.args) : a.payload = b.payload := by
  have hn : a.lengthWord = b.lengthWord := Immediate.ext (congrArg List.length hr)
  simp only [Artifact.payload, Artifact.initcode, hn, hr, ha]

theorem Artifact.sections_unique (a b : Artifact Lib) (hlen : a.runtime.length = b.runtime.length)
    (hp : a.payload = b.payload) : a.runtime = b.runtime ∧ a.args = b.args := by
  have hn : a.lengthWord = b.lengthWord := Immediate.ext hlen
  have ho : a.runtimeStart = b.runtimeStart := congrArg runtimeOffset hn
  have ha : a.argsStart = b.argsStart := by
    simp only [Artifact.argsStart, ho, hlen]
  constructor
  · calc
      a.runtime = (a.payload.drop a.runtimeStart).take a.runtime.length := a.runtime_slice.symm
      _ = (b.payload.drop b.runtimeStart).take b.runtime.length := by rw [hp, ho, hlen]
      _ = b.runtime := b.runtime_slice
  · calc
      a.args = a.payload.drop a.argsStart := a.args_slice.symm
      _ = b.payload.drop b.argsStart := by rw [hp, ha]
      _ = b.args := b.args_slice

theorem wrapper_decode (n : Immediate) : decode (encode (wrapper n)) = some (wrapper n) := decode_encode _

end Solidity.Backend.Creation
