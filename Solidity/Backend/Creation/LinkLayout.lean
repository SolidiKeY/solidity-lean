import Solidity.Backend.Creation.Linking

/-! Bounds and separation derived from the committed assembler's actual metadata. -/
namespace Solidity.Backend.Creation

private def sectionSize (W : Widths L) (items : List (Item L Lib)) : Nat :=
  (items.map (Item.size W)).sum

private theorem refs_bounds (W : Widths L) (link : Lib → Option (Vector UInt8 20))
    (items : List (Item L Lib)) (base : Nat) :
    ∀ r ∈ linkRefsFrom W link base items,
      base ≤ r.1 ∧ r.1 + 20 ≤ base + sectionSize W items := by
  induction items generalizing base with
  | nil => intro r hr; cases hr
  | cons it rest ih =>
    intro r hr
    have htail (ht : r ∈ linkRefsFrom W link (base + it.size W) rest) :
        base ≤ r.1 ∧ r.1 + 20 ≤ base + sectionSize W (it :: rest) := by
      have hb : base + it.size W ≤ r.1 ∧ r.1 + 20 ≤ base + it.size W + sectionSize W rest :=
        ih (base + it.size W) r ht
      simp only [sectionSize, List.map_cons, List.sum_cons]
      unfold sectionSize at hb
      omega
    cases it with
    | instr i => exact htail hr
    | tag l => exact htail hr
    | pushTag l => exact htail hr
    | pushTagRel l => exact htail hr
    | pushLibraryAddress x =>
      change r ∈ (if (link x).isNone then [(base + 1, x)] else []) ++
        linkRefsFrom W link (base + 21) rest at hr
      by_cases hl : (link x).isNone
      · simp only [hl, if_true, List.singleton_append, List.mem_cons] at hr
        rcases hr with he | ht
        · subst r
          simp only [sectionSize, List.map_cons, List.sum_cons, Item.size]
          omega
        · exact htail ht
      · simp only [hl] at hr
        exact htail hr

private theorem refs_separated (W : Widths L) (link : Lib → Option (Vector UInt8 20))
    (items : List (Item L Lib)) (base : Nat) :
    (linkRefsFrom W link base items).Pairwise (fun r s => r.1 + 20 ≤ s.1) := by
  induction items generalizing base with
  | nil => exact List.Pairwise.nil
  | cons it rest ih =>
    cases it with
    | instr i => exact ih _
    | tag l => exact ih _
    | pushTag l => exact ih _
    | pushTagRel l => exact ih _
    | pushLibraryAddress x =>
      change ((if (link x).isNone then [(base + 1, x)] else []) ++
        linkRefsFrom W link (base + 21) rest).Pairwise _
      by_cases hl : (link x).isNone
      · simp only [hl, if_true, List.singleton_append, List.pairwise_cons]
        refine ⟨?_, ih _⟩
        intro t ht
        exact (refs_bounds W link rest (base + 21) t ht).1
      · simpa only [hl, if_false, List.nil_append] using ih (base + 21)

/-- Actual successful assembler metadata is bounded and pairwise disjoint.
The 20-byte address excludes the PUSH20 opcode at the preceding byte. -/
theorem assembler_regions [DecidableEq L] {base : Nat}
    {link : Lib → Option (Vector UInt8 20)} {items : List (Item L Lib)} {out : Assembled Lib}
    (h : assemble base link items = some out) :
    (∀ r ∈ out.linkRefs, base ≤ r.1 ∧ r.1 + 20 ≤ base + (encode out.code).length) ∧
    out.linkRefs.Pairwise (fun r s => r.1 + 20 ≤ s.1) := by
  have hr : out.linkRefs = linkRefsFrom (asmWidths base items) link base items := (assemble_eq h).2.2
  have hsize : (encode out.code).length = sectionSize (asmWidths base items) items := by
    rw [length_encode, (assemble_layout h).2.2]
    simp only [itemOffset, List.take_length, sectionSize]
  rw [hr, hsize]
  exact ⟨refs_bounds _ _ _ _, refs_separated _ _ _ _⟩

/-- Certified table produced from actual base-zero runtime assembly, not a
caller-selected origin. Runtime jump operands stay relative to installed PC zero. -/
def tableOfAssembly [DecidableEq L]
    {link : Lib → Option (Vector UInt8 20)} {items : List (Item L Lib)} {out : Assembled Lib}
    (h : assemble 0 link items = some out) (args : List UInt8)
    (fits : (encode out.code).length < 256 ^ 32) : LinkTable (fromAssembly 0 out args fits) := by
  let bound : ∀ r ∈ out.linkRefs, r.1 + 20 ≤ (encode out.code).length :=
    fun r hr => by simpa only [Nat.zero_add] using (assembler_regions h).1 r hr |>.2
  let site : (r : Nat × Lib) → r.1 + 20 ≤ (encode out.code).length →
      LinkSite (encode out.code).length Lib := fun r hr => ⟨⟨r.1, hr⟩, r.2⟩
  refine ⟨out.linkRefs.pmap site bound, ?_, ?_⟩
  · change out.linkRefs = (out.linkRefs.pmap site bound).map (fun s => (0 + s.location.offset, s.library))
    rw [List.map_pmap]
    simp only [site, Nat.zero_add]
    change out.linkRefs = out.linkRefs.pmap (fun r _ => r) bound
    rw [List.pmap_eq_map, List.map_id']
  · apply (assembler_regions h).2.pmap bound
    intro r hr s hs hsep
    exact Or.inl hsep

theorem Immediate.ext {a b : Immediate} (h : a.value = b.value) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Link the runtime at base zero, then package it. Its wrapper and arguments
are unchanged, and independent execution installs exactly the linked runtime. -/
theorem assembler_link_package [DecidableEq L]
    {link : Lib → Option (Vector UInt8 20)} {items : List (Item L Lib)} {out : Assembled Lib}
    (h : assemble 0 link items = some out) (addresses : Lib → Vector UInt8 20)
    (args : List UInt8) (fits : (encode out.code).length < 256 ^ 32) :
    ∃ out', ∃ fits' : (encode out'.code).length < 256 ^ 32,
      assemble 0 (fillLink link addresses) items = some out' ∧ out'.linkRefs = [] ∧
      let a := fromAssembly 0 out args fits
      let b := fromAssembly 0 out' args fits'
      b.payload = encode (wrapper a.lengthWord) ++ linkBytes a.runtime out.linkRefs addresses ++ args ∧
      Exec b.payload b.payload [] [] (.returned (linkBytes a.runtime out.linkRefs addresses)) := by
  obtain ⟨out', hout, href, hbytes, _, _⟩ := link_patch addresses h
  have hlength : (encode out'.code).length = (encode out.code).length := by
    rw [length_encode, length_encode, (assemble_layout hout).2.2, (assemble_layout h).2.2]
  have fits' : (encode out'.code).length < 256 ^ 32 := by rw [hlength]; exact fits
  have hrt : linkBytes (encode out.code) out.linkRefs addresses = encode out'.code := by
    simpa only [encode_nil, List.nil_append, List.append_nil] using hbytes [] [] rfl
  have hn : (fromAssembly 0 out' args fits').lengthWord = (fromAssembly 0 out args fits).lengthWord :=
    Immediate.ext hlength
  refine ⟨out', fits', hout, href, ?_, ?_⟩
  · change encode (wrapper (fromAssembly 0 out' args fits').lengthWord) ++ encode out'.code ++ args =
      encode (wrapper (fromAssembly 0 out args fits).lengthWord) ++ linkBytes (encode out.code) out.linkRefs addresses ++ args
    rw [hn, hrt]
  · change Exec (fromAssembly 0 out' args fits').payload (fromAssembly 0 out' args fits').payload [] []
      (.returned (linkBytes (encode out.code) out.linkRefs addresses))
    rw [hrt]
    exact installs_runtime _

end Solidity.Backend.Creation
