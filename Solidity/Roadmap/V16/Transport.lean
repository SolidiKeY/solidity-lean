import Solidity.Roadmap.Contracts

/-!
# V16 independent resource and observation transport

Consequences of the existing G01 certificate, not a compiler certificate.
All forward and hash premises remain explicit. No source, machine or EVM
semantics is defined here.
-/

namespace Solidity.Roadmap.V16

/-- A completed consistent execution stays identical at every larger bound. -/
theorem completed_stable {R E O : Type} [LE R] {p : Prefixes R E O}
    (hc : p.Consistent) {r r' : R} (hr : r ≤ r') {o : O}
    (ho : (p r).final = some o) : p r' = p r :=
  (hc r r' hr).final_eq ho

section Certificate
variable {E O : Type} {L₁ L₂ : Lang E O} {π : Pass L₁ L₂}

/-- Completion is preserved at the certificate-supplied bound, with exact
events and outcome. This lemma adds no choice; computability of the supplied
bound must still be audited for each concrete certificate. -/
theorem completion_at_need (c : Cert π) (p : L₁.Prog) (hd : π.Dom p)
    (e : L₂.Env) (he : L₂.Allowed e) (r : L₁.Res) (ha : L₁.Admissible r)
    (hf : L₁.Forward p (π.envAbs e) r) (hg : L₁.Guard p (π.envAbs e) r)
    {o : O} (ho : (L₁.sem p (π.envAbs e) r).final = some o) :
    L₂.Admissible (c.need p hd e r) ∧
      L₂.sem (π.run p hd) e (c.need p hd e r) = L₁.sem p (π.envAbs e) r := by
  have hn := c.need_ok p hd e r he ha hf hg
  exact ⟨hn.1, hn.2.2.2.final_eq ho⟩

/-- Every event of a source prefix occurs at the certificate-supplied target bound.
This applies also to unfinished prefixes; it asserts neither completion nor
absence of target resource failures. -/
theorem event_at_need (c : Cert π) (p : L₁.Prog) (hd : π.Dom p)
    (e : L₂.Env) (he : L₂.Allowed e) (r : L₁.Res) (ha : L₁.Admissible r)
    (hf : L₁.Forward p (π.envAbs e) r) (hg : L₁.Guard p (π.envAbs e) r)
    {x : E} (hx : x ∈ (L₁.sem p (π.envAbs e) r).events) :
    x ∈ (L₂.sem (π.run p hd) e (c.need p hd e r)).events := by
  have hn := c.need_ok p hd e r he ha hf hg
  exact hn.2.2.2.1.subset hx

/-- Event invariants transport backward through the certificate. The
source invariant ranges over admissible bounds, including failure bounds. -/
theorem event_invariant (c : Cert π) (p : L₁.Prog) (hd : π.Dom p)
    (e : L₂.Env) (he : L₂.Allowed e) (P : E → Prop)
    (hs : ∀ r, L₁.Admissible r → ∀ x, x ∈ (L₁.sem p (π.envAbs e) r).events → P x)
    (r : L₂.Res) (ha : L₂.Admissible r) (hg : L₂.Guard (π.run p hd) e r) :
    ∀ x, x ∈ (L₂.sem (π.run p hd) e r).events → P x := by
  obtain ⟨rs, hrs, _, hp⟩ := c.back p hd e r he ha hg
  intro x hx
  exact hs rs hrs x (hp.1.subset hx)
end Certificate

/-- Decoded reachable-world invariants follow from G01's actual exported
world-list equality. This is conditional on public correctness; it neither
constructs that theorem nor establishes deployment or transaction coverage. -/
theorem decoded_invariant {I : IntrinsicSpec} {S : SourceSpec} {V : EvmSpec}
    {compiler : S.Input → Option Artifact} {envAbs : V.lang.Env → S.lang.Env}
    {X : StateExport S I V} (h : PublicCorrectness S V compiler envAbs X)
    {i : S.Input} {r : S.Resolved} (hadm : S.Admitted i r)
    (w : S.WellFormed r) (p : S.InProfile r) {art : Artifact}
    (hc : compiler i = some art) (e : V.lang.Env) (he : V.lang.Allowed e)
    (rt : V.lang.Res) (hrt : V.lang.Admissible rt) (hg : V.lang.Guard (V.load art) e rt)
    (P : I.World → Prop)
    (hs : ∀ ri, I.lang.Admissible ri → ∀ ω,
      ω ∈ I.worlds (I.ofWorld (X.lowering.lower r w p art)) (X.envAbs e) ri → P ω) :
    ∀ ω, ω ∈ V.worlds (V.load art) e rt →
      ∃ ω', X.decode (V.hashed (V.load art) e rt) ω = some ω' ∧ P ω' := by
  obtain ⟨ri, hri, hmap⟩ := h.decode_reach i r hadm w p art hc e he rt hrt hg
  intro ω hω
  have hm : X.decode (V.hashed (V.load art) e rt) ω ∈
      (I.worlds (I.ofWorld (X.lowering.lower r w p art)) (X.envAbs e) ri).map some := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨ω, hω, rfl⟩
  obtain ⟨ω', hω', heq⟩ := List.mem_map.mp hm
  exact ⟨ω', heq.symm, hs ri hri ω' hω'⟩

end Solidity.Roadmap.V16
