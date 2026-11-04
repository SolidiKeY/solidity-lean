import Solidity.Semantics.CtxEquiv.Basic

/-!
# Existing correctness notions as contextual refinement (S1.2)

Each correctness notion the repository states over G01's languages is
contextual refinement or equivalence (`Solidity/Semantics/CtxEquiv/Basic.lean`):

- G01's two-sided `Refines` **is** `Below` both ways (`refines_iff`), and its
  premise form `RefinesUnder` is `Below` both ways with the premises as
  counting conditions (`refinesUnder_iff`).  So `CtxEquivOn` of two
  contracts counting their admissible bounds is exactly `Refines` against
  every allowed adversary (`ctxEquivOn_iff_refines`).
- A G01 pass certificate (`Cert`, the O01 pass framework's input) gives
  contextual refinement in both directions under the premises
  (`Cert.ctxRefines_forward`, `Cert.ctxRefines_back`), and equivalence when
  the languages carry no premise (`Cert.ctxEquiv`).
- The public theorem (G49/G50, `PublicCorrectness`) gives, for every
  admitted input and every artifact the compiler produces, contextual
  refinement of the deployed bytes by the source meaning against every G50
  adversary, for the bytes' runs meeting their hash premise
  (`PublicCorrectness.ctxRefines_back`), and of the source's forward runs by
  the bytes (`PublicCorrectness.ctxRefines_forward`); specification transfer
  follows from these alone (`PublicCorrectness.transfer'`), which restates
  `PublicCorrectness.transfer` through contextual refinement.

**Interface stubs.**  O01 (`Solidity/Optimizer/**`) and T07
(`Solidity/SolcValidation/**`) are not on master.  `Preserves` states D6
("every observation except gas values"; gas lives in the resource bound,
not in a `Prefix`) and is `CtxEquivOn` over the language's own environments
(`preserves_iff`); `Validator` states T07's `solc_validated` with the
public theorem's refinement shape, and gives contextual refinement
(`Validator.ctxRefines_back`).  The owning lanes replace these stubs with
their definitions and keep the two lemmas' statements.
-/

namespace Solidity.CtxEquiv

open Solidity.Roadmap

variable {E O : Type}

/-! ## G01 refinement -/

/-- **G01's `Refines` is simulation both ways.** -/
theorem refines_iff {RS RT : Type} (AS : RS → Prop) (AT : RT → Prop) (s : Prefixes RS E O)
    (t : Prefixes RT E O) :
    Refines AS AT s t ↔
      (Behav.ofPrefixes AS s).Below (Behav.ofPrefixes AT t) ∧
        (Behav.ofPrefixes AT t).Below (Behav.ofPrefixes AS s) := by
  constructor
  · rintro ⟨hf, hb⟩
    refine ⟨fun a ⟨rs, hrs, he⟩ => ?_, fun a ⟨rt, hrt, he⟩ => ?_⟩
    · obtain ⟨rt, hrt, hl⟩ := hf rs hrs
      exact ⟨t rt, ⟨rt, hrt, rfl⟩, he ▸ hl⟩
    · obtain ⟨rs, hrs, hl⟩ := hb rt hrt
      exact ⟨s rs, ⟨rs, hrs, rfl⟩, he ▸ hl⟩
  · rintro ⟨hf, hb⟩
    refine ⟨fun rs hrs => ?_, fun rt hrt => ?_⟩
    · obtain ⟨_, ⟨rt, hrt, rfl⟩, hl⟩ := hf (s rs) ⟨rs, hrs, rfl⟩
      exact ⟨rt, hrt, hl⟩
    · obtain ⟨_, ⟨rs, hrs, rfl⟩, hl⟩ := hb (t rt) ⟨rt, hrt, rfl⟩
      exact ⟨rs, hrs, hl⟩

/-- **G01's `RefinesUnder` is simulation both ways, each side counting the
bounds its premise admits.** -/
theorem refinesUnder_iff {RS RT : Type} (AS : RS → Prop) (AT : RT → Prop) (FS GS : RS → Prop)
    (GT : RT → Prop) (s : Prefixes RS E O) (t : Prefixes RT E O) :
    RefinesUnder AS AT FS GS GT s t ↔
      (Behav.ofPrefixes (fun r => AS r ∧ FS r ∧ GS r) s).Below (Behav.ofPrefixes AT t) ∧
        (Behav.ofPrefixes (fun r => AT r ∧ GT r) t).Below (Behav.ofPrefixes AS s) := by
  constructor
  · rintro ⟨hf, hb⟩
    refine ⟨fun a ⟨rs, ⟨hrs, hfs, hgs⟩, he⟩ => ?_, fun a ⟨rt, ⟨hrt, hgt⟩, he⟩ => ?_⟩
    · obtain ⟨rt, hrt, hl⟩ := hf rs hrs hfs hgs
      exact ⟨t rt, ⟨rt, hrt, rfl⟩, he ▸ hl⟩
    · obtain ⟨rs, hrs, hl⟩ := hb rt hrt hgt
      exact ⟨s rs, ⟨rs, hrs, rfl⟩, he ▸ hl⟩
  · rintro ⟨hf, hb⟩
    refine ⟨fun rs hrs hfs hgs => ?_, fun rt hrt hgt => ?_⟩
    · obtain ⟨_, ⟨rt, hrt, rfl⟩, hl⟩ := hf (s rs) ⟨rs, ⟨hrs, hfs, hgs⟩, rfl⟩
      exact ⟨rt, hrt, hl⟩
    · obtain ⟨_, ⟨rs, hrs, rfl⟩, hl⟩ := hb (t rt) ⟨rt, ⟨hrt, hgt⟩, rfl⟩
      exact ⟨rs, hrs, hl⟩

/-- **Contextual equivalence is G01 refinement against every adversary**, for
contracts counting their admissible bounds. -/
theorem ctxEquivOn_iff_refines {A : Type} (Adm : A → Prop) (L₁ L₂ : Lang E O) (p₁ : L₁.Prog)
    (p₂ : L₂.Prog) (env₁ : A → L₁.Env) (env₂ : A → L₂.Env) :
    CtxEquivOn Adm (Deployed.mk' L₁ p₁ env₁) (Deployed.mk' L₂ p₂ env₂) ↔
      ∀ a, Adm a → Refines L₁.Admissible L₂.Admissible (L₁.sem p₁ (env₁ a)) (L₂.sem p₂ (env₂ a)) := by
  constructor
  · intro h a ha
    exact (refines_iff _ _ _ _).2 ⟨h.1 a ha, h.2 a ha⟩
  · intro h
    exact ⟨fun a ha => ((refines_iff _ _ _ _).1 (h a ha)).1,
      fun a ha => ((refines_iff _ _ _ _).1 (h a ha)).2⟩

/-! ## O's D6 relation (stub) -/

/-- **D6 (stub for O01).**  An optimized program preserves every observation
of the original except gas values, in every allowed environment of the
language: G01 refinement at admissible bounds.  Gas values are resource
choices, not part of a `Prefix`, so they are not compared. -/
def Preserves (L : Lang E O) (p q : L.Prog) : Prop :=
  ∀ e, L.Allowed e → Refines L.Admissible L.Admissible (L.sem p e) (L.sem q e)

/-- **D6 is contextual equivalence** over the language's own allowed
environments. -/
theorem preserves_iff (L : Lang E O) (p q : L.Prog) :
    Preserves L p q ↔ CtxEquivOn L.Allowed (Deployed.mk' L p id) (Deployed.mk' L q id) :=
  (ctxEquivOn_iff_refines L.Allowed L L p q id id).symm

end Solidity.CtxEquiv

namespace Solidity.Roadmap

open Solidity.CtxEquiv

variable {E O : Type}

/-! ## Pass certificates (G01, the O01 framework's input) -/

section Cert
variable {A : Type} {L₁ L₂ : Lang E O} {π : Pass L₁ L₂}

/-- The source of a pass, against adversaries read in the target's
environments, counting its forward bounds meeting its premise. -/
def Pass.srcForward (π : Pass L₁ L₂) (p : L₁.Prog) (env : A → L₂.Env) : Deployed A E O :=
  ⟨L₁, p, fun a => π.envAbs (env a),
    fun a r => L₁.Admissible r ∧ L₁.Forward p (π.envAbs (env a)) r ∧ L₁.Guard p (π.envAbs (env a)) r⟩

/-- The source of a pass, counting its admissible bounds. -/
def Pass.src (π : Pass L₁ L₂) (p : L₁.Prog) (env : A → L₂.Env) : Deployed A E O :=
  Deployed.mk' L₁ p fun a => π.envAbs (env a)

/-- The target of a pass at an input in its domain, counting its admissible
bounds. -/
def Pass.tgt (π : Pass L₁ L₂) (p : L₁.Prog) (h : π.Dom p) (env : A → L₂.Env) : Deployed A E O :=
  Deployed.mk' L₂ (π.run p h) env

/-- The target counting only its bounds meeting its premise. -/
def Pass.tgtGuarded (π : Pass L₁ L₂) (p : L₁.Prog) (h : π.Dom p) (env : A → L₂.Env) :
    Deployed A E O :=
  ⟨L₂, π.run p h, env, fun a r => L₂.Admissible r ∧ L₂.Guard (π.run p h) (env a) r⟩

/-- **A certificate gives backward contextual refinement**: everything the
compiled program shows meeting its premise, the source can show. -/
theorem Cert.ctxRefines_back (c : Cert π) (p : L₁.Prog) (h : π.Dom p) {Adm : A → Prop}
    (env : A → L₂.Env) (henv : ∀ a, Adm a → L₂.Allowed (env a)) :
    CtxRefinesOn Adm (π.tgtGuarded p h env) (π.src p env) :=
  fun a ha => ((refinesUnder_iff _ _ _ _ _ _ _).1 (c.refines p h (env a) (henv a ha))).2

/-- **A certificate gives forward contextual refinement (adequacy)**:
everything the source shows at its forward bounds meeting its premise, the
compiled program can show. -/
theorem Cert.ctxRefines_forward (c : Cert π) (p : L₁.Prog) (h : π.Dom p) {Adm : A → Prop}
    (env : A → L₂.Env) (henv : ∀ a, Adm a → L₂.Allowed (env a)) :
    CtxRefinesOn Adm (π.srcForward p env) (π.tgt p h env) :=
  fun a ha => ((refinesUnder_iff _ _ _ _ _ _ _).1 (c.refines p h (env a) (henv a ha))).1

/-- **Without premises a certificate gives contextual equivalence.** -/
theorem Cert.ctxEquiv (c : Cert π) (p : L₁.Prog) (h : π.Dom p) {Adm : A → Prop}
    (env : A → L₂.Env) (henv : ∀ a, Adm a → L₂.Allowed (env a))
    (hS : ∀ e r, L₁.Admissible r → L₁.Forward p e r ∧ L₁.Guard p e r)
    (hT : ∀ e r, L₂.Admissible r → L₂.Guard (π.run p h) e r) :
    CtxEquivOn Adm (π.src p env) (π.tgt p h env) := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · refine Behav.Below.trans ?_ (c.ctxRefines_forward p h env henv a ha)
    exact Behav.Below.of_sub fun _ ⟨r, hr, he⟩ => ⟨r, ⟨hr, hS _ r hr⟩, he⟩
  · refine Behav.Below.trans ?_ (c.ctxRefines_back p h env henv a ha)
    exact Behav.Below.of_sub fun _ ⟨r, hr, he⟩ => ⟨r, ⟨hr, hT _ r hr⟩, he⟩

end Cert

/-- A certified premise-free pass within one language satisfies D6. -/
theorem Cert.preserves {L : Lang E O} {π : Pass L L} (c : Cert π) (p : L.Prog) (h : π.Dom p)
    (hid : ∀ e, π.envAbs e = e)
    (hS : ∀ e r, L.Admissible r → L.Forward p e r ∧ L.Guard p e r)
    (hT : ∀ e r, L.Admissible r → L.Guard (π.run p h) e r) :
    Preserves L p (π.run p h) := by
  have hc := c.ctxEquiv p h (Adm := L.Allowed) id (fun _ h => h) hS hT
  have he : (fun a => π.envAbs (id a)) = (id : L.Env → L.Env) := funext hid
  have : π.src p (id : L.Env → L.Env) = Deployed.mk' L p id := by
    simp only [Pass.src, he]
  rw [this] at hc
  exact (preserves_iff L p (π.run p h)).2 hc

/-! ## The public theorem (G49/G50) -/

/-- A source meaning deployed against G50 adversaries, counting admissible
bounds. -/
def SourceSpec.contract (S : SourceSpec) (p : S.lang.Prog) : Contract :=
  Deployed.mk' S.lang p S.ofSession

/-- The source meaning counting its forward bounds meeting its premise. -/
def SourceSpec.contractForward (S : SourceSpec) (p : S.lang.Prog) : Contract :=
  ⟨S.lang, p, S.ofSession, fun s r => S.lang.Admissible r ∧ S.lang.Forward p (S.ofSession s) r ∧
    S.lang.Guard p (S.ofSession s) r⟩

/-- The deployed bytes against G50 adversaries, counting admissible bounds. -/
def EvmSpec.contract (V : EvmSpec) (art : Artifact) : Contract :=
  Deployed.mk' V.lang (V.load art) V.ofSession

/-- The deployed bytes counting their bounds meeting the hash premise. -/
def EvmSpec.contractGuarded (V : EvmSpec) (art : Artifact) : Contract :=
  ⟨V.lang, V.load art, V.ofSession, fun s r => V.lang.Admissible r ∧
    V.lang.Guard (V.load art) (V.ofSession s) r⟩

theorem EvmSpec.allowed_ofSession (V : EvmSpec) {s : SessionEnv} (hs : s.Allowed) :
    V.lang.Allowed (V.ofSession s) :=
  (V.allowed_iff _).2 (by rw [V.session_of]; exact hs)

end Solidity.Roadmap

namespace Solidity.CtxEquiv

open Solidity.Roadmap

/-- **The refinement shape of the public theorem** for one source meaning and
one artifact: G01 `RefinesUnder` at every allowed EVM environment, the
source reading the same session. -/
def ArtifactRefines (S : SourceSpec) (V : EvmSpec) (m : S.lang.Prog) (art : Artifact) : Prop :=
  ∀ e, V.lang.Allowed e →
    RefinesUnder S.lang.Admissible V.lang.Admissible
      (S.lang.Forward m (S.ofSession (V.session e))) (S.lang.Guard m (S.ofSession (V.session e)))
      (V.lang.Guard (V.load art) e)
      (S.lang.sem m (S.ofSession (V.session e))) (V.lang.sem (V.load art) e)

/-- **Backward contextual refinement from the public shape**: against every G50
adversary, whatever the bytes show meeting their hash premise, the source
can show. -/
theorem ArtifactRefines.ctxRefines_back {S : SourceSpec} {V : EvmSpec} {m : S.lang.Prog}
    {art : Artifact} (h : ArtifactRefines S V m art) :
    CtxRefines (V.contractGuarded art) (S.contract m) := by
  intro s hs
  have hr := h (V.ofSession s) (V.allowed_ofSession hs)
  rw [V.session_of] at hr
  exact ((refinesUnder_iff _ _ _ _ _ _ _).1 hr).2

/-- **Forward contextual refinement (adequacy) from the public shape.** -/
theorem ArtifactRefines.ctxRefines_forward {S : SourceSpec} {V : EvmSpec} {m : S.lang.Prog}
    {art : Artifact} (h : ArtifactRefines S V m art) :
    CtxRefines (S.contractForward m) (V.contract art) := by
  intro s hs
  have hr := h (V.ofSession s) (V.allowed_ofSession hs)
  rw [V.session_of] at hr
  exact ((refinesUnder_iff _ _ _ _ _ _ _).1 hr).1

/-- **Conversely**, the two contextual refinements give the public shape:
the shape is exactly backward and forward contextual refinement. -/
theorem artifactRefines_iff {S : SourceSpec} {V : EvmSpec} {m : S.lang.Prog} {art : Artifact} :
    ArtifactRefines S V m art ↔
      CtxRefines (V.contractGuarded art) (S.contract m) ∧
        CtxRefines (S.contractForward m) (V.contract art) := by
  refine ⟨fun h => ⟨h.ctxRefines_back, h.ctxRefines_forward⟩, fun ⟨hb, hf⟩ e he => ?_⟩
  have hs : (V.session e).Allowed := (V.allowed_iff e).1 he
  have hb' := hb (V.session e) hs
  have hf' := hf (V.session e) hs
  simp only [EvmSpec.contractGuarded, EvmSpec.contract, Deployed.mk', Deployed.behav,
    V.of_session] at hb' hf'
  exact (refinesUnder_iff _ _ _ _ _ _ _).2 ⟨hf', hb'⟩

end Solidity.CtxEquiv

namespace Solidity.Roadmap

open Solidity.CtxEquiv

section Public
variable {I : IntrinsicSpec} {S : SourceSpec} {V : EvmSpec}
  {compiler : S.Input → Option Artifact} {envAbs : V.lang.Env → S.lang.Env}
  {X : StateExport S I V}

/-- The public theorem's refinement field, in the shape `ArtifactRefines`. -/
theorem PublicCorrectness.artifactRefines (h : PublicCorrectness S V compiler envAbs X)
    {i : S.Input} {r : S.Resolved} (adm : S.Admitted i r) (w : S.WellFormed r) (p : S.InProfile r)
    {art : Artifact} (hc : compiler i = some art) :
    ArtifactRefines S V (S.meaning r w p art) art := by
  intro e he
  have hr := (h.refines i r adm w p art hc e he).2
  rw [h.envAbs_eq e] at hr
  exact hr

/-- **G49/G50 as contextual refinement (backward)**: for every admitted input,
against every G50 adversary, the deployed bytes' runs meeting their premise
are runs of the source meaning. -/
theorem PublicCorrectness.ctxRefines_back (h : PublicCorrectness S V compiler envAbs X)
    {i : S.Input} {r : S.Resolved} (adm : S.Admitted i r) (w : S.WellFormed r) (p : S.InProfile r)
    {art : Artifact} (hc : compiler i = some art) :
    CtxRefines (V.contractGuarded art) (S.contract (S.meaning r w p art)) :=
  (h.artifactRefines adm w p hc).ctxRefines_back

/-- **G49/G50 as contextual refinement (forward, resource adequacy).** -/
theorem PublicCorrectness.ctxRefines_forward (h : PublicCorrectness S V compiler envAbs X)
    {i : S.Input} {r : S.Resolved} (adm : S.Admitted i r) (w : S.WellFormed r) (p : S.InProfile r)
    {art : Artifact} (hc : compiler i = some art) :
    CtxRefines (S.contractForward (S.meaning r w p art)) (V.contract art) :=
  (h.artifactRefines adm w p hc).ctxRefines_forward

/-- **Specification transfer through contextual refinement**: the statement of
`PublicCorrectness.transfer`, derived from the two contextual refinements
only. -/
theorem PublicCorrectness.transfer' (h : PublicCorrectness S V compiler envAbs X) :
    SpecTransfer S V compiler envAbs := by
  intro i r adm w p art hc e he
  have hb := h.ctxRefines_back adm w p hc
  have hf := h.ctxRefines_forward adm w p hc
  have hs : (V.session e).Allowed := (V.allowed_iff e).1 he
  rw [h.envAbs_eq e]
  refine ⟨fun Φ down hS rt hrt hg => ?_, fun o ⟨rs, hrs, hfw, hgd, ho⟩ => ?_⟩
  · have := CtxRefinesOn.safety hb Φ down hs (fun r' hr' => hS r' hr') rt
    simp only [EvmSpec.contractGuarded, V.of_session] at this
    exact this ⟨hrt, hg⟩
  · obtain ⟨rt, hrt, he'⟩ := CtxRefinesOn.completes hf hs (r := rs) ⟨hrs, hfw, hgd⟩ ho
    refine ⟨rt, hrt, ?_⟩
    simp only [EvmSpec.contract, SourceSpec.contractForward, Deployed.mk', V.of_session] at he'
    rw [he']
    exact ho

end Public

end Solidity.Roadmap

namespace Solidity.CtxEquiv

open Solidity.Roadmap

/-! ## T07's `solc_validated` (stub) -/

/-- **T07 (stub).**  A validator for solc's artifacts: a successful check
gives the public refinement shape for every admitted resolution of the
input. -/
structure Validator (S : SourceSpec) (V : EvmSpec) where
  validate : S.Input → Artifact → Bool
  sound : ∀ i art, validate i art = true → ∀ r, S.Admitted i r → ∀ (w : S.WellFormed r)
    (p : S.InProfile r), ArtifactRefines S V (S.meaning r w p art) art

/-- **`solc_validated` as contextual refinement**: a validated solc artifact,
against every G50 adversary, shows only what the source can show. -/
theorem Validator.ctxRefines_back {S : SourceSpec} {V : EvmSpec} (T : Validator S V)
    {i : S.Input} {art : Artifact} (hv : T.validate i art = true) {r : S.Resolved}
    (adm : S.Admitted i r) (w : S.WellFormed r) (p : S.InProfile r) :
    CtxRefines (V.contractGuarded art) (S.contract (S.meaning r w p art)) :=
  (T.sound i art hv r adm w p).ctxRefines_back

/-- Validated adequacy. -/
theorem Validator.ctxRefines_forward {S : SourceSpec} {V : EvmSpec} (T : Validator S V)
    {i : S.Input} {art : Artifact} (hv : T.validate i art = true) {r : S.Resolved}
    (adm : S.Admitted i r) (w : S.WellFormed r) (p : S.InProfile r) :
    CtxRefines (S.contractForward (S.meaning r w p art)) (V.contract art) :=
  (T.sound i art hv r adm w p).ctxRefines_forward

end Solidity.CtxEquiv
