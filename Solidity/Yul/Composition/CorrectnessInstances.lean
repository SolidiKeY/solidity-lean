import Solidity.Roadmap.Contracts

/-!
# Generic three-stage `Stages` composition (no assembly instance)

Executable admission-to-artifact adapter and three-stage certificate transport.
The actual producer contracts are inputs, never assumed axioms. In particular,
`table` is the artifact table the source reads; equating it to emitted bytes is
an explicit linking obligation. This module does not manufacture an assembly
SourceSpec, weaken observations, or assert PublicCorrectness.
-/
namespace Solidity.Yul.Composition.CorrectnessInstances
open Solidity.Roadmap

structure Stages (S : SourceSpec) (I : IntrinsicSpec)
    (Asm : Lang Event Outcome) (V : EvmSpec) where
  admission : Admission S
  lowering : Lowering S I
  compilation : Compilation I Asm
  execution : Execution Asm V

section
variable {S : SourceSpec} {I : IntrinsicSpec} {Asm : Lang Event Outcome} {V : EvmSpec}

/-- The exact registered stage bodies, retaining artifact-table dependence. -/
def Stages.emit (C : Stages S I Asm V) (r : S.Resolved)
    (w : S.WellFormed r) (p : S.InProfile r) (table : Artifact) : Artifact :=
  C.execution.assemble (C.compilation.compile (C.lowering.lower r w p table))

private theorem admitted_wf {i : S.Input} {r : S.Resolved}
    (h : S.Admitted i r) : S.WellFormed r := by
  obtain ⟨_, _, _, hw, _⟩ := h
  exact hw

private theorem admitted_profile {i : S.Input} {r : S.Resolved}
    (h : S.Admitted i r) : S.InProfile r := by
  obtain ⟨_, _, _, _, hp⟩ := h
  exact hp

/-- Computable frontend dispatch. No choice of a resolution or proof oracle. -/
def Stages.compileAt (C : Stages S I Asm V) (table : Artifact)
    (i : S.Input) : Option Artifact :=
  match h : C.admission.frontend i with
  | none => none
  | some r => some (C.emit r (admitted_wf (C.admission.sound i r h))
      (admitted_profile (C.admission.sound i r h)) table)

theorem Stages.compile_admitted (C : Stages S I Asm V) (table : Artifact)
    {i : S.Input} {r : S.Resolved} (h : S.Admitted i r)
    (w : S.WellFormed r) (p : S.InProfile r) :
    C.compileAt table i = some (C.emit r w p table) := by
  unfold Stages.compileAt
  split
  next hn =>
    have hc := C.admission.complete i r h
    rw [hn] at hc
    cases hc
  next r' hr' =>
    have heq : r' = r := Option.some.inj (hr'.symm.trans (C.admission.complete i r h))
    subst r'
    rfl

/-- Exact admission coverage; no residual assembly fragment predicate. -/
theorem Stages.coverage (C : Stages S I Asm V) (table : Artifact) (i : S.Input) :
    (∃ r, S.Admitted i r) ↔ (C.compileAt table i).isSome := by
  constructor
  · rintro ⟨r, h⟩
    rw [C.compile_admitted table h (admitted_wf h) (admitted_profile h)]
    rfl
  · intro h
    unfold Stages.compileAt at h
    split at h
    next hn => cases h
    next r hr => exact ⟨r, C.admission.sound i r hr⟩

def Stages.env (C : Stages S I Asm V) (e : V.lang.Env) : S.lang.Env :=
  C.lowering.pass.envAbs (C.compilation.pass.envAbs (C.execution.pass.envAbs e))

/-- Explicit nested bound supplied by the three actual certificates. -/
def Stages.need (C : Stages S I Asm V) (r : S.Resolved)
    (w : S.WellFormed r) (p : S.InProfile r) (table : Artifact)
    (e : V.lang.Env) (rs : S.lang.Res) : V.lang.Res :=
  C.execution.cert.need (C.compilation.compile (C.lowering.lower r w p table))
    (C.execution.dom _) e
    (C.compilation.cert.need (I.ofWorld (C.lowering.lower r w p table))
      (C.compilation.dom _) (C.execution.pass.envAbs e)
      (C.lowering.cert.need (S.meaning r w p table) (C.lowering.dom r w p table)
        (C.compilation.pass.envAbs (C.execution.pass.envAbs e)) rs))

/-- Full ordered prefix transport, carrying every Forward/Guard premise. -/
theorem Stages.forward (C : Stages S I Asm V) (r : S.Resolved)
    (w : S.WellFormed r) (p : S.InProfile r) (table : Artifact)
    (e : V.lang.Env) (he : V.lang.Allowed e) (rs : S.lang.Res)
    (ha : S.lang.Admissible rs)
    (hf : S.lang.Forward (S.meaning r w p table) (C.env e) rs)
    (hg : S.lang.Guard (S.meaning r w p table) (C.env e) rs) :
    V.lang.Admissible (C.need r w p table e rs) ∧
      V.lang.Guard (V.load (C.emit r w p table)) e (C.need r w p table e rs) ∧
      (S.lang.sem (S.meaning r w p table) (C.env e) rs).Le
        (V.lang.sem (V.load (C.emit r w p table)) e (C.need r w p table e rs)) := by
  have ha₂ := C.execution.cert.envSound e he
  have ha₁ := C.compilation.cert.envSound _ ha₂
  have h₁ := C.lowering.cert.need_ok _ (C.lowering.dom r w p table) _ rs ha₁ ha hf hg
  rw [C.lowering.agrees r w p table] at h₁
  have h₂ := C.compilation.cert.need_ok _ (C.compilation.dom _) _ _ ha₂ h₁.1 h₁.2.1 h₁.2.2.1
  rw [C.compilation.agrees] at h₂
  have h₃ := C.execution.cert.need_ok _ (C.execution.dom _) e _ he h₂.1 h₂.2.1 h₂.2.2.1
  rw [C.execution.agrees] at h₃
  exact ⟨h₃.1, h₃.2.2.1, h₁.2.2.2.trans (h₂.2.2.2.trans h₃.2.2.2)⟩

/-- Success AND failure preserve full bytes and events at the actual bound. -/
theorem Stages.completed (C : Stages S I Asm V) (r : S.Resolved)
    (w : S.WellFormed r) (p : S.InProfile r) (table : Artifact)
    (e : V.lang.Env) (he : V.lang.Allowed e) (rs : S.lang.Res)
    (ha : S.lang.Admissible rs)
    (hf : S.lang.Forward (S.meaning r w p table) (C.env e) rs)
    (hg : S.lang.Guard (S.meaning r w p table) (C.env e) rs)
    {o : Outcome} (ho : (S.lang.sem (S.meaning r w p table) (C.env e) rs).final = some o) :
    V.lang.sem (V.load (C.emit r w p table)) e (C.need r w p table e rs) =
      S.lang.sem (S.meaning r w p table) (C.env e) rs :=
  (C.forward r w p table e he rs ha hf hg).2.2.final_eq ho

/-- Backward execution reflects the entire prefix and its own hash premise. -/
theorem Stages.backward (C : Stages S I Asm V) (r : S.Resolved)
    (w : S.WellFormed r) (p : S.InProfile r) (table : Artifact)
    (e : V.lang.Env) (he : V.lang.Allowed e) (rt : V.lang.Res)
    (ha : V.lang.Admissible rt)
    (hg : V.lang.Guard (V.load (C.emit r w p table)) e rt) :
    ∃ rs, S.lang.Admissible rs ∧
      S.lang.Guard (S.meaning r w p table) (C.env e) rs ∧
      (V.lang.sem (V.load (C.emit r w p table)) e rt).Le
        (S.lang.sem (S.meaning r w p table) (C.env e) rs) := by
  have hg₃ : V.lang.Guard (C.execution.pass.run (C.compilation.compile (C.lowering.lower r w p table))
      (C.execution.dom _)) e rt := by
    rw [C.execution.agrees]
    exact hg
  obtain ⟨r₂, ha₂, hg₂, hp₂⟩ := C.execution.cert.back _ (C.execution.dom _) e rt he ha hg₃
  rw [C.execution.agrees] at hp₂
  have hg₂' : Asm.Guard (C.compilation.pass.run (I.ofWorld (C.lowering.lower r w p table)) (C.compilation.dom _))
      (C.execution.pass.envAbs e) r₂ := by
    rw [C.compilation.agrees]
    exact hg₂
  obtain ⟨r₁, ha₁, hg₁, hp₁⟩ := C.compilation.cert.back _ (C.compilation.dom _) _ r₂
    (C.execution.cert.envSound e he) ha₂ hg₂'
  rw [C.compilation.agrees] at hp₁
  have hg₁' : I.lang.Guard (C.lowering.pass.run (S.meaning r w p table) (C.lowering.dom r w p table))
      (C.compilation.pass.envAbs (C.execution.pass.envAbs e)) r₁ := by
    rw [C.lowering.agrees]
    exact hg₁
  obtain ⟨rs, has, hgs, hps⟩ := C.lowering.cert.back _ (C.lowering.dom r w p table) _ r₁
    (C.compilation.cert.envSound _ (C.execution.cert.envSound e he)) ha₁ hg₁'
  rw [C.lowering.agrees] at hps
  exact ⟨rs, has, hgs, hp₂.trans (hp₁.trans hps)⟩

theorem Stages.refines (C : Stages S I Asm V) (r : S.Resolved)
    (w : S.WellFormed r) (p : S.InProfile r) (table : Artifact)
    (e : V.lang.Env) (he : V.lang.Allowed e) :
    RefinesUnder S.lang.Admissible V.lang.Admissible
      (S.lang.Forward (S.meaning r w p table) (C.env e))
      (S.lang.Guard (S.meaning r w p table) (C.env e))
      (V.lang.Guard (V.load (C.emit r w p table)) e)
      (S.lang.sem (S.meaning r w p table) (C.env e))
      (V.lang.sem (V.load (C.emit r w p table)) e) := by
  constructor
  · intro rs ha hf hg
    have hn := C.forward r w p table e he rs ha hf hg
    exact ⟨_, hn.1, hn.2.2⟩
  · intro rt ha hg
    obtain ⟨rs, has, _, hp⟩ := C.backward r w p table e he rt ha hg
    exact ⟨rs, has, hp⟩

/-- Linking is an actual missing producer obligation, not an implicit fixed point. -/
def Stages.Linked (C : Stages S I Asm V) (r : S.Resolved)
    (w : S.WellFormed r) (p : S.InProfile r) (table : Artifact) : Prop :=
  C.emit r w p table = table

/-- Once a producer proves linking, source meaning reads the emitted table. -/
theorem Stages.linked_compile (C : Stages S I Asm V) (table : Artifact)
    {i : S.Input} {r : S.Resolved} (h : S.Admitted i r)
    (w : S.WellFormed r) (p : S.InProfile r) (hl : C.Linked r w p table) :
    C.compileAt table i = some table := by
  rw [C.compile_admitted table h w p]
  exact congrArg some hl
/-- Whole-input compiler with a supplied linking table generator. No choice or
assumed source execution occurs in the compiler body. -/
def Stages.compiler (C : Stages S I Asm V) (tables : S.Input → Artifact) :
    S.Input → Option Artifact := fun i => C.compileAt (tables i) i

/-- Explicit linking premise required from actual compiler installation. -/
def Stages.TablesLinked (C : Stages S I Asm V) (tables : S.Input → Artifact) : Prop :=
  ∀ i r, S.Admitted i r → ∀ w p, C.Linked r w p (tables i)

/-- G01 specification transfer instantiated from the actual stage certificates.
This is conditional infrastructure; concrete assembly producers still owe the
stage bodies, certificates and artifact-table linking proof. -/
theorem Stages.specTransfer (C : Stages S I Asm V) (tables : S.Input → Artifact)
    (linked : C.TablesLinked tables) : SpecTransfer S V (C.compiler tables) C.env := by
  intro i r adm w p art hc e he
  have hc' := C.compile_admitted (tables i) adm w p
  have hemit : C.emit r w p (tables i) = art := Option.some.inj (hc'.symm.trans hc)
  have htable : tables i = art := (linked i r adm w p).symm.trans hemit
  rw [← htable]
  have href := C.refines r w p (tables i) e he
  rw [linked i r adm w p] at href
  refine ⟨fun Φ down hs => href.safety Φ down hs, ?_⟩
  intro o ⟨rs, ha, hf, hg, ho⟩
  obtain ⟨rt, hrt, hfin, _⟩ := href.completes ha hf hg ho
  exact ⟨rt, hrt, hfin⟩

end
end Solidity.Yul.Composition.CorrectnessInstances
