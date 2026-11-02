import Solidity.Roadmap.Contracts

/-! P8b structural adapter over G01 itself. SourceSpec is the explicit typed
input owned by copy-recovery. No SourceSpec, world emitter or simulation is
invented here. A total world emitter is an explicit UNDISCHARGED producer
input; dom/agrees/environment laws do not imply a Cert. -/
namespace Solidity.Lowering.P8b
open Roadmap

/-- Exact image of ALL well-formed in-profile source meanings and artifacts.
No constructor, source fragment, or additional admission predicate is added. -/
def MeaningDomain (S : SourceSpec) (p : S.lang.Prog) : Prop :=
  ∃ (r : S.Resolved) (w : S.WellFormed r) (a : S.InProfile r) (art : Artifact),
    p=S.meaning r w a art

theorem meaning_dom (S : SourceSpec) (r : S.Resolved) (w : S.WellFormed r)
    (a : S.InProfile r) (art : Artifact) : MeaningDomain S (S.meaning r w a art) :=
  ⟨r,w,a,art,rfl⟩

/-- Both actual G01 packages identify their environment with SessionEnv.
The SAME full adversarial session is transported, without filtering callbacks. -/
def environment (S : SourceSpec) (I : IntrinsicSpec) (e : I.lang.Env) : S.lang.Env :=
  S.ofSession (I.session e)

theorem session_exact (S : SourceSpec) (I : IntrinsicSpec) (e : I.lang.Env) :
    S.session (environment S I e)=I.session e := S.session_of _

theorem envSound (S : SourceSpec) (I : IntrinsicSpec) (e : I.lang.Env)
    (allowed : I.lang.Allowed e) : S.lang.Allowed (environment S I e) := by
  apply (S.allowed_iff _).mpr
  rw [session_exact]
  exact (I.allowed_iff _).mp allowed

theorem envOnto (S : SourceSpec) (I : IntrinsicSpec) (e : S.lang.Env)
    (allowed : S.lang.Allowed e) :
    ∃ e', I.lang.Allowed e' ∧ environment S I e'=e := by
  refine ⟨I.ofSession (S.session e),?_,?_⟩
  · apply (I.allowed_iff _).mpr
    rw [I.session_of]
    exact (S.allowed_iff _).mp allowed
  · simp only [environment,I.session_of,S.of_session]

/-- A structural pass for a PROVIDED total, deterministic world emitter.
This does not implement that emitter or supply any semantic certificate.
Resource conversion is deliberately absent, rather than chosen by choice. -/
def pass (S : SourceSpec) (I : IntrinsicSpec) (emit : S.lang.Prog → I.World) :
    Pass S.lang I.lang where
  Dom := MeaningDomain S
  run := fun p _ => I.ofWorld (emit p)
  envAbs := environment S I

def lower (S : SourceSpec) (I : IntrinsicSpec) (emit : S.lang.Prog → I.World)
    (r : S.Resolved) (w : S.WellFormed r) (a : S.InProfile r) (art : Artifact) : I.World :=
  emit (S.meaning r w a art)

theorem dom (S : SourceSpec) (I : IntrinsicSpec) (emit : S.lang.Prog → I.World)
    (r : S.Resolved) (w : S.WellFormed r) (a : S.InProfile r) (art : Artifact) :
    (pass S I emit).Dom (S.meaning r w a art) := meaning_dom S r w a art

theorem agrees (S : SourceSpec) (I : IntrinsicSpec) (emit : S.lang.Prog → I.World)
    (r : S.Resolved) (w : S.WellFormed r) (a : S.InProfile r) (art : Artifact) :
    (pass S I emit).run (S.meaning r w a art) (dom S I emit r w a art)=
      I.ofWorld (lower S I emit r w a art) := rfl

/-- A wrong emitter is refuted by a REAL source completion at a guarded
forward bound. In particular, structural dom/agrees cannot manufacture Cert. -/
theorem no_certificate_of_wrong_completion (S : SourceSpec) (I : IntrinsicSpec)
    (emit : S.lang.Prog → I.World) (r : S.Resolved) (w : S.WellFormed r)
    (a : S.InProfile r) (art : Artifact) (e : I.lang.Env) (rs : S.lang.Res)
    (he : I.lang.Allowed e) (admissible : S.lang.Admissible rs)
    (forward : S.lang.Forward (S.meaning r w a art) (environment S I e) rs)
    (guarded : S.lang.Guard (S.meaning r w a art) (environment S I e) rs)
    (outcome : Outcome)
    (complete : (S.lang.sem (S.meaning r w a art) (environment S I e) rs).final=some outcome)
    (wrong : ∀ rt, I.lang.Admissible rt →
      (I.lang.sem (I.ofWorld (emit (S.meaning r w a art))) e rt).final≠some outcome) :
    ¬ Nonempty (Cert (pass S I emit)) := by
  rintro ⟨c⟩
  obtain ⟨rt,ht,ho,_⟩ := (c.refines (S.meaning r w a art) (dom S I emit r w a art) e he).completes
    admissible forward guarded complete
  exact wrong rt ht ho
/-- Conditional RECORD ASSEMBLY only. The actual semantic certificate must
be delivered separately; this argument is not discharged by dom/agrees.
The wrong-emitter control proves it cannot be filled for an arbitrary emit. -/
def assemble (S : SourceSpec) (I : IntrinsicSpec) (emit : S.lang.Prog → I.World)
    (certificate : Cert (pass S I emit)) : Lowering S I where
  lower := lower S I emit
  pass := pass S I emit
  dom := dom S I emit
  agrees := agrees S I emit
  cert := certificate

/-- Assembly preserves the producer's EXACT bound function. It introduces
no choice, fuel conversion, failure erasure or computability claim. -/
theorem assembled_need (S : SourceSpec) (I : IntrinsicSpec) (emit : S.lang.Prog → I.World)
    (certificate : Cert (pass S I emit)) (p : S.lang.Prog) (hp : MeaningDomain S p)
    (e : I.lang.Env) (r : S.lang.Res) :
    (assemble S I emit certificate).cert.need p hp e r=certificate.need p hp e r := rfl

end Solidity.Lowering.P8b
