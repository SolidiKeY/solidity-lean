import Solidity.Yul.Composition.CorrectnessInstances

/-! Conditional G01 public-correctness instance. Every residual field below is
an actual missing environment/deployment/hash/state producer fact, not a supplied
PublicCorrectness or desired execution. Concrete assembly bodies remain inputs. -/
namespace Solidity.Yul.Composition.CorrectnessInstances
open Solidity.Roadmap
section
variable {S : SourceSpec} {I : IntrinsicSpec} {Asm : Lang Event Outcome} {V : EvmSpec}

def Stages.intrinsicEnv (C : Stages S I Asm V) (e : V.lang.Env) : I.lang.Env :=
  C.compilation.pass.envAbs (C.execution.pass.envAbs e)

def Stages.stateExport (C : Stages S I Asm V)
    (decode : List Bytes → V.World → Option I.World) : StateExport S I V where
  lowering := C.lowering
  decode := decode
  envAbs := C.intrinsicEnv

/-- Residual producer obligations: 9 of the 13 `PublicCorrectness` fields pass
through unchanged (only coverage, envOnto, envAbs_agrees and refines are
derived); the control fills this from `toy_publicCorrectness`. No
observation is removed and no target hash premise is replaced by a source one. -/
structure PublicBoundary (C : Stages S I Asm V) (tables : S.Input → Artifact)
    (decode : List Bytes → V.World → Option I.World) : Prop where
  bothPipelines : S.AllPipelines
  fixed : S.fixed = V.fixed
  session : ∀ e, S.session (C.env e) = V.session e
  ifixed : I.fixed = V.fixed
  isession : ∀ e, I.session (C.intrinsicEnv e) = V.session e
  /-- `type(C).creationCode` is what `new C` deploys: every `CREATE` runs the
  table's creation bytes for the contract its event names. -/
  creates_table : ∀ i art, (C.compiler tables) i = some art → art.PrefixFree ∧
    ∀ e rt, V.created (V.load art) e rt =
      (createsOf (V.lang.sem (V.load art) e rt).events).map fun ca => art.initcode ca.1 ++ ca.2
  /-- The bytes hash only preimages the source determines, and address
  storage only by the source's slot preimages (each at some source bound: a
  failing transaction may hash before it fails).  So the compiler cannot
  choose the preimages the EVM's premise reads. -/
  hashes_source : ∀ i r, S.Admitted i r → ∀ (w : S.WellFormed r) (p : S.InProfile r) art,
    (C.compiler tables) i = some art → ∀ e rt, V.lang.Allowed e → V.lang.Admissible rt →
      (∀ b, b ∈ V.hashed (V.load art) e rt →
        ∃ rs, S.lang.Admissible rs ∧ b ∈ S.hashed (S.meaning r w p art) (C.env e) rs) ∧
      ∀ b, b ∈ V.slotHashed (V.load art) e rt →
        ∃ rs, S.lang.Admissible rs ∧ b ∈ S.slotHashed (S.meaning r w p art) (C.env e) rs
  decode_reach : ∀ i r, S.Admitted i r → ∀ (w : S.WellFormed r) (p : S.InProfile r) art,
    (C.compiler tables) i = some art → ∀ e, V.lang.Allowed e → ∀ rt, V.lang.Admissible rt →
      V.lang.Guard (V.load art) e rt →
      ∃ ri, I.lang.Admissible ri ∧
        (V.worlds (V.load art) e rt).map (decode (V.hashed (V.load art) e rt)) =
          (I.worlds (I.ofWorld (C.lowering.lower r w p art)) (C.intrinsicEnv e) ri).map some
  decode_commutes : ∀ i r, S.Admitted i r → ∀ (_ : S.WellFormed r) (_ : S.InProfile r) art,
    (C.compiler tables) i = some art → ∀ e rt, V.lang.Allowed e → V.lang.Admissible rt →
      V.lang.Guard (V.load art) e rt →
      ∀ ω, ω ∈ V.worlds (V.load art) e rt →
      ∀ ω', decode (V.hashed (V.load art) e rt) ω = some ω' →
      ∀ e', V.lang.Allowed e' → (V.session e').balance = V.balances ω →
        I.lang.Allowed (C.intrinsicEnv e') ∧
        RefinesUnder I.lang.Admissible V.lang.Admissible
          (I.lang.Forward (I.ofWorld ω') (C.intrinsicEnv e')) (I.lang.Guard (I.ofWorld ω') (C.intrinsicEnv e'))
          (fun rt' => HashPremise V.fixed
            (V.hashed (V.load art) e rt ++ V.hashed (V.resume ω) e' rt')
            (V.slotHashed (V.load art) e rt ++ V.slotHashed (V.resume ω) e' rt'))
          (I.lang.sem (I.ofWorld ω') (C.intrinsicEnv e')) (V.lang.sem (V.resume ω) e')

/-- Construct G01's actual public record, deriving coverage/environment/refinement
from the stages rather than asking for a PublicCorrectness premise. -/
theorem Stages.publicCorrectness (C : Stages S I Asm V) (tables : S.Input → Artifact)
    (decode : List Bytes → V.World → Option I.World)
    (linked : C.TablesLinked tables) (B : PublicBoundary C tables decode) :
    PublicCorrectness S V (C.compiler tables) C.env (C.stateExport decode) where
  coverage := fun i => C.coverage (tables i) i
  bothPipelines := B.bothPipelines
  envOnto e he := by
    obtain ⟨ei, hei, hi⟩ := C.lowering.cert.envOnto e he
    obtain ⟨ea, hea, ha⟩ := C.compilation.cert.envOnto ei hei
    obtain ⟨ev, hev, hv⟩ := C.execution.cert.envOnto ea hea
    exact ⟨ev, hev, by unfold Stages.env; rw [hv, ha, hi]⟩
  fixed := B.fixed
  session := B.session
  envAbs_agrees := fun _ => rfl
  ifixed := B.ifixed
  isession := B.isession
  creates_table := B.creates_table
  hashes_source := B.hashes_source
  refines := by
    intro i r adm w p art hc e he
    have hc' := C.compile_admitted (tables i) adm w p
    have hemit : C.emit r w p (tables i) = art := Option.some.inj (hc'.symm.trans hc)
    have htable : tables i = art := (linked i r adm w p).symm.trans hemit
    rw [← htable]
    have href := C.refines r w p (tables i) e he
    rw [linked i r adm w p] at href
    exact ⟨C.lowering.cert.envSound _
      (C.compilation.cert.envSound _ (C.execution.cert.envSound e he)), href⟩
  decode_reach := B.decode_reach
  decode_commutes := B.decode_commutes
end
end Solidity.Yul.Composition.CorrectnessInstances
