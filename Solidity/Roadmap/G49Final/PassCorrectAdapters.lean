import Solidity.Roadmap.G49Final.PassCorrect
import Solidity.Lowering.P8b.Frozen

/-! Exactly one adapter per full-certificate carrier shape. The Cert adapter
is the only semantic implementation; Lowering/Compilation/Execution and P8b
reuse it with their original total-domain and exact output-agreement fields.
No frozen theorem is restated, changed or replaced by an oracle. -/
namespace Solidity.Roadmap.G49Final

/-- Read a typed program's existing language semantics without changing them. -/
def Behaviour.ofLang (L : Lang Event Outcome) (program : L.Prog) : Behaviour where
  Env := L.Env
  Res := L.Res
  resLE := L.resLE
  Allowed := L.Allowed
  Admissible := L.Admissible
  Forward := L.Forward program
  Guard := L.Guard program
  observe := L.sem program
  consistent := L.consistent program

/-- The one full-Cert adapter retains constructive resources, both directions,
environment maps and complete Event/Outcome observations at an exact target. -/
def cert_adapter {A B : Lang Event Outcome} (pass : Pass A B) (certificate : Cert pass)
    (program : A.Prog) (domain : pass.Dom program) (target : B.Prog)
    (agrees : pass.run program domain = target) :
    PassCorrect (Behaviour.ofLang A program) (Behaviour.ofLang B target) where
  envAbs := pass.envAbs
  envSound := certificate.envSound
  envOnto := certificate.envOnto
  need := certificate.need program domain
  need_ok e r allowed source := by
    have transported := certificate.need_ok program domain e r allowed source.1 source.2.1 source.2.2
    rw [agrees] at transported
    exact ⟨⟨transported.1, transported.2.1, transported.2.2.1⟩, transported.2.2.2⟩
  back e r allowed admissible guard := by
    have originalGuard : B.Guard (pass.run program domain) e r := by
      simpa only [agrees] using guard
    have transported := certificate.back program domain e r allowed admissible originalGuard
    simpa only [agrees] using transported

/-- Frozen Lowering carrier: no extra fragment/domain or no-failure premise. -/
def lowering_adapter {S : SourceSpec} {I : IntrinsicSpec} (lowering : Lowering S I)
    (r : S.Resolved) (w : S.WellFormed r) (p : S.InProfile r) (art : Artifact) :
    PassCorrect (Behaviour.ofLang S.lang (S.meaning r w p art))
      (Behaviour.ofLang I.lang (I.ofWorld (lowering.lower r w p art))) :=
  cert_adapter lowering.pass lowering.cert _ (lowering.dom r w p art) _
    (lowering.agrees r w p art)

/-- Frozen Compilation carrier: preserves all worlds, not a selected fragment. -/
def compilation_adapter {I : IntrinsicSpec} {Asm : Lang Event Outcome}
    (backend : Compilation I Asm) (world : I.World) :
    PassCorrect (Behaviour.ofLang I.lang (I.ofWorld world))
      (Behaviour.ofLang Asm (backend.compile world)) :=
  cert_adapter backend.pass backend.cert _ (backend.dom world) _ (backend.agrees world)

/-- Frozen Execution carrier, at the SAME artifact table read by Source. -/
def execution_adapter {Asm : Lang Event Outcome} {V : EvmSpec}
    (execution : Execution Asm V) (program : Asm.Prog) (art : Artifact)
    (artifact : execution.assemble program = art) :
    PassCorrect (Behaviour.ofLang Asm program) (Behaviour.ofLang V.lang (V.load art)) :=
  cert_adapter execution.pass execution.cert _ (execution.dom program) _
    ((execution.agrees program).trans (congrArg V.load artifact))

/-- P8b adds no alternate proof: its frozen inherited Lowering is consumed. -/
def p8b_adapter {A : Solidity.Lowering.P8b.Frozen.SourceInput} {I : IntrinsicSpec}
    (producer : Solidity.Lowering.P8b.Frozen.Producer A I)
    (r : A.source.Resolved) (w : A.source.WellFormed r) (p : A.source.InProfile r) (art : Artifact) :
    PassCorrect (Behaviour.ofLang A.source.lang (A.source.meaning r w p art))
      (Behaviour.ofLang I.lang (I.ofWorld (producer.lower r w p art))) :=
  lowering_adapter producer.toLowering r w p art

/-- One source-boundary package; it is not replicated for later passes. -/
structure SourceProgram (S : SourceSpec) where
  resolved : S.Resolved
  wellFormed : S.WellFormed resolved
  inProfile : S.InProfile resolved

/-- Derive source well-formedness/profile once from the frozen admission
relation, without choosing or fabricating an admitted resolution. -/
def source_from_admitted {S : SourceSpec} (i : S.Input) (r : S.Resolved)
    (admitted : S.Admitted i r) : SourceProgram S := by
  have valid : S.WellFormed r ∧ S.InProfile r := by
    obtain ⟨_, _, _, w, p⟩ := admitted
    exact ⟨w, p⟩
  exact ⟨r, valid.1, valid.2⟩

/-- Establish the single source-end run condition using the existing source
no-failure/hash contracts. This is proved once here, not assumed at each pass.
It does not assert every source execution has no failure or no collision. -/
theorem source_ready {S : SourceSpec} (r : S.Resolved) (w : S.WellFormed r)
    (p : S.InProfile r) (art : Artifact) (e : S.lang.Env) (rs : S.lang.Res)
    (source : S.lang.Admissible rs ∧ S.NoFailure rs ∧
      distinctCount (S.hashed (S.meaning r w p art) e rs) < hashBound ∧
      HashPremise S.fixed (S.hashed (S.meaning r w p art) e rs)
        (S.slotHashed (S.meaning r w p art) e rs)) :
    (Behaviour.ofLang S.lang (S.meaning r w p art)).Ready e rs :=
  ⟨source.1, (S.forward_iff _ e rs).mpr ⟨source.2.1, source.2.2.1⟩,
    (S.guard_iff _ e rs).mpr source.2.2.2⟩

/-- Forget guard/resource transport only at the final boundary. The fold
itself always retains the full stronger constructive witness. -/
theorem PassCorrect.refines {a b : Behaviour} (pass : PassCorrect a b)
    (e : b.Env) (allowed : b.Allowed e) :
    RefinesUnder a.Admissible b.Admissible (a.Forward (pass.envAbs e))
      (a.Guard (pass.envAbs e)) (b.Guard e)
      (a.observe (pass.envAbs e)) (b.observe e) := by
  constructor
  · intro rs ha hf hg
    have output := pass.need_ok e rs allowed ⟨ha, hf, hg⟩
    exact ⟨pass.need e rs, output.1.1, output.2⟩
  · intro rt ha hg
    obtain ⟨rs, hs, _, le⟩ := pass.back e rt allowed ha hg
    exact ⟨rs, hs, le⟩

end Solidity.Roadmap.G49Final
