import Solidity.Roadmap.Contracts

/-!
# Frozen G01 certificate-chain backfill

This composes the existing complete Lowering, Compilation and Execution
certificates at the actual lowered world and assembled artifact. All three
packages and the exact artifact equation are named typed inputs. It constructs
none of those producers, supplies no V08 agreement instance, and does not claim
PublicCorrectness, coverage, deployment/state decoding or full G49/G50 closure.
No whole-domain closure premise beyond the frozen producer fields is needed.
-/
namespace Solidity.Roadmap.G49Final

/-- The unchanged three full certificates yield two-sided guarded refinement
with the actual composed environment, source meaning and loaded artifact.
The artifact equation retains source meaning's dependence on its own table. -/
theorem pass_chain {S : SourceSpec} {I : IntrinsicSpec}
    {Asm : Lang Event Outcome} {V : EvmSpec}
    (lowering : Lowering S I) (backend : Compilation I Asm)
    (execution : Execution Asm V)
    (r : S.Resolved) (w : S.WellFormed r) (p : S.InProfile r) (art : Artifact)
    (artifact : execution.assemble (backend.compile (lowering.lower r w p art)) = art)
    (e : V.lang.Env) (allowed : V.lang.Allowed e) :
    S.lang.Allowed (lowering.pass.envAbs (backend.pass.envAbs (execution.pass.envAbs e))) ∧
      RefinesUnder S.lang.Admissible V.lang.Admissible
        (S.lang.Forward (S.meaning r w p art)
          (lowering.pass.envAbs (backend.pass.envAbs (execution.pass.envAbs e))))
        (S.lang.Guard (S.meaning r w p art)
          (lowering.pass.envAbs (backend.pass.envAbs (execution.pass.envAbs e))))
        (V.lang.Guard (V.load art) e)
        (S.lang.sem (S.meaning r w p art)
          (lowering.pass.envAbs (backend.pass.envAbs (execution.pass.envAbs e))))
        (V.lang.sem (V.load art) e) := by
  have asmAllowed : Asm.Allowed (execution.pass.envAbs e) :=
    execution.cert.envSound e allowed
  have intrinsicAllowed : I.lang.Allowed
      (backend.pass.envAbs (execution.pass.envAbs e)) :=
    backend.cert.envSound _ asmAllowed
  refine ⟨lowering.cert.envSound _ intrinsicAllowed, ?_, ?_⟩
  · intro rs admissible forward guard
    have lo := lowering.cert.need_ok (S.meaning r w p art)
      (lowering.dom r w p art) _ rs intrinsicAllowed admissible forward guard
    rw [lowering.agrees r w p art] at lo
    have be := backend.cert.need_ok (I.ofWorld (lowering.lower r w p art))
      (backend.dom _) _ _ asmAllowed lo.1 lo.2.1 lo.2.2.1
    rw [backend.agrees] at be
    have ex := execution.cert.need_ok (backend.compile (lowering.lower r w p art))
      (execution.dom _) e _ allowed be.1 be.2.1 be.2.2.1
    rw [execution.agrees, artifact] at ex
    exact ⟨_, ex.1, lo.2.2.2.trans (be.2.2.2.trans ex.2.2.2)⟩
  · intro rt admissible guard
    have targetGuard : V.lang.Guard
        (execution.pass.run (backend.compile (lowering.lower r w p art))
          (execution.dom _)) e rt := by
      simpa only [execution.agrees, artifact] using guard
    obtain ⟨ra, ha, ga, targetBelow⟩ := execution.cert.back
      (backend.compile (lowering.lower r w p art)) (execution.dom _) e rt
      allowed admissible targetGuard
    rw [execution.agrees, artifact] at targetBelow
    have asmGuard : Asm.Guard
        (backend.pass.run (I.ofWorld (lowering.lower r w p art)) (backend.dom _))
        (execution.pass.envAbs e) ra := by
      simpa only [backend.agrees] using ga
    obtain ⟨ri, hi, gi, asmBelow⟩ := backend.cert.back
      (I.ofWorld (lowering.lower r w p art)) (backend.dom _)
      (execution.pass.envAbs e) ra asmAllowed ha asmGuard
    rw [backend.agrees] at asmBelow
    have intrinsicGuard : I.lang.Guard
        (lowering.pass.run (S.meaning r w p art) (lowering.dom r w p art))
        (backend.pass.envAbs (execution.pass.envAbs e)) ri := by
      simpa only [lowering.agrees] using gi
    obtain ⟨rs, hs, _, intrinsicBelow⟩ := lowering.cert.back
      (S.meaning r w p art) (lowering.dom r w p art)
      (backend.pass.envAbs (execution.pass.envAbs e)) ri intrinsicAllowed hi intrinsicGuard
    rw [lowering.agrees] at intrinsicBelow
    exact ⟨rs, hs, targetBelow.trans (asmBelow.trans intrinsicBelow)⟩

end Solidity.Roadmap.G49Final
