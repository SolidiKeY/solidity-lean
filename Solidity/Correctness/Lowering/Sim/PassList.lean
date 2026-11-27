import Solidity.Goals.LoweringSim
import Solidity.Roadmap.G49Final.PassCorrect

/-! The session lift supplies a one-pass list, conditional on the existing
lowering goal. This does not produce the diagram or prove the lowering goal. -/

namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals.Shrink.Lowering
open Solidity.Roadmap.G49Final

/-- Package the session certificate with its identity tail, retaining the
compilation, boundary agreement, transport and both public refinements. -/
theorem passList_of_loweringBySimulation (h : Solidity.Goals.loweringBySimulation)
    : letI : FreshNames := productionNames
    ∃ D : Diagram, D.Simulates ∧ D.Total ∧ SessionLift D ∧
    ∀ (F : Solidity.Roadmap.Fixed) (E : Source.Env) (P : Source.SrcProg E),
      InFragment P → ∃ c : Compilation,
      c.Names P ∧ c.Accepted ∧ BodiesBound D P c ∧ Agrees D F P (loweredWorld c) ∧
      ∃ pc : PassCorrect (sourceBehaviour D F P (loweredWorld c))
          (targetBehaviour F (loweredWorld c)),
      ∃ passes : PassList (sourceBehaviour D F P (loweredWorld c))
          (targetBehaviour F (loweredWorld c)),
        passes = PassList.cons pc (PassList.nil (targetBehaviour F (loweredWorld c))) ∧
        passes.fold.envAbs = envAbs ∧
        (∀ e n, passes.fold.need e n = transport D n) ∧
        (∀ e, (targetBehaviour F (loweredWorld c)).Allowed e →
          ∀ rt, (targetBehaviour F (loweredWorld c)).Admissible rt →
            (targetBehaviour F (loweredWorld c)).Guard e rt →
            ∃ rs, (sourceBehaviour D F P (loweredWorld c)).Admissible rs ∧
              (sourceBehaviour D F P (loweredWorld c)).Guard (passes.fold.envAbs e) rs ∧
              ((targetBehaviour F (loweredWorld c)).observe e rt).Le
                ((sourceBehaviour D F P (loweredWorld c)).observe (passes.fold.envAbs e) rs)) ∧
        ∀ e, (targetBehaviour F (loweredWorld c)).Allowed e →
          ∀ n, (sourceBehaviour D F P (loweredWorld c)).Ready (passes.fold.envAbs e) n →
            ((targetBehaviour F (loweredWorld c)).Ready e (passes.fold.need e n) ∧
              ((sourceBehaviour D F P (loweredWorld c)).observe (passes.fold.envAbs e) n).Le
                ((targetBehaviour F (loweredWorld c)).observe e (passes.fold.need e n))) ∧
            (∀ rt, (targetBehaviour F (loweredWorld c)).Admissible rt →
              (targetBehaviour F (loweredWorld c)).Guard e rt →
              ∃ rs, (sourceBehaviour D F P (loweredWorld c)).Admissible rs ∧
                (sourceBehaviour D F P (loweredWorld c)).Guard (passes.fold.envAbs e) rs ∧
                ((targetBehaviour F (loweredWorld c)).observe e rt).Le
                  ((sourceBehaviour D F P (loweredWorld c)).observe (passes.fold.envAbs e) rs)) := by
  letI : FreshNames := productionNames
  obtain ⟨_, D, sim, total, lift⟩ := h
  refine ⟨D, sim, total, lift, ?_⟩
  intro F E P fragment
  obtain ⟨c, names, accepted, bound, ⟨⟨pc, env, need⟩, agrees⟩⟩ := lift F E P fragment
  let passes := PassList.cons pc (PassList.nil (targetBehaviour F (loweredWorld c)))
  refine ⟨c, names, accepted, bound, agrees, pc, passes, rfl, ?_, ?_, ?_, ?_⟩
  · exact env
  · exact need
  · exact fun e allowed rt admissible guard => passes.fold.back e rt allowed admissible guard
  · exact fun e allowed n ready => public_end_to_end passes e allowed n ready

end Solidity.Correctness.Lowering.Sim
