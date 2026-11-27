import Solidity.Correctness.Lowering.Sim.PassList

/-! A conditional consumer at the concrete Source and intrinsic endpoints. -/
namespace Solidity.Examples.Lowering.Sim

open Solidity.Goals.Shrink.Lowering
open Solidity.Roadmap.G49Final

example (h : Solidity.Goals.loweringBySimulation)
    (F : Solidity.Roadmap.Fixed) (E : Source.Env) (P : Source.SrcProg E)
    (fragment : letI : FreshNames := productionNames; InFragment P) :
    letI : FreshNames := productionNames
    ∃ D : Diagram, ∃ c : Compilation,
      c.Names P ∧ c.Accepted ∧ BodiesBound D P c ∧ Agrees D F P (loweredWorld c) ∧
      ∃ passes : PassList (sourceBehaviour D F P (loweredWorld c))
          (targetBehaviour F (loweredWorld c)),
        passes.fold.envAbs = envAbs ∧
        (∀ e n, passes.fold.need e n = transport D n) ∧
        ∀ e, (targetBehaviour F (loweredWorld c)).Allowed e →
          ∀ n, (sourceBehaviour D F P (loweredWorld c)).Ready (envAbs e) n →
            ((targetBehaviour F (loweredWorld c)).Ready e (transport D n) ∧
              ((sourceBehaviour D F P (loweredWorld c)).observe (envAbs e) n).Le
                ((targetBehaviour F (loweredWorld c)).observe e (transport D n))) ∧
            (∀ rt, (targetBehaviour F (loweredWorld c)).Admissible rt →
              (targetBehaviour F (loweredWorld c)).Guard e rt →
              ∃ rs, (sourceBehaviour D F P (loweredWorld c)).Admissible rs ∧
                (sourceBehaviour D F P (loweredWorld c)).Guard (envAbs e) rs ∧
                ((targetBehaviour F (loweredWorld c)).observe e rt).Le
                  ((sourceBehaviour D F P (loweredWorld c)).observe (envAbs e) rs)) := by
  letI : FreshNames := productionNames
  obtain ⟨D, _, _, _, packaged⟩ :=
    Solidity.Correctness.Lowering.Sim.passList_of_loweringBySimulation h
  obtain ⟨c, names, accepted, bound, agrees, _, passes, _, env, need, _, ends⟩ :=
    packaged F E P fragment
  refine ⟨D, c, names, accepted, bound, agrees, passes, env, need, ?_⟩
  intro e allowed n ready
  have result := ends e allowed n (by simpa only [env] using ready)
  simpa only [env, need] using result

end Solidity.Examples.Lowering.Sim
