import Solidity.Yul.Views.RetainedAliasSubSafety
import Solidity.Yul.Views.RetainedAliasSubControls

/-! Caller safety is derived from the original caller invariant, independently
of callee context size. Dormant saved references remain statically well typed;
no historical index event or current ancestor bound is fabricated. -/
namespace Solidity.Yul.Views.Controls

theorem rass_success (pipeline : Roadmap.Pipeline) :
    Source.MemOK agEnv agState.2.heap.ty
      (RetainedAliasSub.execute (raoPlan pipeline) (rasSuccessPlan pipeline) raState.1).1.2 :=
  RetainedAliasSubSafety.MemOK _ _ _ _ ra_initial_safe

theorem rass_late_static (pipeline : Roadmap.Pipeline) :
    Source.MemOK agEnv agState.2.heap.ty
      (RetainedAliasSub.execute (raoPlan pipeline) (rasPlan pipeline) raState.1).1.2 :=
  RetainedAliasSubSafety.MemOK _ _ _ _ ra_initial_safe

theorem rass_first_static (pipeline : Roadmap.Pipeline) :
    Source.MemOK agEnv agState.2.heap.ty
      (RetainedAliasSub.execute (raoStaticPlan pipeline) (rasSkipPlan pipeline) raState.1).1.2 :=
  RetainedAliasSubSafety.MemOK _ _ _ _ ra_initial_safe

/-- Caller and callee contexts need not have the same shape or size. -/
theorem rass_empty (pipeline : Roadmap.Pipeline) :
    Source.MemOK agEnv agState.2.heap.ty
      (RetainedAliasSub.execute (raoPlan pipeline) (rasSuccessPlan pipeline) Source.Locals.nil).1.2 := by
  apply RetainedAliasSubSafety.MemOK
  exact ⟨⟨ra_initial_safe.1.1,True.intro⟩,ra_initial_safe.2⟩

theorem rass_heap (pipeline : Roadmap.Pipeline) :
    (RetainedAliasSub.execute (raoPlan pipeline) (rasSuccessPlan pipeline) raState.1).1.2.2.heap=raState.2.heap :=
  RetainedAliasSubSafety.heap _ _ _

/-- The actual restored caller alias has owner RefOK, not merely list membership. -/
theorem rass_reference (pipeline : Roadmap.Pipeline) :
    ((RetainedAliasSub.execute (raoPlan pipeline) (rasSuccessPlan pipeline) raState.1).1.2.1.get .here).RefOK
      agEnv (RetainedAliasSub.execute (raoPlan pipeline) (rasSuccessPlan pipeline) raState.1).1.2.2.heap.ty :=
  Source.LocalsOK.get _ .here (rass_success pipeline).1.2

/-- Child1 typing survives although both callee aliases name child0. -/
theorem rass_dormant_path (pipeline : Roadmap.Pipeline) : agEnv.pathTy (agInner 1)=some agAliasTy := by
  have typed := rass_reference pipeline
  rw [rasub_alias] at typed
  exact typed
end Solidity.Yul.Views.Controls
