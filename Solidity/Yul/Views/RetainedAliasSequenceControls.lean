import Solidity.Yul.Views.RetainedAliasSequence
import Solidity.Yul.Views.RetainedAliasOwnershipControls

/-! Two actual checked programs share their reached source state, residual and
retained capture prefix. A static second shrink must not reset the first growth
or its complementary journal; a successful shrink retains raw tail bytes. -/
namespace Solidity.Yul.Views.Controls
open Solidity.Backend.MemoryOps RetainedAliasOwnership RetainedAliasSequence

def rasScopes (pipeline : Roadmap.Pipeline) :=
  (captureEvaluatedValue (raGlobals pipeline) {packedStepFrame with static:=true} 2
    (sourceLocalAlias .here (.there .here)) (raCaptured pipeline).2 (execute (raoPlan pipeline)).1.2).2

def rasState (pipeline : Roadmap.Pipeline) : Source.EMState agEnv [agAliasTy,agAliasTy] :=
  ((execute (raoPlan pipeline)).1.2.1.set .here ((execute (raoPlan pipeline)).1.2.1.get (.there .here)),
    (execute (raoPlan pipeline)).1.2.2)

def rasPreparation (pipeline : Roadmap.Pipeline) :=
  prepareCapturedOwnership? {packedStepFrame with static:=true} rhLayout agFixed [] (rasScopes pipeline) 101 0
    (rasState pipeline) (execute (raoPlan pipeline)).2

theorem ras_ready (pipeline : Roadmap.Pipeline) : (rasPreparation pipeline).isSome := by
  cases pipeline <;> unfold rasPreparation rasScopes rasState raoPlan <;> decide

def rasPlan (pipeline : Roadmap.Pipeline) : NextPlan (raoPlan pipeline) (raGlobals pipeline)
    {packedStepFrame with static:=true} 0 .here (.there .here) rhLayout agFixed [] 101 0 :=
  (rasPreparation pipeline).get (ras_ready pipeline)

/-- The checked next plan consumes the first ACTUAL source/residual result. -/
theorem ras_late_static (pipeline : Roadmap.Pipeline) :
    executeThen (raoPlan pipeline) (rasPlan pipeline)=
      ((.error (.revert []),rasState pipeline),(execute (raoPlan pipeline)).2) :=
  late_static (raoPlan pipeline) (rasPlan pipeline) rfl rfl

/-- The first completed physical map survives late static failure. -/
theorem ras_prefix_map (pipeline : Roadmap.Pipeline) :
    finiteEncode (raoPlan pipeline).next
      ((executeThen (raoPlan pipeline) (rasPlan pipeline)).1.2.2.ex.world.accounts account).storage
      (fun slot => (executeThen (raoPlan pipeline) (rasPlan pipeline)).2.cells (complementKey false account slot))=
        some (raoPlan pipeline).nextRaw :=
  late_static_reencode (raoPlan pipeline) (rasPlan pipeline) rfl rfl

def rasSuccessPlan (pipeline : Roadmap.Pipeline) : NextPlan (raoPlan pipeline) (raGlobals pipeline)
    packedStepFrame 0 .here (.there .here) rhLayout agFixed [] 101 0 := (rasPlan pipeline).withStatic false

theorem ras_success_map (pipeline : Roadmap.Pipeline) :
    finiteEncode (rasSuccessPlan pipeline).next
      ((executeThen (raoPlan pipeline) (rasSuccessPlan pipeline)).1.2.2.ex.world.accounts account).storage
      (fun slot => (executeThen (raoPlan pipeline) (rasSuccessPlan pipeline)).2.cells (complementKey false account slot))=
        some (rasSuccessPlan pipeline).nextRaw :=
  RetainedAliasSequence.reencode (raoPlan pipeline) (rasSuccessPlan pipeline) rfl rfl

/-- Returning the original journal after late refusal would erase a real prefix. -/
theorem ras_no_reset (pipeline : Roadmap.Pipeline) :
    (executeThen (raoPlan pipeline) (rasPlan pipeline)).2≠raoResidual pipeline := by
  intro reset
  have cell := congrArg (fun journal : ResidualJournal complementCarrierOwnership =>
    journal.cells (complementKey false account 1000)) reset
  rw [ras_late_static] at cell
  dsimp only at cell
  rw [(rao_residual pipeline).1] at cell
  change (⟨2^240,by decide⟩ : Roadmap.Word)=packedMask (raiPaths pipeline) rhRaw0 1000 at cell
  rw [(rai_complement pipeline).2.2] at cell
  have different : (⟨2^240,by decide⟩ : Roadmap.Word)≠⟨77*2^32+2^240,by decide⟩ := by decide
  exact different cell

theorem ras_safe (pipeline : Roadmap.Pipeline) : Source.MemOK agEnv agState.2.heap.ty
    (executeThen (raoPlan pipeline) (rasPlan pipeline)).1.2 :=
  RetainedAliasSequence.MemOK (raoPlan pipeline) (rasPlan pipeline) _ ra_initial_safe

/-- The second capture still includes the overwritten old child1 alias. -/
theorem ras_captured_union (pipeline : Roadmap.Pipeline) : capturedVisitIndices rhLayout [] (rasScopes pipeline) 0=[1,0] := by
  unfold rasScopes
  rw [RetainedLocalAlias.captured,(rao_source_status pipeline).2]
  rfl

def rasSkipScopes (pipeline : Roadmap.Pipeline) :=
  (captureEvaluatedValue (raGlobals pipeline) packedStepFrame 2
    (sourceLocalAlias .here (.there .here)) (raCaptured pipeline).2 (execute (raoStaticPlan pipeline)).1.2).2

def rasSkipState (pipeline : Roadmap.Pipeline) : Source.EMState agEnv [agAliasTy,agAliasTy] :=
  ((execute (raoStaticPlan pipeline)).1.2.1.set .here ((execute (raoStaticPlan pipeline)).1.2.1.get (.there .here)),
    (execute (raoStaticPlan pipeline)).1.2.2)

def rasSkipPreparation (pipeline : Roadmap.Pipeline) :=
  prepareCapturedOwnership? packedStepFrame rhLayout agFixed [] (rasSkipScopes pipeline) 101 0
    (rasSkipState pipeline) (execute (raoStaticPlan pipeline)).2

theorem rasSkip_state_eq (pipeline : Roadmap.Pipeline) : rasSkipState pipeline=raAfter := by
  unfold rasSkipState
  rw [rao_static]
  rfl

theorem rasSkip_journal_eq (pipeline : Roadmap.Pipeline) :
    (execute (raoStaticPlan pipeline)).2=raoResidual pipeline := by rw [rao_static]

theorem rasSkip_visits (pipeline : Roadmap.Pipeline) :
    capturedVisitIndices rhLayout [] (rasSkipScopes pipeline) (0:Roadmap.Word).val=[1,0] := by
  unfold rasSkipScopes
  rw [RetainedLocalAlias.captured,rao_static]
  rfl

def rasSkipImage (pipeline : Roadmap.Pipeline) : CapturedArrayImage rhLayout agFixed [] (rasSkipScopes pipeline) 0 :=
  ⟨raiElements,by rw [rasSkip_visits];exact Option.get_mem rai_elements_ready⟩
def rasSkipRaw := saveSlot rhRaw0 101 0

theorem rasSkip_checked (pipeline : Roadmap.Pipeline) :
    packedSeparationCheck ((rasSkipImage pipeline).snapshot rasSkipRaw)=true := by
  rw [show (rasSkipImage pipeline).snapshot rasSkipRaw=(rasSkipImage .legacy).snapshot rasSkipRaw from rfl]
  decide

theorem rasSkip_op_ready (pipeline : Roadmap.Pipeline) :
    (finiteAccountWrite? (T:=agEnv.lay) account ((rasSkipImage pipeline).snapshot rasSkipRaw) rasSkipRaw).isSome := by
  rw [show (rasSkipImage pipeline).snapshot rasSkipRaw=(rasSkipImage .legacy).snapshot rasSkipRaw from rfl]
  decide

def rasSkipOp (pipeline : Roadmap.Pipeline) :=
  (finiteAccountWrite? (T:=agEnv.lay) account ((rasSkipImage pipeline).snapshot rasSkipRaw) rasSkipRaw).get (rasSkip_op_ready pipeline)

def rasSkipPlan (pipeline : Roadmap.Pipeline) : NextPlan (raoStaticPlan pipeline) (raGlobals pipeline)
    packedStepFrame 0 .here (.there .here) rhLayout agFixed [] 101 0 :=
  ⟨0,(by
    change aggregateSourceLengths packedStepFrame (rasSkipState pipeline) rhLayout.header=some 0
    rw [rasSkip_state_eq]
    rfl),
    rasSkipImage pipeline,CapturedArrayImage.prepared _,raiPaths pipeline,
    (by
      change (rasSkipImage pipeline).sourceInventory? (F:=packedStepFrame) (rasSkipState pipeline)=some (raiPaths pipeline)
      change (raiImage pipeline).sourceInventory? (F:=packedStepFrame) (rasSkipState pipeline)=some (raiPaths pipeline)
      rw [rasSkip_state_eq]
      exact rai_source pipeline),
    rhRaw0,(by
      change finiteEncode (raiPaths pipeline) ((rasSkipState pipeline).2.ex.world.accounts account).storage
        (fun q => (execute (raoStaticPlan pipeline)).2.cells (complementKey false account q))=some rhRaw0
      rw [rasSkip_state_eq,rasSkip_journal_eq]
      exact rai_reencode pipeline),
    rai_separated pipeline,rasSkipImage pipeline,CapturedArrayImage.prepared _,rasSkip_checked pipeline,
    rasSkipOp pipeline,Option.get_mem (rasSkip_op_ready pipeline)⟩

/-- Factored checked fields reproduce the REAL public preparation, without a
larger recursion/heartbeat budget for one closed-model reduction. -/
theorem ras_skip_prepared (pipeline : Roadmap.Pipeline) :
    rasSkipPreparation pipeline=some (rasSkipPlan pipeline) := checked_prepared (rasSkipPlan pipeline)

theorem ras_skip_ready (pipeline : Roadmap.Pipeline) : (rasSkipPreparation pipeline).isSome := by
  rw [ras_skip_prepared]
  rfl

theorem ras_first_refusal (pipeline : Roadmap.Pipeline) :
    executeThen (raoStaticPlan pipeline) (rasSkipPlan pipeline)=
      ((.error (.revert []),(execute (raoStaticPlan pipeline)).1.2),(execute (raoStaticPlan pipeline)).2) :=
  first_static (raoStaticPlan pipeline) (rasSkipPlan pipeline) rfl

/-- The skipped second operation really WOULD succeed on its checked input. -/
theorem ras_ready_but_skipped (pipeline : Roadmap.Pipeline) :
    (execute (rasSkipPlan pipeline)).1.1=.ok ((execute (raoStaticPlan pipeline)).1.2.1.get (.there .here)) ∧
    (executeThen (raoStaticPlan pipeline) (rasSkipPlan pipeline)).1.1=.error (.revert []) := by
  constructor
  · rw [RetainedAliasOwnership.nonstatic (rasSkipPlan pipeline) rfl]
  · rw [ras_first_refusal]

/-- The concrete sequence is the actual Source monadic program. -/
theorem ras_source_bind (pipeline : Roadmap.Pipeline) :
    (executeThen (raoPlan pipeline) (rasPlan pipeline)).1=
      (program (raGlobals pipeline) packedStepFrame 0 .here (.there .here) (raoPlan pipeline).sourceOp >>= fun _ =>
        program (raGlobals pipeline) {packedStepFrame with static:=true} 0 .here (.there .here)
          (rasPlan pipeline).sourceOp).run raState := source (raoPlan pipeline) (rasPlan pipeline)

theorem ras_distinct_headers (pipeline : Roadmap.Pipeline) :
    (raoPlan pipeline).nextRaw 101=3 ∧ (rasSuccessPlan pipeline).nextRaw 101=0 :=
  ⟨find_saveSlot _ _ _,find_saveSlot _ _ _⟩
end Solidity.Yul.Views.Controls
