import Solidity.Yul.Views.RetainedAliasOwnership
import Solidity.Yul.Views.RetainedLocalAliasImageControls

/-! Actual alias assignment followed by a canonical retained-child header write.
The enlarged captured inventory includes both dormant children; regrowth reads
tail77 from its original raw packed word, preserving child1 and high padding. -/
namespace Solidity.Yul.Views.Controls
open Solidity.Backend.MemoryOps
open RetainedAliasOwnership

def raoResidual (pipeline : Roadmap.Pipeline) : ResidualJournal complementCarrierOwnership :=
  ⟨fun k => if k.transient then 0 else packedMask (raiPaths pipeline) rhRaw0 k.slot,[]⟩
def raoNextRaw := saveSlot rhRaw0 101 3
def raoNext (pipeline : Roadmap.Pipeline) := (raiImage pipeline).snapshot raoNextRaw

theorem rao_next_checked (pipeline : Roadmap.Pipeline) : packedSeparationCheck (raoNext pipeline)=true := by
  rw [show raoNext pipeline=raoNext .legacy from rfl]
  decide

theorem rao_op_ready (pipeline : Roadmap.Pipeline) :
    (finiteAccountWrite? (T:=agEnv.lay) account (raoNext pipeline) raoNextRaw).isSome := by
  rw [show raoNext pipeline=raoNext .legacy from rfl]
  decide

def raoOp (pipeline : Roadmap.Pipeline) :=
  (finiteAccountWrite? (T:=agEnv.lay) account (raoNext pipeline) raoNextRaw).get (rao_op_ready pipeline)

@[irreducible]
def raoPlan (pipeline : Roadmap.Pipeline) : Plan (raGlobals pipeline) packedStepFrame 0 raState
    .here (.there .here) [] rhLayout agFixed [] 101 3 (raoResidual pipeline) :=
  ⟨0,(by rfl),raiImage pipeline,rai_prepared pipeline,raiPaths pipeline,rai_source pipeline,
    rhRaw0,rai_reencode pipeline,rai_separated pipeline,raiImage pipeline,rai_prepared pipeline,
    rao_next_checked pipeline,raoOp pipeline,Option.get_mem (rao_op_ready pipeline)⟩

/-- No success/prepared-output view premise: every field is a real checked computation. -/
theorem rao_full_map (pipeline : Roadmap.Pipeline) :
    finiteEncode (raoPlan pipeline).next ((execute (raoPlan pipeline)).1.2.2.ex.world.accounts account).storage
      (fun q => (execute (raoPlan pipeline)).2.cells (complementKey false account q))=
        some (saveSlot rhRaw0 101 3) := by
  have full := reencode (raoPlan pipeline) rfl
  change _=some (saveSlot (raoPlan pipeline).raw 101 3) at full
  have raw : (raoPlan pipeline).raw=rhRaw0 := by unfold raoPlan;rfl
  rw [raw] at full
  exact full

theorem rao_source_status (pipeline : Roadmap.Pipeline) :
    (execute (raoPlan pipeline)).1.1=.ok (Source.Val.storRef (τ:=agAliasTy) (by rfl) (agInner 0)) ∧
    (execute (raoPlan pipeline)).1.2.1=raAfter.1 := by
  rw [nonstatic (raoPlan pipeline) rfl]
  exact ⟨rfl,rfl⟩

/-- The actual Source length and element operations observe recovered tail77. -/
theorem rao_reads (pipeline : Roadmap.Pipeline) :
    (Source.readLen packedStepFrame (agInner 0)).run (execute (raoPlan pipeline)).1.2=
      (.ok 3,(execute (raoPlan pipeline)).1.2) ∧
    (Source.readLoc packedStepFrame (.stor ((agInner 0).go (.index 2)))).run (execute (raoPlan pipeline)).1.2=
      (.ok (Source.intWrap rcU16 77),(execute (raoPlan pipeline)).1.2) ∧
    (Source.readLoc packedStepFrame (.stor ((agInner 1).go (.index 0)))).run (execute (raoPlan pipeline)).1.2=
      (.ok (Source.intWrap rcU16 99),(execute (raoPlan pipeline)).1.2) := by
  rw [nonstatic (raoPlan pipeline) rfl]
  unfold raoPlan
  dsimp only
  rw [show raoOp pipeline=raoOp .legacy from rfl]
  exact ⟨rfl,rfl,rfl⟩

theorem rao_MemOK (pipeline : Roadmap.Pipeline) :
    Source.MemOK agEnv agState.2.heap.ty (execute (raoPlan pipeline)).1.2 :=
  RetainedAliasOwnership.MemOK (raoPlan pipeline) _ ra_initial_safe

/-- This restores exactly the Source external state and residual journal at the
post-alias boundary. It does not restore arbitrary caller locals or a whole call. -/
theorem rao_rollback (pipeline : Roadmap.Pipeline) :
    companionRollback (companionEnter (raoPlan pipeline).before account account 0 [] false)
      ⟨(execute (raoPlan pipeline)).1.2.2.ex,(execute (raoPlan pipeline)).2⟩=(raoPlan pipeline).before := by
  rw [RetainedAliasOwnership.companion]
  exact congrArg Prod.fst ((raoPlan pipeline).rollback rfl)

def raoStaticPlan (pipeline : Roadmap.Pipeline) : Plan (raGlobals pipeline) {packedStepFrame with static:=true} 0 raState
    .here (.there .here) [] rhLayout agFixed [] 101 3 (raoResidual pipeline) :=
  (raoPlan pipeline).withStatic true

/-- Static refusal is after the real alias producer; its prior journal survives. -/
theorem rao_static (pipeline : Roadmap.Pipeline) :
    execute (raoStaticPlan pipeline)=((.error (.revert []),raAfter),raoResidual pipeline) :=
  RetainedAliasOwnership.static (raoStaticPlan pipeline) rfl

/-- Treating static failure as erasure of the alias prefix would be wrong. -/
theorem rao_prefix_changed : raAfter≠raState := by
  intro same
  have paths := congrArg (fun st : Source.EMState agEnv [agAliasTy,agAliasTy] =>
    entryPathIndices rhLayout.root (localStoragePaths st.1)) same
  change [0,0]=[1,0] at paths
  cases paths

/-- Actual source-success-only journal updates retain arbitrary high padding. -/
theorem rao_residual (pipeline : Roadmap.Pipeline) :
    (execute (raoPlan pipeline)).2.cells (complementKey false account 1000)=⟨2^240,by decide⟩ ∧
    (execute (raoPlan pipeline)).2.cells (complementKey false account 2000)=⟨2^240,by decide⟩ := by
  rw [nonstatic (raoPlan pipeline) rfl]
  dsimp only
  rw [show (raoPlan pipeline).updates=(raoPlan .legacy).updates from by unfold raoPlan;rfl,
    show raoResidual pipeline=raoResidual .legacy from rfl]
  unfold raoPlan
  decide

theorem rao_other_bank (pipeline : Roadmap.Pipeline) :
    (execute (raoPlan pipeline)).2.cells (complementKey true account 1000)=
      (raoResidual pipeline).cells (complementKey true account 1000) :=
  other_journal (raoPlan pipeline) _ (Or.inl rfl)

theorem rao_other_account (pipeline : Roadmap.Pipeline) :
    (execute (raoPlan pipeline)).2.cells (complementKey false 2 1000)=
      (raoResidual pipeline).cells (complementKey false 2 1000) :=
  other_journal (raoPlan pipeline) _ (Or.inr (by decide))
end Solidity.Yul.Views.Controls
