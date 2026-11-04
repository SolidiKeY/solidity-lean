import Solidity.Lowering.V08.WorldReset
import Solidity.Lowering.V08.SourceEnvironmentControls

/-! Inhabited installed-account/reset correspondence, exact typed source reads
and dirty-read negative. Both pipelines retain complete reached Source machines.
This is not a full Image witness or an admitted call/transaction/compiler proof. -/
namespace Solidity.Lowering.V08.WorldResetControls
open Solidity

def Cell : Contract := contract!{ bool saved; bool transient scratch; }
def catalog : Unit → Contract := fun _ => Cell

def store (saved scratch : Bool) : Storage Cell := .cons (.prim saved) (.cons (.prim scratch) .nil)

def relation : WorldImage.StoreRelation SourceEnvironmentControls.E catalog :=
  fun _ _ persistent temporary target => ∃ saved scratch : Bool,
    persistent.read SourceEnvironmentControls.saved = some (.bool saved) ∧
    temporary.read SourceEnvironmentControls.scratch = some (.bool scratch) ∧
    target = store saved scratch

def slots : WorldImage.ResetInputs relation where
  slots address kind persistent temporary target represented := by
    obtain ⟨saved, scratch, persistentRead, transientRead, stored⟩ := represented
    subst target
    exact ⟨saved, false, persistentRead, rfl, rfl⟩

def kindOf (name : String) : Option Unit := if name = "C" then some () else none

def target : ContractWorld.World catalog :=
  { accounts := fun address =>
      if address = EnvironmentProjection.liftAddress SourceEnvironmentControls.self
      then some ⟨(), store true true⟩ else none
    funds := fun address => EnvironmentProjection.liftBalance
      (SourceEnvironmentControls.populated.ex.world.accounts
        (EnvironmentProjection.lowerAddress address)).balance }

theorem initial_account (pipeline : Roadmap.Pipeline) :
    WorldImage.AccountImage (SourceEnvironmentControls.global pipeline) kindOf relation
      SourceEnvironmentControls.populated target
      (EnvironmentProjection.liftAddress SourceEnvironmentControls.self) := by
  refine ⟨"C", (), store true true, rfl, rfl, rfl, ?_⟩
  exact ⟨true, true, rfl, rfl, rfl⟩

-- This is an installed AccountImage client, not a full Image instance.
def reached_account (pipeline : Roadmap.Pipeline) :
    WorldImage.AccountImage (SourceEnvironmentControls.global pipeline) kindOf relation
      (SourceTransient.endExecution SourceEnvironmentControls.populated) target.resetTransient
      (EnvironmentProjection.liftAddress SourceEnvironmentControls.self) :=
  WorldImage.account_reset slots _ (initial_account pipeline)

theorem target_reads :
    ((target.accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.self)).map
        (fun account => account.2.find (SRef.ofRoot "scratch" rfl)),
     (target.resetTransient.accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.self)).map
        (fun account => account.2.find (SRef.ofRoot "scratch" rfl))) =
      (some (some (.prim true)), some (some (.prim false))) := by
  rfl

theorem source_read_before (pipeline : Roadmap.Pipeline) :
    (Source.evalE (SourceEnvironmentControls.global pipeline) SourceEnvironmentControls.frame 2
      (.state SourceEnvironmentControls.scratchDecl rfl : Source.RExpr SourceEnvironmentControls.E [.bool] .bool)).run
      (SourceEnvironmentControls.locals, SourceEnvironmentControls.populated) =
      (.ok (.val (.bool true)), (SourceEnvironmentControls.locals, SourceEnvironmentControls.populated)) := by
  rfl

theorem source_read_after (pipeline : Roadmap.Pipeline) :
    (Source.evalE (SourceEnvironmentControls.global pipeline) SourceEnvironmentControls.frame 2
      (.state SourceEnvironmentControls.scratchDecl rfl : Source.RExpr SourceEnvironmentControls.E [.bool] .bool)).run
      (SourceEnvironmentControls.locals, SourceTransient.endExecution SourceEnvironmentControls.populated) =
      (.ok (.val (.bool false)), (SourceEnvironmentControls.locals,
        SourceTransient.endExecution SourceEnvironmentControls.populated)) := by
  rfl

theorem wrong_dirty_read :
    (target.resetTransient.accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.self)).map
      (fun account => account.2.find (SRef.ofRoot "scratch" rfl)) ≠ some (some (.prim true)) := by
  decide +kernel

theorem target_complete_owner :
    (target.accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.self),
     target.resetTransient.accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.self),
     target.resetTransient.funds, target.resetTransient.roles, target.resetTransient.timestamp) =
    (some ⟨(), store true true⟩, some ⟨(), store true false⟩,
      target.funds, target.roles, target.timestamp) := by
  rfl

/-- info: 'Solidity.Lowering.V08.WorldResetControls.slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slots
/-- info: 'Solidity.Lowering.V08.WorldResetControls.initial_account' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial_account
/-- info: 'Solidity.Lowering.V08.WorldResetControls.reached_account' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reached_account
/-- info: 'Solidity.Lowering.V08.WorldResetControls.target_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_reads
/-- info: 'Solidity.Lowering.V08.WorldResetControls.source_read_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_read_before
/-- info: 'Solidity.Lowering.V08.WorldResetControls.source_read_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_read_after
/-- info: 'Solidity.Lowering.V08.WorldResetControls.wrong_dirty_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrong_dirty_read
/-- info: 'Solidity.Lowering.V08.WorldResetControls.target_complete_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_complete_owner
end Solidity.Lowering.V08.WorldResetControls
