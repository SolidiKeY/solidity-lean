import Solidity.Yul.World.DelegateEntry

namespace Solidity.Yul.World.DelegatePhysical
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical (flag registry)

def account : Address := CallerFrameChecks.owner

def request : PackedSlotRequest := ⟨false,account,7,0xaabbcc01⟩
def before : BoolEncodingJournal := boolEncodingWrite boolEncodingInitial
  (ownedByteKey false account flag,⟨⟨2,by decide⟩,by decide⟩)
def prepared := prepareRepresentedSlot (E:=env) registry registry (request) (before)
theorem ready : (prepared).isSome := by decide
def plan : RepresentedSlotPlan (E:=env) registry registry (request) (before) := (prepared).get (ready)

theorem source_op : (plan).packed.sourceOp=writeOp account := by
  change (Source.Op.account account (fun ac=>{ac with storage := preserveScalarWrite (L:=env.lay account) flagPath (representedPath flag canonicalTrueByte).codec (.bool true) ac.storage}))=_
  apply congrArg (Source.Op.account account)
  funext ac
  rw [StateCallPhysical.preserve_true]
  rfl

theorem complement : (plan).packed.residualUpdate=(complementKey false account 7,0xaabbcc00) := rfl

theorem step_exact {Γ} (s : EMState env Γ) (sender : Address) (v : Word) (depth : Nat)
    (r : ResidualJournal complementCarrierOwnership) (o : ObservedEffects env.layout env.lay env.lay)
    (same : o.effects.execution=s.2.ex) :
    (PhysicalSlotPort.step registry registry (request) (before)
      (DelegateBody.frame account sender v depth) (plan) s r o same rfl).1=
      (((.ok (),changed s account),residualWrite r (plan).packed.residualUpdate),
        requestEncoding (E:=env) registry registry (request) (before)) := by
  unfold PhysicalSlotPort.step
  rw [representedSourceStep_nonstatic _ _ _ _ rfl,source_op]
  rfl

theorem full_word {Γ} (s : EMState env Γ) (sender : Address) (v : Word) (depth : Nat)
    (r : ResidualJournal complementCarrierOwnership) (o : ObservedEffects env.layout env.lay env.lay)
    (same : o.effects.execution=s.2.ex) :
    let result:=PhysicalSlotPort.step registry registry (request) (before)
      (DelegateBody.frame account sender v depth) (plan) s r o same rfl
    reencodePersistentSlot (representedBanks (E:=env) registry false result.1.2)
      ⟨result.2.effects.execution,result.1.1.2⟩ account 7=some (request).raw :=
  PhysicalSlotPort.persistent_word (DelegateBody.frame account sender v depth) (plan) s r o same rfl rfl rfl
    (by simp only [registry,finiteSeparated,List.pairwise_singleton])

theorem target_unchanged {Γ} (s : EMState env Γ) (a target : Address) (different : target≠a) :
    (changed s a).2.ex.world.accounts target=s.2.ex.world.accounts target :=
  Source.World.set_other s.2.ex.world different _

theorem no_transfer {Γ} (s : EMState env Γ) (a : Address) :
    ((changed s a).2.ex.world.accounts a).balance=(s.2.ex.world.accounts a).balance := by
  change ((s.2.ex.world.set a _).accounts a).balance=_
  rw [Source.World.set_get]

/-- All three actual journals roll back, retaining the ordered prefix. -/
theorem outer_rollback {Γ} (s : EMState env Γ) (sender : Address) (v : Word)
    (r : ResidualJournal complementCarrierOwnership) (o : ObservedEffects env.layout env.lay env.lay)
    (data : Bytes) :
    finish s (before) o (companionEnter ⟨s.2.ex,r⟩ account sender v [] false)
      ⟨⟨changed s account,residualWrite r (plan).packed.residualUpdate⟩,
        requestEncoding (E:=env) registry registry (request) (before)⟩ [] (.revert data)=
      (⟨⟨s,r⟩,before⟩,⟨⟨s.2.ex,committedLogs o.trace,data⟩,o.trace,rfl⟩) := by
  simpa only [ExecState.run,residualRun,requestEncoding,changed,rollbackTrace,discardLogs,List.append_nil] using
    finish_runs_revert s r (before) o [writeOp account] [(plan).packed.residualUpdate]
      (encodingWrites (selectedSlotPaths (registry account) 7) false account (fun _=>(request).raw) (before))
      account sender v [] false [] data
end Solidity.Yul.World.DelegatePhysical
