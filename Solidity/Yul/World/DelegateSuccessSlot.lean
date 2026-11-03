import Solidity.Yul.World.DelegateSuccessFraming

/-! Actual selected success reconstructs the complete physical persistent
word, including complement bytes. This is not universal layout adequacy. -/
namespace Solidity.Yul.World.DelegateSuccessSlot
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical (registry)
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegateSuccessBoundary (completed)

theorem full_word {Γ} (s : EMState env Γ) (sender : Address) (value : Word) (depth : Nat)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env) registry registry request b)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex) :
    reencodePersistentSlot (representedBanks (E:=env) registry false (completed s r b p o).1.2)
      ⟨(completed s r b p o).2.effects.execution,(completed s r b p o).1.1.2⟩ account 7=some request.raw := by
  have bank : request.transient=false := rfl
  have separated : finiteSeparated (registry request.address) := by
    simp only [registry,finiteSeparated,List.pairwise_singleton]
  have actual:=PhysicalSlotPort.persistent_word (DelegateBody.frame account sender value depth)
    p s r o shared rfl rfl bank separated
  unfold PhysicalSlotPort.step at actual
  rw [representedSourceStep_nonstatic _ _ _ _ rfl,DelegateSuccessPreparation.source_op] at actual
  exact actual

theorem complement (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env) registry registry request b) :
    p.packed.residualUpdate=(complementKey false account 7,0xaabbcc00) := by
  unfold PackedSlotPlan.residualUpdate
  rw [p.request_eq]
  change (complementKey false account 7,complementWord
    (packedOwnsByte (representedRegistry (registry account) false account (requestEncoding (E:=env) registry registry request b)) 7) request.raw)=_
  have owns : packedOwnsByte (representedRegistry (registry account) false account
      (requestEncoding (E:=env) registry registry request b)) 7=packedOwnsByte (registry account) 7 := by
    funext i
    exact representedRegistry_owns (registry account) false account _ 7 i
  rw [owns]
  rfl

/-- The successful residual update retains every other bank/account/slot. -/
theorem residual_other {Γ} (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (p : RepresentedSlotPlan (E:=env) registry registry request b)
    (o : ObservedEffects env.layout env.lay env.lay) (k : ResidualKey complementCarrierOwnership)
    (different : k≠complementKey false account 7) :
    (completed s r b p o).1.1.2.cells k=r.cells k := by
  change (residualWrite r p.packed.residualUpdate).cells k=r.cells k
  rw [complement]
  exact residualSave_other r.cells _ k _ different

/-- Actual complete Source operation equality preserves unrelated accounts. -/
theorem account_other {Γ} (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (p : RepresentedSlotPlan (E:=env) registry registry request b)
    (o : ObservedEffects env.layout env.lay env.lay) (a : Address) (different : a≠account) :
    (completed s r b p o).1.1.1.2.ex.world.accounts a=s.2.ex.world.accounts a :=
  DelegatePhysical.target_unchanged s account a different
end Solidity.Yul.World.DelegateSuccessSlot

namespace Solidity.Yul.World.DelegateSuccessSlot
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical (registry)
open Solidity.Yul.World.DelegatePhysical

theorem witness_word (G : Glob env) :
    reencodePersistentSlot (representedBanks (E:=env) registry false (DelegateSuccessWitness.result G).1.2)
      ⟨(DelegateSuccessWitness.result G).2.effects.execution,(DelegateSuccessWitness.result G).1.1.2⟩ account 7=some request.raw :=
  full_word (DelegateRevertWitness.source G) DelegateChecks.sender DelegateChecks.value 1
    DelegateRevertControls.residue DelegateRevertControls.encoding DelegateRevertControls.plan
    DelegateRevertControls.observer rfl

theorem wrong_old_word (G : Glob env) :
    reencodePersistentSlot (representedBanks (E:=env) registry false (DelegateSuccessWitness.result G).1.2)
      ⟨(DelegateSuccessWitness.result G).2.effects.execution,(DelegateSuccessWitness.result G).1.1.2⟩ account 7≠some 0xaabbcc00 := by
  rw [witness_word]
  decide

theorem transient_unchanged (G : Glob env) :
    (DelegateSuccessWitness.result G).1.1.2.cells (complementKey true account 7)=
      DelegateRevertControls.residue.cells (complementKey true account 7) :=
  residual_other (DelegateRevertWitness.source G) DelegateRevertControls.residue
    DelegateRevertControls.encoding DelegateRevertControls.plan DelegateRevertControls.observer
    (complementKey true account 7) (by intro eq; have impossible:=congrArg (fun x=>x.transient) eq; cases impossible)
end Solidity.Yul.World.DelegateSuccessSlot
