import Solidity.Yul.World.GeneralReturningHalts

namespace Solidity.Yul.World.GeneralReturning
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall (env glob input output)

/-- Balance-only source operations retain every typed storage component. -/
theorem balance_storage {D L T} (s : ExecState D L T) (owner : Address) (v : Word) (a : Address) :
    ((s.apply (.account owner (fun x=>x.withBalance v))).world.accounts a).storage=(s.world.accounts a).storage := by
  change ((s.world.set owner ((s.world.accounts owner).withBalance v)).accounts a).storage=_
  by_cases same : a=owner
  · subst a
    rw [World.set_get]
    rfl
  · rw [World.set_other s.world same]

/-- Exact preservation of the source components used by BOTH VY2 banks under
actual transfer; companion residual/owned encodings need no erasure/update. -/
theorem transfer_storage {D L T} (s next : ExecState D L T) (src dst : Address) (v : Word)
    (different : src≠dst) (transfer : s.transfer src dst v=some next) :
    (∀ a, (next.world.accounts a).storage=(s.world.accounts a).storage) ∧ next.transient=s.transient := by
  simp only [ExecState.transfer,different,if_false] at transfer
  split at transfer
  · cases transfer
    refine ⟨?_,rfl⟩
    intro a
    exact (balance_storage _ dst _ a).trans (balance_storage _ src _ a)
  · cases transfer

/-- Actual source journal prefix is retained verbatim under transfer; the
two newly recorded accounts are newest-first, not a projected world claim. -/
theorem transfer_journal_prefix {D L T} (s next : ExecState D L T) (src dst : Address) (v : Word)
    (different : src≠dst) (transfer : s.transfer src dst v=some next) :
    next.journal.drop 2=s.journal ∧ next.journal.length=s.journal.length+2 := by
  simp only [ExecState.transfer,different,if_false] at transfer
  split at transfer
  · cases transfer
    exact ⟨rfl,rfl⟩
  · cases transfer

/-- The ACTUAL persistent and transient re-encoders retain complete raw words,
including residual and dirty Bool bytes, under the selected real transfer. -/
theorem represented_views {Γ} (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (ps ts : (a : Address) → List (ScalarPath env.layout (env.lay a))) (a : Address) (q : Word) :
    reencodePersistentSlot (representedBanks ps false b) ⟨next,r⟩ a q=
      reencodePersistentSlot (representedBanks ps false b) ⟨s.2.ex,r⟩ a q ∧
    reencodeTransientSlot (representedBanks ts true b) ⟨next,r⟩ a q=
      reencodeTransientSlot (representedBanks ts true b) ⟨s.2.ex,r⟩ a q := by
  have keep := transfer_storage s.2.ex next CallerFrameChecks.owner CallerFrameChecks.receiver 7 (by decide) transfer
  constructor
  · unfold reencodePersistentSlot
    rw [keep.1 a]
  · unfold reencodeTransientSlot
    rw [keep.2]

theorem after_memOK {Γ} (H : HeapTy) (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (ok : Source.MemOK env H s) : Source.MemOK env H (after s next) :=
  ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2⟩

/-- Owner's actual partial-window MemOK theorem, applied to the actual returned
source state. No full allocator/view/world adequacy premise is smuggled in. -/
theorem output_memOK {Γ} (H : HeapTy) (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (p : Placement s.2.heap)
    (a : Nat) (string : Bool) (old : Bytes)
    (found : s.2.heap.get a=some ⟨heapByteType string,heapByteData env.layout string old⟩)
    (m outMemory : ByteView) (offset source size : Word) (out : EMState env Γ)
    (copied : HeapWindow.copyStateWindow (successResult s next r b o).2.effects (after s next)
      p a string old found m offset source size=some (outMemory,out))
    (ok : Source.MemOK env H s) : Source.MemOK env H out :=
  HeapWindow.copyStateWindow_memOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ copied (after_memOK H s next ok)

/-- Actual successful child -> enclosing three-journal revert, for arbitrary
caller worlds/prefixes and actual transfer. This boundary restores the full
source/physical state and ordered caller trace, not projected observations. -/
theorem enclosing_revert (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (data : Bytes) :
    finish s b o (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      (successResult s next r b o).1 [] (.revert data)=
      (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs o.trace,data⟩,o.trace,rfl⟩) := by
  simp only [ExecState.transfer,show CallerFrameChecks.owner≠CallerFrameChecks.receiver from by decide,if_false] at transfer
  split at transfer
  next affordable =>
    cases transfer
    have restored := finish_runs_revert s r b o
      [.account CallerFrameChecks.owner (fun x=>x.withBalance
        ⟨(s.2.ex.world.accounts CallerFrameChecks.owner).balance.val-7,by omega⟩),
       .account CallerFrameChecks.receiver (fun x=>x.withBalance
        ⟨(s.2.ex.world.accounts CallerFrameChecks.receiver).balance.val+7,affordable.2⟩)]
      [] [] CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false [] data
    simpa only [ExecState.run,residualRun,boolEncodingRun,rollbackTrace,discardLogs,List.append_nil] using restored
  next impossible => cases transfer

end Solidity.Yul.World.GeneralReturning
