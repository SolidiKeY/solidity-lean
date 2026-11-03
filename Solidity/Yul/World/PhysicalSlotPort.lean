import Solidity.Yul.World.Adapters
import Solidity.Yul.Views.OwnedBoolFrame
import Solidity.Yul.Views.SourceEnvironmentInputs

/-! World-facing actual represented slot action. The complete VY2 result is
returned alongside observations: source, complement and owned-byte journals
are never replaced by an execution-only rollback claim. -/
namespace Solidity.Yul.World.PhysicalSlotPort
open Solidity.Source
open Solidity.Roadmap (Address Word)
open Solidity.Yul.Views

/-- Checked same-account request and actual shared source execution. Source
EMState and all physical journals remain in the producer's original carrier. -/
def step {E : Env} {Γ : RCtx}
    (ps ts : (a : Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership)
    (entry : ObservedEffects E.layout E.lay E.lay)
    (_sameExecution : entry.effects.execution = s.2.ex) (_owner : q.address = F.this) :=
  let physical := representedSourceStep ps ts q before F p s r
  (physical, { entry with effects := { entry.effects with execution := physical.1.1.2.2.ex } })

def frameWrite? {E : Env} {Γ : RCtx}
    (ps ts : (a : Address) → List (ScalarPath E.layout (E.lay a)))
    (F : Fr) (bank : Bool) (slot raw : Word) (before : BoolEncodingJournal)
    (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (entry : ObservedEffects E.layout E.lay E.lay) (same : entry.effects.execution = s.2.ex) :=
  let q : PackedSlotRequest := ⟨bank,F.this,slot,raw⟩
  (prepareRepresentedSlot ps ts q before).map (fun p => step ps ts q before F p s r entry same rfl)

/-- This exact public adapter consumes the actual same-account preparer. -/
theorem frameWrite_physical {E : Env} {Γ : RCtx}
    (ps ts : (a : Address) → List (ScalarPath E.layout (E.lay a)))
    (F : Fr) (bank : Bool) (slot raw : Word) (before : BoolEncodingJournal)
    (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (entry : ObservedEffects E.layout E.lay E.lay) (same : entry.effects.execution = s.2.ex) :
    (frameWrite? ps ts F bank slot raw before s r entry same).map Prod.fst =
      representedFrameWrite? ps ts F bank slot raw before s r := by
  simp only [frameWrite?,representedFrameWrite?,Option.map_map,Function.comp_def,step]

theorem persistent_word {E Γ ps ts q before} (F : Fr) (p : RepresentedSlotPlan ps ts q before)
    (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (entry : ObservedEffects E.layout E.lay E.lay) (same : entry.effects.execution = s.2.ex)
    (owner : q.address = F.this) (static : F.static = false) (bank : q.transient = false)
    (separated : finiteSeparated (ps q.address)) :
    let result := step ps ts q before F p s r entry same owner
    reencodePersistentSlot (representedBanks ps false result.1.2)
      ⟨result.2.effects.execution,result.1.1.2⟩ q.address q.slot = some q.raw :=
  represented_step_persistent_at_request F p s r static bank separated

/-- Both rollback components use the SAME actual checked operation. Full
source/complement rollback and owned-byte rollback are jointly retained. -/
theorem rollback {E Γ ps ts q before} (F : Fr) (p : RepresentedSlotPlan ps ts q before)
    (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (entry : ObservedEffects E.layout E.lay E.lay) (same : entry.effects.execution = s.2.ex)
    (owner : q.address = F.this) (static : F.static = false) :
    let result := step ps ts q before F p s r entry same owner
    companionRollback (companionEnter ⟨s.2.ex,r⟩ F.this F.this 0 [] false)
      ⟨result.2.effects.execution,result.1.1.2⟩ = ⟨s.2.ex,r⟩ ∧
    boolEncodingRollback before.journal.length result.1.2 = before ∧ result.2.trace = entry.trace := by
  have restore := represented_step_rollback F p s r static
  exact ⟨restore.1,restore.2,rfl⟩

theorem memOK {E Γ ps ts q before} (H : HeapTy) (F : Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (entry : ObservedEffects E.layout E.lay E.lay)
    (same : entry.effects.execution = s.2.ex) (owner : q.address = F.this) (ok : MemOK E H s) :
    MemOK E H (step ps ts q before F p s r entry same owner).1.1.1.2 :=
  representedSourceStep_MemOK H F p s r ok

theorem static_result {E Γ ps ts q before} (F : Fr) (p : RepresentedSlotPlan ps ts q before)
    (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (entry : ObservedEffects E.layout E.lay E.lay) (same : entry.effects.execution = s.2.ex)
    (owner : q.address = F.this) (static : F.static = true) :
    let result := step ps ts q before F p s r entry same owner
    result.1 = (((.error (.revert []),s),r),before) ∧
    result.2.effects.execution = entry.effects.execution ∧ result.2.trace = entry.trace ∧
    result.2.effects.returndata = entry.effects.returndata := by
  unfold step
  rw [representedSourceStep_static F p s r static]
  exact ⟨rfl,same.symm,rfl,rfl⟩

/-- Public CallFrame context, including actual calldata, is transported through
the producer adapter; library code selection never changes its storage account. -/
def sourceFrame (frame : Source.CallFrame) (contract : String) (checked : Bool) (depth : Nat) : Fr :=
  sourceFrameOfCall frame contract checked depth

theorem sourceFrame_owner (frame : Source.CallFrame) (contract : String) (checked : Bool) (depth : Nat) :
    (sourceFrame frame contract checked depth).this = frame.this ∧
    (sourceFrame frame contract checked depth).static = frame.static := ⟨rfl,rfl⟩

/-- Enclosing rollback after the committed actual child restores all three
journals. The observations remain the full caller prefix, not projections. -/
theorem two_outer_rollback {E Γ ps ts q before} (F : Fr) (p : RepresentedSlotPlan ps ts q before)
    (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (entry : ObservedEffects E.layout E.lay E.lay) (same : entry.effects.execution = s.2.ex)
    (owner : q.address = F.this) (next : PackedSlotRequest)
    (child : RepresentedSlotPlan ps ts next (requestEncoding ps ts q before))
    (childOwner : next.address = F.this) (static : F.static = false) :
    let first := step ps ts q before F p s r entry same owner
    let second := step ps ts next (requestEncoding ps ts q before) F child first.1.1.1.2 first.1.1.2 first.2 rfl childOwner
    companionRollback (companionEnter ⟨s.2.ex,r⟩ F.this F.this 0 [] false)
      (companionCommit (companionEnter ⟨first.2.effects.execution,first.1.1.2⟩ F.this F.this 0 [] false)
        ⟨second.2.effects.execution,second.1.1.2⟩) = ⟨s.2.ex,r⟩ ∧
    boolEncodingRollback before.journal.length second.1.2 = before ∧ second.2.trace = entry.trace := by
  have restore := represented_two_outer_rollback F p s r next child static
  exact ⟨restore.1,restore.2,rfl⟩

theorem transient_word {E Γ ps ts q before} (F : Fr) (p : RepresentedSlotPlan ps ts q before)
    (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (entry : ObservedEffects E.layout E.lay E.lay) (same : entry.effects.execution = s.2.ex)
    (owner : q.address = F.this) (static : F.static = false) (bank : q.transient = true)
    (separated : finiteSeparated (ts q.address)) :
    let result := step ps ts q before F p s r entry same owner
    reencodeTransientSlot (representedBanks ts true result.1.2)
      ⟨result.2.effects.execution,result.1.1.2⟩ q.address q.slot = some q.raw := by
  have result := representedSourceStep_transient F p s r static
    (by rw [p.request_eq]; exact bank) (by rw [p.request_eq]; exact separated)
  simpa only [p.request_eq] using result

end Solidity.Yul.World.PhysicalSlotPort
