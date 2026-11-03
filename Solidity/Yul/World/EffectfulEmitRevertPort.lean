import Solidity.Yul.World.EffectfulEmitRevert

/-! Transport the actual selected Source halt over the existing physical action
and finishStep. No requested Outcome or assumed run equation is a premise.
Forward physical use requires checkedExecute?'s real incoming-view guards. -/
namespace Solidity.Yul.World.EffectfulEmitRevertPort
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.EffectfulEmitSource
open Solidity.Yul.World.EffectfulEmitPort

/-- Operational completion helper, not an arbitrary-result adequacy law. -/
def completeWith {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (emitted : (Except Halt Unit × Carrier (env indexed anonymous) Γ) ×
      ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay) :=
  let actual:=EffectfulEmitRevert.run G F 9 s
  let coupled:=(((actual.1.map (fun _=>()),actual.2),emitted.1.2.1.2),emitted.1.2.2)
  finishStep s b o (companionEnter ⟨s.2.ex,r⟩ F.this F.sender F.value [] F.static)
    coupled (if F.static then [] else [.log (log G F)]) (.success [])

def complete {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous)
      (registry indexed anonymous) (request F.this) b)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :=
  completeWith G F s r b o (execute G F s r b p o shared)

/-- Guard refusal remains None. It is not recoded as Source halt or EVM revert. -/
def checkedComplete? {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :=
  (checkedExecute? G F s r b o shared).map (completeWith G F s r b o)

/-- Exact actual Source error bytes drive full three-journal completion. -/
theorem actual {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous)
      (registry indexed anonymous) (request F.this) b)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (normal : F.static=false) :
    complete G F s r b p o shared=
      (.ok (.revert (EffectfulEmitRevert.data G)),
        (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs o.trace,EffectfulEmitRevert.data G⟩,o.trace,rfl⟩)) := by
  simp only [complete,completeWith,EffectfulEmitRevert.actual G F s normal,
    execute_normal G F normal s r b p o shared,normal,Bool.false_eq_true,if_false,
    Except.map,finishStep]
  have restored:=EffectfulEmitRollback.enclosing_revert G F s r b p o shared normal
    (EffectfulEmitRevert.data G)
  rw [execute_normal G F normal s r b p o shared] at restored
  simpa only [normal] using congrArg (fun result =>
    ((Except.ok (.revert (EffectfulEmitRevert.data G)) : Except Halt Solidity.Roadmap.Outcome),result)) restored

end Solidity.Yul.World.EffectfulEmitRevertPort
