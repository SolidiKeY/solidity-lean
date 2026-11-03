import Solidity.Yul.World.EffectfulEmitPort

/-! Enclosing-frame rollback of the actual effectful emit producer. The enclosing
revert is a frame-composition input, not a newly claimed reachable Source call.
All three journals and full ordered observations are retained. -/
namespace Solidity.Yul.World.EffectfulEmitRollback
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.EffectfulEmitSource
open Solidity.Yul.World.EffectfulEmitPort

theorem rollback_after {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (F : Fr) (s : EMState (env indexed anonymous) Γ) :
    (Source.rollbackTo (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run
      (after G F s)=(.ok (),s) := by
  change ((Except.ok () : Except Source.Halt Unit),
    (s.1,{s.2 with ex:=((s.2.ex.apply (writeOp F.this)).undoN ((s.2.ex.apply (writeOp F.this)).journal.length-s.2.ex.journal.length)), logs:=(((F.this,legacy G)::s.2.logs).drop (((F.this,legacy G)::s.2.logs).length-s.2.logs.length))}))=_
  simp only [ExecState.journal_apply,Nat.add_sub_cancel_left,List.length_cons,
    ExecState.undoN,ExecState.undo_apply,List.drop]

/-- Actual producer followed by an enclosing frame revert. The enclosing outcome
is a composition input, not an arbitrary-callee execution certificate. -/
theorem enclosing_revert {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (F : Fr) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous)
      (registry indexed anonymous) (request F.this) b)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (normal : F.static=false) (data : Bytes) :
    finish s b o (companionEnter ⟨s.2.ex,r⟩ F.this F.sender F.value [] F.static)
      (execute G F s r b p o shared).1.2 [.log (log G F)] (.revert data)=
      (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs o.trace,data⟩,o.trace,rfl⟩) := by
  rw [execute_normal G F normal s r b p o shared]
  let f:=companionEnter (⟨s.2.ex,r⟩ : ResidualCompanion (env indexed anonymous).layout
    (env indexed anonymous).lay (env indexed anonymous).lay complementCarrierOwnership)
    F.this F.sender F.value [] F.static
  have back := companionRollback_run (⟨s.2.ex,r⟩ : ResidualCompanion (env indexed anonymous).layout
    (env indexed anonymous).lay (env indexed anonymous).lay complementCarrierOwnership)
    [writeOp F.this] [p.packed.residualUpdate] F.this F.sender F.value [] F.static
  change companionRollback f ⟨(after G F s).2.ex,residualWrite r p.packed.residualUpdate⟩=⟨s.2.ex,r⟩ at back
  have enc : boolEncodingRollback b.journal.length
      (requestEncoding (E:=env indexed anonymous) (registry indexed anonymous)
        (registry indexed anonymous) (request F.this) b)=b := boolEncodingRollback_run b _
  have rolled : (Source.rollbackTo (f.source.mark,s.2.logs.length,s.2.heap)).run
      (after G F s)=(.ok (),s) := rollback_after G F s
  change finish s b o f ⟨⟨after G F s,residualWrite r p.packed.residualUpdate⟩,
    requestEncoding (E:=env indexed anonymous) (registry indexed anonymous)
      (registry indexed anonymous) (request F.this) b⟩ [.log (log G F)] (.revert data)=_
  simp only [finish,back,enc,rolled,rollbackTrace,discardLogs,List.append_nil,returnData]

end Solidity.Yul.World.EffectfulEmitRollback
