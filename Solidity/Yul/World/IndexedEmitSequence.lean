import Solidity.Yul.World.IndexedEmitRules

/-! Two actual typed indexed-local Source emits through the owned observation
extension. The legacy Source log and ordered extension trace stay distinct. -/
namespace Solidity.Yul.World.IndexedEmitSequence
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.IndexedEmitPort
open Solidity.Yul.World.ScalarEmitPort (env)

def twice {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) Γ) (i j : Source.Idx Γ ReturningCall.uint)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :=
  let first:=executeCaller G false s i r b o shared
  let sharedNext : first.2.effects.execution=first.1.2.1.1.2.ex := by
    dsimp only [first]
    rw [caller_execute_run]
    exact shared
  executeCaller G false first.1.2.1.1 j first.1.2.1.2 first.1.2.2 first.2 sharedNext

theorem twice_exact {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) Γ) (i j : Source.Idx Γ ReturningCall.uint)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    twice G s i j r b o shared=
      ((.ok (),⟨⟨ScalarLocalEmit.after G (selected s.1 j) (ScalarLocalEmit.after G (selected s.1 i) s),r⟩,b⟩),
        emitObserved (emitObserved o (encoding G s.1 i)) (encoding G s.1 j)) := by
  unfold twice
  simp only [caller_execute_run]
  rfl

theorem trace_exact {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) Γ) (i j : Source.Idx Γ ReturningCall.uint)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    (twice G s i j r b o shared).2.trace=o.trace++[.log (encoding G s.1 i),.log (encoding G s.1 j)] := by
  rw [twice_exact]
  simp only [emitObserved,List.append_assoc,List.singleton_append]

theorem rollback_legacy {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) Γ) (i j : Source.Idx Γ ReturningCall.uint) :
    (Source.rollbackTo (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run
      (ScalarLocalEmit.after G (selected s.1 j) (ScalarLocalEmit.after G (selected s.1 i) s))=(.ok (),s) := by
  change ((Except.ok () : Except Source.Halt Unit),
    (s.1,{s.2 with ex:=s.2.ex.undoN (s.2.ex.journal.length-s.2.ex.journal.length), logs:=((CallerFrameChecks.owner,G.selector (ScalarEmitPort.signature indexed anonymous)++ScalarLocalEmit.data (selected s.1 j))::(CallerFrameChecks.owner,G.selector (ScalarEmitPort.signature indexed anonymous)++ScalarLocalEmit.data (selected s.1 i))::s.2.logs).drop ((s.2.logs.length+2)-s.2.logs.length)}))=_
  simp only [Nat.sub_self,ExecState.undoN,Nat.add_sub_cancel_left,List.drop]

/-- Enclosing rollback removes exactly the two failed-frame extension logs,
restores actual legacy Source logs, and retains arbitrary full caller prefixes. -/
theorem enclosing_revert {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) Γ) (i j : Source.Idx Γ ReturningCall.uint)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (bytes : Roadmap.Bytes) :
    finish s b o (companionEnter ⟨s.2.ex,r⟩ CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false)
      (twice G s i j r b o shared).1.2 [.log (encoding G s.1 i),.log (encoding G s.1 j)] (.revert bytes)=
      (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs o.trace,bytes⟩,o.trace,rfl⟩) := by
  rw [twice_exact]
  have companion := companionRollback_run (⟨s.2.ex,r⟩ : ResidualCompanion (env indexed anonymous).layout
    (env indexed anonymous).lay (env indexed anonymous).lay complementCarrierOwnership)
    [] [] CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false
  have enc := boolEncodingRollback_run b []
  simp only [companionRunSource,companionRunResidual,ExecState.run,residualRun] at companion
  simp only [boolEncodingRun] at enc
  let f:=companionEnter (⟨s.2.ex,r⟩ : ResidualCompanion (env indexed anonymous).layout
    (env indexed anonymous).lay (env indexed anonymous).lay complementCarrierOwnership)
    CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false
  have back : companionRollback f ⟨(ScalarLocalEmit.after G (selected s.1 j) (ScalarLocalEmit.after G (selected s.1 i) s)).2.ex,r⟩=⟨s.2.ex,r⟩ := companion
  have rolled : (Source.rollbackTo (f.source.mark,s.2.logs.length,s.2.heap)).run
      (ScalarLocalEmit.after G (selected s.1 j) (ScalarLocalEmit.after G (selected s.1 i) s))=(.ok (),s) := rollback_legacy G s i j
  change finish s b o f ⟨⟨ScalarLocalEmit.after G (selected s.1 j) (ScalarLocalEmit.after G (selected s.1 i) s),r⟩,b⟩
    [.log (encoding G s.1 i),.log (encoding G s.1 j)] (.revert bytes)=_
  simp only [finish,back,enc,rolled,rollbackTrace,discardLogs,List.append_nil,returnData]

def caller (indexed anonymous : Bool) :=
  (⟨IndexedEmitChecks.inputs indexed anonymous,(ScalarEmitChecks.caller indexed anonymous).2⟩ :
    EMState (env indexed anonymous) [ReturningCall.uint,.bool,ReturningCall.uint,ReturningCall.uint])

theorem witnessed_order {indexed anonymous} (G : Glob (env indexed anonymous)) :
    (twice G (caller indexed anonymous) IndexedEmitChecks.index .here CallerFrameChecks.residual
      CallerFrameChecks.encoding (ScalarEmitChecks.observed indexed anonymous) rfl).2.trace=
      GeneralReturningChecks.tracePrefix++[.log (encoding G (IndexedEmitChecks.inputs indexed anonymous) IndexedEmitChecks.index),
        .log (encoding G (IndexedEmitChecks.inputs indexed anonymous) .here)] := trace_exact G _ _ _ _ _ _ rfl

theorem reversed_order (G : Glob (env false false)) :
    (twice G (caller false false) IndexedEmitChecks.index .here CallerFrameChecks.residual
      CallerFrameChecks.encoding (ScalarEmitChecks.observed false false) rfl).2.trace≠
      GeneralReturningChecks.tracePrefix++[.log (encoding G (IndexedEmitChecks.inputs false false) .here),
        .log (encoding G (IndexedEmitChecks.inputs false false) IndexedEmitChecks.index)] := by
  rw [witnessed_order]
  intro same
  have first:=(List.cons.inj (List.append_cancel_left same)).1
  exact IndexedEmitChecks.wrong_head_data G (congrArg Log.data (Observation.log.inj first)).symm

end Solidity.Yul.World.IndexedEmitSequence
