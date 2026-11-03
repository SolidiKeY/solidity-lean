import Solidity.Yul.World.StaticEventPort

namespace Solidity.Yul.World.StaticEventPortControls
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StaticEventEncoding
open Solidity.Yul.World.StaticEventControls

theorem shape (anonymous : Bool) : metadata (declaration anonymous)=some ([true,false,true],anonymous) := by
  cases anonymous <;> simp only [metadata,declaration,indexedFlags]

theorem fits {anonymous} (G : Glob (env anonymous)) :
    (topics (ts:=types) G (declaration anonymous) anonymous (part anonymous)).length<5 := by
  cases anonymous <;> simp only [topics,part,Bool.false_eq_true,if_false,if_true,List.length_cons,List.length_nil] <;> decide

def run {anonymous Δ} (G : Glob (env anonymous)) (F : Fr) (s : EMState (env anonymous) Δ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :=
  StaticEventPort.execute G F 8 (declaration anonymous) (typed anonymous) (args anonymous) (locals anonymous)
    s (values anonymous) (evaluated G F s.2) [true,false,true] anonymous (shape anonymous)
    (part anonymous) (partition anonymous) (fits G) r b o shared

def log {anonymous} (G : Glob (env anonymous)) (F : Fr) :=
  resultLog (ts:=types) G F (declaration anonymous) anonymous (part anonymous) (fits G) ReturningCall.output

def legacyWords : List Word := [1,Source.intWord ReturningCall.value,0x70]

theorem run_exact {anonymous Δ} (G : Glob (env anonymous)) (F : Fr) (s : EMState (env anonymous) Δ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (normal : F.static=false) :
    run G F s r b o shared=
      ((.ok (),⟨⟨StaticEventPort.after (ts:=types) G F (declaration anonymous) legacyWords s,r⟩,b⟩),emitObserved o (log G F)) := by
  apply StaticEventPort.execute_normal G F 8 (declaration anonymous) (typed anonymous) (args anonymous) (locals anonymous)
    s (values anonymous) (evaluated G F s.2) legacyWords rfl normal [true,false,true] anonymous (shape anonymous)
    (part anonymous) (partition anonymous) [Source.intWord ReturningCall.value] rfl (fits G) r b o shared

theorem static_exact {anonymous Δ} (G : Glob (env anonymous)) (F : Fr) (s : EMState (env anonymous) Δ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (static : F.static=true) :
    run G F s r b o shared=((.error (.revert []),⟨⟨s,r⟩,b⟩),o) := by
  unfold run StaticEventPort.execute
  rw [StaticEventPort.source_static G F 8 (declaration anonymous) (typed anonymous) (args anonymous) (locals anonymous)
    s (values anonymous) (evaluated G F s.2) legacyWords rfl static]
  rfl

theorem rollback_after {anonymous Δ} (G : Glob (env anonymous)) (F : Fr) (s : EMState (env anonymous) Δ) :
    (Source.rollbackTo (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run
      (StaticEventPort.after (ts:=types) G F (declaration anonymous) legacyWords s)=(.ok (),s) := by
  change ((Except.ok () : Except Source.Halt Unit),(s.1,{s.2 with ex:=s.2.ex.undoN (s.2.ex.journal.length-s.2.ex.journal.length),logs:=
    ((F.this,G.selector (sigOf (env anonymous).layout "Mixed" types)++Source.abiLayout
      (legacyWords.map (fun w=>(false,wordBytes w))))::s.2.logs).drop ((s.2.logs.length+1)-s.2.logs.length)}))=_
  simp only [Nat.sub_self,ExecState.undoN,Nat.add_sub_cancel_left,List.drop]

theorem ordered {anonymous Δ} (G : Glob (env anonymous)) (F : Fr) (s : EMState (env anonymous) Δ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (normal : F.static=false) :
    (run G F s r b o shared).2.trace=o.trace++[.log (log G F)] := by
  rw [run_exact G F s r b o shared normal]
  rfl

theorem enclosing_revert {anonymous Δ} (G : Glob (env anonymous)) (F : Fr) (s : EMState (env anonymous) Δ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (normal : F.static=false) (data : Bytes) :
    finish s b o (companionEnter ⟨s.2.ex,r⟩ F.this F.sender F.value [] F.static)
      (run G F s r b o shared).1.2 [.log (log G F)] (.revert data)=
      (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs o.trace,data⟩,o.trace,rfl⟩) := by
  rw [run_exact G F s r b o shared normal]
  have companion := companionRollback_run (⟨s.2.ex,r⟩ : ResidualCompanion (env anonymous).layout
    (env anonymous).lay (env anonymous).lay complementCarrierOwnership) [] [] F.this F.sender F.value [] F.static
  have enc := boolEncodingRollback_run b []
  simp only [companionRunSource,companionRunResidual,ExecState.run,residualRun] at companion
  simp only [boolEncodingRun] at enc
  let f:=companionEnter (⟨s.2.ex,r⟩ : ResidualCompanion (env anonymous).layout
    (env anonymous).lay (env anonymous).lay complementCarrierOwnership) F.this F.sender F.value [] F.static
  have back : companionRollback f ⟨(StaticEventPort.after (ts:=types) G F (declaration anonymous) legacyWords s).2.ex,r⟩=⟨s.2.ex,r⟩ := companion
  have rolled : (Source.rollbackTo (f.source.mark,s.2.logs.length,s.2.heap)).run
      (StaticEventPort.after (ts:=types) G F (declaration anonymous) legacyWords s)=(.ok (),s) := rollback_after G F s
  change finish s b o f ⟨⟨StaticEventPort.after (ts:=types) G F (declaration anonymous) legacyWords s,r⟩,b⟩ [.log (log G F)] (.revert data)=_
  simp only [finish,back,enc,rolled,rollbackTrace,discardLogs,List.append_nil,returnData]
end Solidity.Yul.World.StaticEventPortControls
