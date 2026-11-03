import Solidity.Yul.World.MemoryEventPort

namespace Solidity.Yul.World.MemoryEventPortControls
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StaticEventEncoding (topics resultLog)
open Solidity.Yul.World.MemoryEventControls

theorem fits {anonymous} (G : Glob (env anonymous)) :
    (topics (ts:=types) G (declaration anonymous) anonymous (part G)).length<5 := by
  cases anonymous <;> simp only [topics,part,Bool.false_eq_true,if_false,if_true,List.length_cons,List.length_nil] <;> decide

def run {anonymous Δ} (G : Glob (env anonymous)) (F : Fr) (s : EMState (env anonymous) Δ)
    (tagFound : s.2.heap.get 0=some ⟨.bytes .memory,.bytes tag⟩)
    (labelFound : s.2.heap.get 1=some ⟨.string .memory,.string label⟩)
    (dataFound : s.2.heap.get 2=some ⟨.bytes .memory,.bytes blob⟩)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :=
  MemoryEventPort.execute G F 8 (declaration anonymous) (typed anonymous) (args anonymous) (locals anonymous) (local_args anonymous)
    s (values anonymous) (evaluated G F s.2) legacyData (full_codec F 8 ⟨Source.L0 (env anonymous),s.2⟩ tagFound labelFound dataFound)
    [true,true,false,false] anonymous (shape anonymous) (part G) (partition G F 8 s tagFound labelFound dataFound)
    data (data_codec G F 8 s dataFound) (fits G) r b o shared

def log {anonymous} (G : Glob (env anonymous)) (F : Fr) :=
  resultLog (ts:=types) G F (declaration anonymous) anonymous (part G) (fits G) data

theorem run_exact {anonymous Δ} (G : Glob (env anonymous)) (F : Fr) (s : EMState (env anonymous) Δ)
    (tagFound : s.2.heap.get 0=some ⟨.bytes .memory,.bytes tag⟩)
    (labelFound : s.2.heap.get 1=some ⟨.string .memory,.string label⟩)
    (dataFound : s.2.heap.get 2=some ⟨.bytes .memory,.bytes blob⟩)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (normal : F.static=false) :
    run G F s tagFound labelFound dataFound r b o shared=
      ((.ok (),⟨⟨MemoryEventPort.after (ts:=types) G F (declaration anonymous) legacyData s,r⟩,b⟩),emitObserved o (log G F)) :=
  MemoryEventPort.execute_normal G F 8 (declaration anonymous) (typed anonymous) (args anonymous) (locals anonymous) (local_args anonymous)
    s (values anonymous) (evaluated G F s.2) legacyData (full_codec F 8 ⟨Source.L0 (env anonymous),s.2⟩ tagFound labelFound dataFound)
    [true,true,false,false] anonymous (shape anonymous) (part G) (partition G F 8 s tagFound labelFound dataFound)
    data (data_codec G F 8 s dataFound) (fits G) r b o shared normal

theorem static_exact {anonymous Δ} (G : Glob (env anonymous)) (F : Fr) (s : EMState (env anonymous) Δ)
    (tagFound : s.2.heap.get 0=some ⟨.bytes .memory,.bytes tag⟩)
    (labelFound : s.2.heap.get 1=some ⟨.string .memory,.string label⟩)
    (dataFound : s.2.heap.get 2=some ⟨.bytes .memory,.bytes blob⟩)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (static : F.static=true) :
    run G F s tagFound labelFound dataFound r b o shared=((.error (.revert []),⟨⟨s,r⟩,b⟩),o) := by
  unfold run MemoryEventPort.execute
  rw [MemoryEventPort.source_static G F 8 (declaration anonymous) (typed anonymous) (args anonymous) (locals anonymous)
    s (values anonymous) (evaluated G F s.2) legacyData (full_codec F 8 ⟨Source.L0 (env anonymous),s.2⟩ tagFound labelFound dataFound) static]
  rfl

theorem wrong_preimage : tag≠wordBytes (Source.toWord tag.length)++pad32 tag := by decide

theorem cross_word : blob.length=33 ∧ data.length=160 := by
  constructor
  · simp only [blob,List.length_map,List.length_range]
  · change ((wordBytes (Source.intWord ReturningCall.value)++wordBytes (Source.toWord 64)++[])++
      ((wordBytes (Source.toWord blob.length)++pad32 blob)++[])).length=160
    simp only [List.length_append,wordBytes_length,List.length_nil,Nat.add_zero]
    change 32+32+(32+(pad32 blob).length)=160
    decide

theorem rollback_after {anonymous Δ} (G : Glob (env anonymous)) (F : Fr) (s : EMState (env anonymous) Δ) :
    (Source.rollbackTo (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run
      (MemoryEventPort.after (ts:=types) G F (declaration anonymous) legacyData s)=(.ok (),s) := by
  change ((Except.ok () : Except Source.Halt Unit),(s.1,{s.2 with ex:=s.2.ex.undoN (s.2.ex.journal.length-s.2.ex.journal.length),logs:=((F.this,G.selector (sigOf (env anonymous).layout "Payload" types)++legacyData)::s.2.logs).drop ((s.2.logs.length+1)-s.2.logs.length)}))=_
  simp only [Nat.sub_self,ExecState.undoN,Nat.add_sub_cancel_left,List.drop]

theorem enclosing_revert {anonymous Δ} (G : Glob (env anonymous)) (F : Fr) (s : EMState (env anonymous) Δ)
    (tagFound : s.2.heap.get 0=some ⟨.bytes .memory,.bytes tag⟩)
    (labelFound : s.2.heap.get 1=some ⟨.string .memory,.string label⟩)
    (dataFound : s.2.heap.get 2=some ⟨.bytes .memory,.bytes blob⟩)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (normal : F.static=false) (bytes : Bytes) :
    finish s b o (companionEnter ⟨s.2.ex,r⟩ F.this F.sender F.value [] F.static)
      (run G F s tagFound labelFound dataFound r b o shared).1.2 [.log (log G F)] (.revert bytes)=
      (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs o.trace,bytes⟩,o.trace,rfl⟩) := by
  rw [run_exact G F s tagFound labelFound dataFound r b o shared normal]
  have companion := companionRollback_run (⟨s.2.ex,r⟩ : ResidualCompanion (env anonymous).layout
    (env anonymous).lay (env anonymous).lay complementCarrierOwnership) [] [] F.this F.sender F.value [] F.static
  have enc := boolEncodingRollback_run b []
  simp only [companionRunSource,companionRunResidual,ExecState.run,residualRun] at companion
  simp only [boolEncodingRun] at enc
  let f:=companionEnter (⟨s.2.ex,r⟩ : ResidualCompanion (env anonymous).layout
    (env anonymous).lay (env anonymous).lay complementCarrierOwnership) F.this F.sender F.value [] F.static
  have back : companionRollback f ⟨(MemoryEventPort.after (ts:=types) G F (declaration anonymous) legacyData s).2.ex,r⟩=⟨s.2.ex,r⟩ := companion
  have rolled : (Source.rollbackTo (f.source.mark,s.2.logs.length,s.2.heap)).run
      (MemoryEventPort.after (ts:=types) G F (declaration anonymous) legacyData s)=(.ok (),s) := rollback_after G F s
  change finish s b o f ⟨⟨MemoryEventPort.after (ts:=types) G F (declaration anonymous) legacyData s,r⟩,b⟩ [.log (log G F)] (.revert bytes)=_
  simp only [finish,back,enc,rolled,rollbackTrace,discardLogs,List.append_nil,returnData]
end Solidity.Yul.World.MemoryEventPortControls
