import Solidity.Yul.World.MemoryEventPortControls

/-! Inhabited three-object Source heap with real argument and function-local
aliases. The heap is constructed, not an arbitrary-heap realization premise. -/
namespace Solidity.Yul.World.MemoryEventWitness
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.MemoryEventControls

def heap (anonymous : Bool) : Source.Heap (env anonymous).layout :=
  (((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes tag⟩).1.alloc
    ⟨.string .memory,.string label⟩).1.alloc ⟨.bytes .memory,.bytes blob⟩).1

theorem heap_found (anonymous : Bool) :
    (heap anonymous).get 0=some ⟨.bytes .memory,.bytes tag⟩ ∧
    (heap anonymous).get 1=some ⟨.string .memory,.string label⟩ ∧
    (heap anonymous).get 2=some ⟨.bytes .memory,.bytes blob⟩ := ⟨rfl,rfl,rfl⟩

def caller (anonymous : Bool)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay) : EMState (env anonymous) types :=
  ⟨locals anonymous,⟨o.effects.execution,heap anonymous,interactionEvents o.trace,
    [(CallerFrameChecks.owner,[0x76,0x77])],⟨types,locals anonymous⟩⟩⟩

def run {anonymous} (G : Glob (env anonymous)) (F : Fr)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay) :=
  MemoryEventPortControls.run G F (caller anonymous o) rfl rfl rfl r b o rfl

theorem run_exact {anonymous} (G : Glob (env anonymous)) (F : Fr)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay) (normal : F.static=false) :
    run G F r b o=
      ((.ok (),⟨⟨MemoryEventPort.after (ts:=types) G F (declaration anonymous) legacyData (caller anonymous o),r⟩,b⟩),
        emitObserved o (MemoryEventPortControls.log G F)) :=
  MemoryEventPortControls.run_exact G F (caller anonymous o) rfl rfl rfl r b o rfl normal

theorem actual_args {anonymous} (G : Glob (env anonymous)) (F : Fr)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay) :
    (Source.evalConvArgs G F 8 (args anonymous)).run (caller anonymous o)=
      (.ok (values anonymous),caller anonymous o) := evaluated G F _

theorem aliases {anonymous} (F : Fr)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay) :
    (Source.bytesOfRV F 8 (.val ((caller anonymous o).1.get .here))).run (caller anonymous o)=(.ok tag,caller anonymous o) ∧
    (Source.bytesOfRV F 8 (.val ((caller anonymous o).2.fnLocals.2.get .here))).run (caller anonymous o)=(.ok tag,caller anonymous o) := by
  exact ⟨MemoryEventTopic.bytes_read F 8 0 tag _ rfl,MemoryEventTopic.bytes_read F 8 0 tag _ rfl⟩

theorem heap_types (anonymous : Bool) :
    (heap anonymous).ty 0=some (.bytes .memory) ∧ (heap anonymous).ty 1=some (.string .memory) ∧
    (heap anonymous).ty 2=some (.bytes .memory) ∧ (heap anonymous).next=3 := ⟨rfl,rfl,rfl,rfl⟩

/-- Standalone real heap states for empty and word-boundary topic controls. -/
def single {E : Env} (base : St E) (contents : Bytes) : EMState E [] :=
  ⟨Source.L0 E,{base with heap:=(Source.Heap.empty.alloc ⟨.bytes .memory,.bytes contents⟩).1,fnLocals:=⟨[],.nil⟩}⟩

theorem any_length_topic {E} (G : Glob E) (F : Fr) (n : Nat) (base : St E) (contents : Bytes) :
    (MemoryEventTopic.topic G F n (.memRef rfl 0 : Source.Val E.layout (.bytes .memory))).run (single base contents)=
      (.ok (some (G.fixed.hash contents)),single base contents) :=
  MemoryEventTopic.bytes_topic G F n 0 contents (single base contents) rfl

theorem boundaries {E} (G : Glob E) (F : Fr) (n : Nat) (base : St E) :
    (MemoryEventTopic.topic G F n (.memRef rfl 0 : Source.Val E.layout (.bytes .memory))).run (single base [])=
      (.ok (some (G.fixed.hash [])),single base []) ∧
    (MemoryEventTopic.topic G F n (.memRef rfl 0 : Source.Val E.layout (.bytes .memory))).run (single base (List.replicate 31 0xa5))=
      (.ok (some (G.fixed.hash (List.replicate 31 0xa5))),single base (List.replicate 31 0xa5)) ∧
    (MemoryEventTopic.topic G F n (.memRef rfl 0 : Source.Val E.layout (.bytes .memory))).run (single base (List.replicate 32 0xa5))=
      (.ok (some (G.fixed.hash (List.replicate 32 0xa5))),single base (List.replicate 32 0xa5)) ∧
    (MemoryEventTopic.topic G F n (.memRef rfl 0 : Source.Val E.layout (.bytes .memory))).run (single base (List.replicate 33 0xa5))=
      (.ok (some (G.fixed.hash (List.replicate 33 0xa5))),single base (List.replicate 33 0xa5)) :=
  ⟨any_length_topic G F n base [],any_length_topic G F n base _,any_length_topic G F n base _,any_length_topic G F n base _⟩

theorem dangling {E} (G : Glob E) (F : Fr) (n : Nat) (base : St E) :
    (MemoryEventTopic.topic G F n (.memRef rfl 1 : Source.Val E.layout (.bytes .memory))).run (single base [])=
      (.error (.stuck "dangling memory reference"),single base []) :=
  MemoryEventTopic.dangling_bytes G F n 1 (single base []) rfl

theorem caller_memOK (anonymous : Bool)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay) :
    Source.MemOK (env anonymous) (heap anonymous).ty (caller anonymous o) := by
  have ok : HeapOK (E:=env anonymous) (heap anonymous) :=
    HeapOK.alloc (HeapOK.alloc (HeapOK.alloc HeapOK.empty (.bytes tag)) (.string label)) (.bytes blob)
  have shaped : HeapShaped (E:=env anonymous) (heap anonymous) :=
    HeapShaped.alloc (E:=env anonymous) (x:=⟨.bytes .memory,.bytes blob⟩)
      (HeapShaped.alloc (E:=env anonymous) (x:=⟨.string .memory,.string label⟩)
        (HeapShaped.alloc (E:=env anonymous) (x:=⟨.bytes .memory,.bytes tag⟩) HeapShaped.empty trivial) trivial) trivial
  have inner : HeapInner (E:=env anonymous) (heap anonymous) :=
    HeapInner.alloc (E:=env anonymous) (x:=⟨.bytes .memory,.bytes blob⟩)
      (HeapInner.alloc (E:=env anonymous) (x:=⟨.string .memory,.string label⟩)
        (HeapInner.alloc (E:=env anonymous) (x:=⟨.bytes .memory,.bytes tag⟩) HeapInner.empty trivial) trivial) trivial
  exact ⟨⟨⟨ok,HeapTy.Le.refl _⟩,
    ⟨⟨.bytes .memory,rfl,rfl⟩,⟨⟨.string .memory,rfl,rfl⟩,⟨trivial,⟨⟨.bytes .memory,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩,shaped,inner⟩
end Solidity.Yul.World.MemoryEventWitness
