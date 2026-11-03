import Solidity.Yul.World.MemoryEventSource

namespace Solidity.Yul.World.MemoryEventControls
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StaticEventEncoding (Split metadata topics resultLog)
open Solidity.Yul.World.MemoryEventTopic

def tag : Bytes := [0xa1,0,0xfe]
def label : Bytes := [0xce,0xbc,0xce,0xbb]
def blob : Bytes := (List.range 33).map UInt8.ofNat

def declaration (anonymous : Bool) : Decl := ⟨.event,"Payload",some "Finite",false,
  .event "Payload" (.cons (.eventParam (.elem .bytes) true (some "tag"))
    (.cons (.eventParam (.elem .string) true (some "label"))
      (.cons (.eventParam (.elem (.int false 256 (by decide))) false (some "value"))
        (.cons (.eventParam (.elem .bytes) false (some "data")) .nil)))) anonymous⟩
def env (anonymous : Bool) : Env := ⟨declaration anonymous::ReturningCall.env.decls⟩
def types : List STy := [.bytes .memory,.string .memory,ReturningCall.uint,.bytes .memory]
def values (anonymous : Bool) : Vals (env anonymous).layout types :=
  .cons (.memRef rfl 0) (.cons (.memRef rfl 1) (.cons (.int (t:=IntTy.u256) ReturningCall.value (by decide)) (.cons (.memRef rfl 2) .nil)))
def locals (anonymous : Bool) : Locals (env anonymous).layout types :=
  .cons (.memRef rfl 0) (.cons (.memRef rfl 1) (.cons (.int (t:=IntTy.u256) ReturningCall.value (by decide)) (.cons (.memRef rfl 2) .nil)))
def args (anonymous : Bool) : RConvArgs (env anonymous) types types :=
  .cons (.local .here) (by cases anonymous <;> decide)
    (.cons (.local (.there .here)) (by cases anonymous <;> decide)
      (.cons (.local (.there (.there .here))) (by cases anonymous <;> decide)
        (.cons (.local (.there (.there (.there .here)))) (by cases anonymous <;> decide) .nil)))

def part {anonymous} (G : Glob (env anonymous)) : Split (env anonymous).layout :=
  ([G.fixed.hash tag,G.fixed.hash label],⟨[ReturningCall.uint,.bytes .memory],
    .cons (.int (t:=IntTy.u256) ReturningCall.value (by decide)) (.cons (.memRef rfl 2) .nil)⟩)

def allParts : List (Bool × Bytes) := [(true,tag),(true,label),
  (false,wordBytes (Source.intWord ReturningCall.value)),(true,blob)]
def dataParts : List (Bool × Bytes) := [(false,wordBytes (Source.intWord ReturningCall.value)),(true,blob)]
def legacyData : Bytes := Source.abiLayout allParts
def data : Bytes := Source.abiLayout dataParts

theorem typed (anonymous : Bool) : (declaration anonymous).paramTys (env anonymous)=some types := rfl

theorem registered (anonymous : Bool) : (env anonymous).decls.head?=some (declaration anonymous) := rfl

theorem shape (anonymous : Bool) : metadata (declaration anonymous)=some ([true,true,false,false],anonymous) := by
  cases anonymous <;> simp only [metadata,declaration,StaticEventEncoding.indexedFlags]

theorem local_args (anonymous : Bool) : LocalEventBoundary.LocalArguments (args anonymous) := by
  unfold args
  repeat constructor

theorem evaluated {anonymous} (G : Glob (env anonymous)) (F : Fr) (st : St (env anonymous)) :
    (Source.evalConvArgs G F 8 (args anonymous)).run ⟨locals anonymous,st⟩=(.ok (values anonymous),⟨locals anonymous,st⟩) := by
  cases anonymous <;> cases G with
  | mk p pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem partition {anonymous Γ} (G : Glob (env anonymous)) (F : Fr) (n : Nat) (s : EMState (env anonymous) Γ)
    (tagFound : s.2.heap.get 0=some ⟨.bytes .memory,.bytes tag⟩)
    (labelFound : s.2.heap.get 1=some ⟨.string .memory,.string label⟩)
    (dataFound : s.2.heap.get 2=some ⟨.bytes .memory,.bytes blob⟩) :
    (MemoryEventEncoding.split G F n [true,true,false,false] (values anonymous)).run s=(.ok (some (part G)),s) := by
  simp only [values,MemoryEventEncoding.split,Source.Hoare.run_bind,
    bytes_topic G F n 0 tag s tagFound,string_topic G F n 1 label s labelFound,
    MemoryEventTopic.word G F n (.int (t:=IntTy.u256) ReturningCall.value (by decide)) (Source.intWord ReturningCall.value) rfl s,
    bytes_topic G F n 2 blob s dataFound]
  rfl

theorem data_codec {anonymous Γ} (G : Glob (env anonymous)) (F : Fr) (n : Nat) (s : EMState (env anonymous) Γ)
    (dataFound : s.2.heap.get 2=some ⟨.bytes .memory,.bytes blob⟩) :
    (Source.encodeVals F n false (part G).2.2.toR).run s=(.ok data,s) := by
  simp only [Source.encodeVals,part,Vals.toR,Source.encodeParts,Source.Hoare.run_bind]
  rw [StaticEventArgs.encodeOne_word F n (.int (t:=IntTy.u256) ReturningCall.value (by decide)) (Source.intWord ReturningCall.value) rfl s]
  dsimp only
  rw [bytes_codec F n 2 blob s dataFound]
  rfl

theorem full_codec {anonymous Γ} (F : Fr) (n : Nat) (s : EMState (env anonymous) Γ)
    (tagFound : s.2.heap.get 0=some ⟨.bytes .memory,.bytes tag⟩)
    (labelFound : s.2.heap.get 1=some ⟨.string .memory,.string label⟩)
    (dataFound : s.2.heap.get 2=some ⟨.bytes .memory,.bytes blob⟩) :
    (Source.encodeVals F n false (values anonymous).toR).run s=(.ok legacyData,s) := by
  simp only [Source.encodeVals,values,Vals.toR,Source.encodeParts,Source.Hoare.run_bind]
  rw [bytes_codec F n 0 tag s tagFound]
  dsimp only
  rw [string_codec F n 1 label s labelFound]
  dsimp only
  rw [StaticEventArgs.encodeOne_word F n (.int (t:=IntTy.u256) ReturningCall.value (by decide)) (Source.intWord ReturningCall.value) rfl s]
  dsimp only
  rw [bytes_codec F n 2 blob s dataFound]
  rfl
end Solidity.Yul.World.MemoryEventControls
