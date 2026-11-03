import Solidity.Yul.World.StateCallStatic

namespace Solidity.Yul.World.StateCallChecks
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical
open Solidity.Yul.World.StateCallPort

def initial : ExecState env.layout env.lay env.lay := ⟨⟨fun _=>Account.empty _⟩,.empty,[]⟩
def entry := (((initial.apply (.account CallerFrameChecks.owner (fun a=>{a with balance:=11,nonce:=1,code:=some 0}))).apply
  (.account CallerFrameChecks.receiver (fun a=>{a with balance:=23,nonce:=2,code:=some 0}))).apply
  (.account CallerFrameChecks.target (fun a=>{a with nonce:=37}))).apply (.account CallerFrameChecks.owner id)
def moved := (entry.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 4))).apply
  (.account CallerFrameChecks.receiver (fun a=>a.withBalance 30))
def zeroMoved := (entry.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 11))).apply
  (.account CallerFrameChecks.receiver (fun a=>a.withBalance 23))
def heap (G : Glob env) : Source.Heap env.layout := (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes (input G)⟩).1

def placement (G : Glob env) : Placement (heap G) where
  address _:=128
  shape _:=.bytes 4
  free:=192
  free_start:=by decide
  distinct a b ha hb _ := by
    have az : a=0 := by
      by_cases z : a=0
      · exact z
      · simp only [heap,Source.Heap.alloc,Source.Heap.empty,if_neg z,Option.isSome_none,Bool.false_eq_true] at ha
    have bz : b=0 := by
      by_cases z : b=0
      · exact z
      · simp only [heap,Source.Heap.alloc,Source.Heap.empty,if_neg z,Option.isSome_none,Bool.false_eq_true] at hb
    exact az.trans bz.symm
  typed a τ d h := by
    by_cases z : a=0
    · subst a
      change some (⟨.bytes .memory,.bytes (input G)⟩ : Σ σ,Source.Data env.layout σ)=some ⟨τ,d⟩ at h
      cases h
      simpa only [input_length] using HasMemoryShape.bytes (D:=env.layout) (l:=.memory) (input G)
    · simp only [heap,Source.Heap.alloc,Source.Heap.empty,if_neg z] at h
      cases h
  starts _ _:=by decide
  ends _ _:=by decide
  separate a b ha hb hn := by
    have az : a=0 := by
      by_cases z : a=0
      · exact z
      · simp only [heap,Source.Heap.alloc,Source.Heap.empty,if_neg z,Option.isSome_none,Bool.false_eq_true] at ha
    have bz : b=0 := by
      by_cases z : b=0
      · exact z
      · simp only [heap,Source.Heap.alloc,Source.Heap.empty,if_neg z,Option.isSome_none,Bool.false_eq_true] at hb
    exact False.elim (hn (az.trans bz.symm))

def byteEntry (G : Glob env) : HeapByteEntry (heap G) := ⟨0,false,input G,rfl⟩
def memory (G : Glob env) := encodeByteHeap (placement G) [byteEntry G] (mstore (mstore (fun _=>0xa5) 64 192) 96 0)
def locals : Locals env.layout [.bytes .memory] := .cons (.memRef rfl 0) .nil

def caller (G : Glob env) : EMState env [.bytes .memory] :=
  ⟨locals,⟨entry,heap G,interactionEvents GeneralReturningChecks.tracePrefix,[(CallerFrameChecks.owner,[0x70])],⟨[.bytes .memory],locals⟩⟩⟩
def observed : ObservedEffects env.layout env.lay env.lay :=
  ⟨⟨entry,committedLogs GeneralReturningChecks.tracePrefix,[9,8,7,6]⟩,GeneralReturningChecks.tracePrefix,rfl⟩
def residual := residualWrite (initialPackedComplement (D:=env.layout) (L:=env.lay) (T:=env.lay) registry registry (fun _=>0xaabbcc00))
  (complementKey true CallerFrameChecks.owner 9,0x9988)

theorem loaded (G : Glob env) : PhysicalHeapPort.port.load (memory G) 160 4=some (input G) := by
  have actual:=PhysicalHeapPort.load_encoded (heap G) (placement G) [byteEntry G]
    (by simp only [List.map_cons,List.map_nil,List.nodup_cons,List.not_mem_nil,List.nodup_nil,not_false_eq_true,and_self])
    (byteEntry G) List.mem_cons_self (mstore (mstore (fun _=>0xa5) 64 192) 96 0)
  simpa only [byteEntry,PhysicalHeapPort.payloadOffset,placement,input_length] using actual

theorem success (G : Glob env) :
    call (CallerFrame.liftInvoke (invoke false G)) (caller G) residual encodingPrefix observed rfl (memory G) (parent (caller G))
      .call CallerFrameChecks.receiver 10000 7 160 4=some (.ok (.success ReturningCall.output),successResult (caller G) moved residual observed) :=
  call_success G _ moved rfl rfl residual rfl observed rfl _ 10000 160 4 (loaded G)

theorem reverted (G : Glob env) :
    call (CallerFrame.liftInvoke (invoke true G)) (caller G) residual encodingPrefix observed rfl (memory G) (parent (caller G))
      .call CallerFrameChecks.receiver 10000 7 160 4=some (.ok (.revert (errorData G)),revertResult G (caller G) residual observed) :=
  call_revert G _ moved rfl rfl residual rfl observed rfl _ 10000 160 4 (loaded G)

theorem outer_after_success (G : Glob env) :
    finish (caller G) encodingPrefix observed (enter (caller G) residual (parent (caller G)) .call CallerFrameChecks.receiver 7 (input G))
      (successResult (caller G) moved residual observed).1 [] (.revert [0xdd,0xee])=
      (⟨⟨caller G,residual⟩,encodingPrefix⟩,⟨⟨entry,committedLogs GeneralReturningChecks.tracePrefix,[0xdd,0xee]⟩,
        GeneralReturningChecks.tracePrefix,rfl⟩) := outer_revert G _ moved rfl residual observed _

theorem static_reverted (G : Glob env) (failed : Bool) :
    call (CallerFrame.liftInvoke (staticInvoke failed G)) (caller G) residual encodingPrefix observed rfl (memory G) (parent (caller G))
      .staticcall CallerFrameChecks.receiver 10000 0 160 4=some (.ok (.revert []),staticResult G (caller G) residual encodingPrefix observed) :=
  static_call failed G _ zeroMoved rfl rfl residual encodingPrefix observed rfl _ 10000 160 4 (loaded G)

theorem written_value (G : Glob env) :
    ((successResult (caller G) moved residual observed).1.1.1.2.ex.world.accounts CallerFrameChecks.receiver).storage.read flagPath=some (.bool true) := rfl

theorem caller_storage (G : Glob env) :
    ((successResult (caller G) moved residual observed).1.1.1.2.ex.world.accounts CallerFrameChecks.owner).storage=
      (entry.world.accounts CallerFrameChecks.owner).storage := rfl

theorem full_prefix (G : Glob env) :
    let result:=successResult (caller G) moved residual observed
    result.2.trace=GeneralReturningChecks.tracePrefix ∧ result.2.effects.returndata=ReturningCall.output ∧
    result.1.1.1.1=locals ∧ result.1.1.1.2.heap=heap G ∧ result.1.1.1.2.fnLocals=(caller G).2.fnLocals ∧
    result.1.1.1.2.logs=(caller G).2.logs ∧ result.1.1.1.2.events=(caller G).2.events ∧
    result.1.1.1.2.ex.journal.length=7 ∧ entry.journal.length=4 ∧
    result.1.1.2.journal.length=2 ∧ residual.journal.length=1 ∧ result.1.2.journal.length=2 ∧ encodingPrefix.journal.length=1 :=
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem initial_full_word :
    reencodePersistentSlot (representedBanks (E:=env) registry false encodingPrefix) ⟨entry,residual⟩
      CallerFrameChecks.receiver 7=some 0xaabbcc00 := rfl

theorem initial_bool : (entry.world.accounts CallerFrameChecks.receiver).storage.cell flagPath=none ∧
    (entry.world.accounts CallerFrameChecks.receiver).storage.read flagPath=some (.bool false) := ⟨rfl,rfl⟩

theorem padding_unchanged : (residualWrite residual plan.packed.residualUpdate).cells=residual.cells :=
  complement_preserved residual rfl

theorem aliases (G : Glob env) :
    let s:=(successResult (caller G) moved residual observed).1.1.1
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val (s.1.get .here))).run s=(.ok (input G),s) ∧
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val (s.2.fnLocals.2.get .here))).run s=(.ok (input G),s) := ⟨rfl,rfl⟩

def wrongResidual := residualWrite residual (complementKey false CallerFrameChecks.receiver 7,0x11223300)

theorem padding_refused (failed : Bool) (G : Glob env) (o : ObservedEffects env.layout env.lay env.lay)
    (frame : ResidualFrame) (target : Roadmap.Address) (gas : Word) (bytes : Bytes) (s : EMState env [])
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (bad : r.cells (complementKey false CallerFrameChecks.receiver 7)≠(0xaabbcc00 : Word)) :
    invoke failed G o frame .call target gas bytes ⟨⟨s,r⟩,b⟩=none := by
  dsimp only [invoke]
  change (if (_ : Bool) then (if r.cells (complementKey false CallerFrameChecks.receiver 7)=(0xaabbcc00 : Word)
    then (_ : Option ((Except Source.Halt Outcome × Carrier env []) × List Observation)) else none) else none)=none
  rw [if_neg bad]
  split <;> rfl

theorem wrong_padding_refused (G : Glob env) :
    invoke false G observed (enter (caller G) wrongResidual (parent (caller G)) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver 10000 (input G) ⟨⟨⟨Source.L0 env,(caller G).2⟩,wrongResidual⟩,encodingPrefix⟩=none := by
  have saved : wrongResidual.cells (complementKey false CallerFrameChecks.receiver 7)=(0x11223300 : Word) := by
    dsimp only [wrongResidual,residualWrite]
    exact residualSave_get residual.cells (complementKey false CallerFrameChecks.receiver 7) (0x11223300 : Word)
  apply padding_refused
  rw [saved]
  decide

theorem wrong_owner_refused (G : Glob env) :
    invoke false G observed (enter (caller G) residual {(parent (caller G)) with this:=CallerFrameChecks.target} .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver 10000 (input G) ⟨⟨⟨Source.L0 env,(caller G).2⟩,residual⟩,encodingPrefix⟩=none := rfl

def wrongCode (G : Glob env) : EMState env [] :=
  ⟨Source.L0 env,{(caller G).2 with ex:=entry.apply (.account CallerFrameChecks.receiver (fun a=>{a with code:=some 1}))}⟩

theorem wrong_code_refused (G : Glob env) :
    invoke false G observed (enter (wrongCode G) residual (parent (wrongCode G)) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver 10000 (input G) ⟨⟨wrongCode G,residual⟩,encodingPrefix⟩=none := rfl

theorem caller_memOK (G : Glob env) : Source.MemOK env (heap G).ty (caller G) := by
  have ok : HeapOK (E:=env) (heap G) := HeapOK.alloc HeapOK.empty (.bytes (input G))
  have shaped : HeapShaped (E:=env) (heap G) :=
    HeapShaped.alloc (E:=env) (x:=⟨.bytes .memory,.bytes (input G)⟩) HeapShaped.empty trivial
  have inner : HeapInner (E:=env) (heap G) :=
    HeapInner.alloc (E:=env) (x:=⟨.bytes .memory,.bytes (input G)⟩) HeapInner.empty trivial
  exact ⟨⟨⟨ok,HeapTy.Le.refl _⟩,⟨⟨.bytes .memory,rfl,rfl⟩,trivial⟩⟩,shaped,inner⟩

end Solidity.Yul.World.StateCallChecks
