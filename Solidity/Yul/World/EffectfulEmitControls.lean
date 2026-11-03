import Solidity.Yul.World.EffectfulEmitPort
import Solidity.Yul.World.GeneralReturningChecks
import Solidity.Yul.World.WorldChecks

namespace Solidity.Yul.World.EffectfulEmitControls
open Solidity.Source
open Solidity.Roadmap (Word Bytes Address)
open Solidity.Yul.Views
open Solidity.Yul.World.EffectfulEmitSource
open Solidity.Yul.World.EffectfulEmitPort

abbrev E := env false false
def owner : Address := ⟨21,by decide⟩
def other : Address := ⟨22,by decide⟩
def frame : Fr := {this:=owner,sender:=other,value:=7,static:=false,contract:="Finite"}
def initial : ExecState E.layout E.lay E.lay := ⟨⟨fun _=>Account.empty _⟩,.empty,[]⟩
def entry := ((initial.apply (.account owner (fun a=>{a with balance:=23,nonce:=17,code:=some 0}))).apply
  (.account other (fun a=>{a with balance:=31,nonce:=19}))).apply (.account other id)
def heap : Source.Heap E.layout := (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [0x70,0x71,0xff]⟩).1
def locals : Locals E.layout [.bytes .memory,.bytes .memory] := .cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)
def state : EMState E [.bytes .memory,.bytes .memory] :=
  ⟨locals,⟨entry,heap,interactionEvents GeneralReturningChecks.tracePrefix,[(other,[0x77])],⟨[.bytes .memory],.cons (.memRef rfl 0) .nil⟩⟩⟩
def residual := residualWrite (residualWrite (⟨fun _=>0xaabbcc00,[]⟩ : ResidualJournal complementCarrierOwnership)
  (complementKey true owner 9,0x9988)) (complementKey false other 9,0x887700)
def encoding := boolEncodingWrite (boolEncodingWrite boolEncodingInitial
  (ownedByteKey false owner (flag false false owner),⟨⟨2,by decide⟩,by decide⟩))
  (ownedByteKey false other (flag false false other),⟨⟨3,by decide⟩,by decide⟩)
def observed : ObservedEffects E.layout E.lay E.lay :=
  ⟨⟨entry,committedLogs GeneralReturningChecks.tracePrefix,[9,8,7]⟩,GeneralReturningChecks.tracePrefix,rfl⟩
def prepared := prepareRepresentedSlot (E:=E) (registry false false) (registry false false) (request owner) encoding
theorem ready : prepared.isSome := by decide +kernel
def plan : RepresentedSlotPlan (E:=E) (registry false false) (registry false false) (request owner) encoding := prepared.get ready

theorem before_view : beforeWord frame state residual encoding=some 0xaabbcc00 := by decide +kernel

theorem caller_prefixes : state.2.ex.journal.length=3 ∧ residual.journal.length=2 ∧ encoding.journal.length=2 ∧
    state.2.heap.get 0=some ⟨.bytes .memory,.bytes [0x70,0x71,0xff]⟩ := ⟨rfl,rfl,rfl,rfl⟩

def program : Program E :=
  {body:=fun _=>none,consts:=fun _=>none,inits:=fun _=>[],ctor:=fun _=>none,
    ctorLocals:=fun _=>[],baseArgs:=fun _=>[],contracts:=["Finite"]}
def global (pipeline : Solidity.Roadmap.Pipeline) : Glob E :=
  {prog:=program,pipeline:=pipeline,fixed:=Solidity.Yul.World.Checks.fixed,balance0:=fun _=>100,
    hasCode:=fun _ _=>false,callee:=fun _=>.answer (.success []),timestamp:=13}

theorem actual (pipeline : Solidity.Roadmap.Pipeline) :
    checkedExecute? (global pipeline) frame state residual encoding observed rfl=
      some (completed (global pipeline) frame state residual encoding plan observed) := by
  apply checked_normal (global pipeline) frame rfl state residual encoding observed rfl 0xaabbcc00 before_view rfl
    (by decide +kernel) plan
  exact Option.some_get ready

def wrongResidual := residualWrite residual (complementKey false owner 7,0x11223300)
theorem wrong_padding (pipeline : Solidity.Roadmap.Pipeline) :
    checkedExecute? (global pipeline) frame state wrongResidual encoding observed rfl=none := by
  apply checked_padding_refusal
  decide +kernel

theorem wrong_view : beforeWord frame state wrongResidual encoding=some 0x11223300 := by decide +kernel
theorem correct_wrong_patch : boolField.saveWord (0x11223300 : Word) ((boolCodec E.layout).encode (.bool true))=0x11223301 := by decide +kernel
end Solidity.Yul.World.EffectfulEmitControls
