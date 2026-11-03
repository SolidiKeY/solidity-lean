import Solidity.Yul.World.SourceModifierArgument
namespace Solidity.Yul.World.SourceModifierArgumentControls
open Solidity.Source
open Solidity.Roadmap (Address)
open Solidity.Yul.World.SourceModifierArgument
open Solidity.Yul.World.SourceModifierBoundary (uint)

def owner : Address := ⟨21,by decide +kernel⟩
def other : Address := ⟨22,by decide +kernel⟩
def initial (failed : Bool) : ExecState (env failed).layout (env failed).lay (env failed).lay :=
  ⟨⟨fun _=>Account.empty _⟩,.empty,[]⟩
def entry (failed : Bool) := (initial failed).apply
  (.account owner (fun a=>{a with balance:=23,nonce:=17,code:=some 0}))
def heap (failed : Bool) : Source.Heap (env failed).layout :=
  (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [0x70,0x71,0xff]⟩).1
def caller (failed : Bool) : EMState (env failed) [] :=
  ⟨Source.L0 (env failed),⟨entry failed,heap failed,[.call other 3 [0x33] false],[(owner,[0xaa])],
    ⟨[.bytes .memory,.bytes .memory],.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)⟩⟩⟩
def frame : Fr := {this:=owner,sender:=other,value:=7,static:=false,contract:="Guarded",cd:=[0x77]}

def selected : Int := 0x12 * 2^248 + 0x99
example : IntTy.u256.lo ≤ selected ∧ selected ≤ IntTy.u256.hi := by decide +kernel
example : (wordBytes (intWord selected)).headD 0=0x12 := by decide +kernel
example : (wordBytes (intWord selected)).getLast?=some 0x99 := by decide +kernel
example : wordBytes (intWord selected)≠wordBytes (intWord 256) := by decide +kernel
example : wordBytes (intWord selected)≠[] := by decide +kernel
example : (wordBytes (intWord selected)).take 31≠wordBytes (intWord selected) := by decide +kernel
example : wordBytes (intWord selected)≠wordBytes (intWord (2^256-1)) := by decide +kernel

example (G : Glob (env false)) :
    (Source.runMods (glob G) frame 7 (body false) (body false).mods
      (locals false selected (by decide +kernel))).run (caller false)=
      (.ok (locals false selected (by decide +kernel)),caller false) :=
  actual G frame (caller false) selected (by decide +kernel) rfl
example (G : Glob (env true)) :
    (Source.runMods (glob G) frame 7 (body true) (body true).mods
      (locals true selected (by decide +kernel))).run (caller true)=
      (.error (.revert (data G selected)),caller true) :=
  actual G frame (caller true) selected (by decide +kernel) rfl
example (G : Glob (env true)) :
    (Source.runMods (glob G) frame 7 (body true) (body true).mods
      (locals true 0 (by decide +kernel))).run (caller true)=
      (.error (.revert (data G 0)),caller true) :=
  actual G frame (caller true) 0 (by decide +kernel) rfl
example (G : Glob (env true)) :
    (Source.runMods (glob G) frame 7 (body true) (body true).mods
      (locals true (2^256-1) (by decide +kernel))).run (caller true)=
      (.error (.revert (data G (2^256-1))),caller true) :=
  actual G frame (caller true) (2^256-1) (by decide +kernel) rfl
example (failed : Bool) (G : Glob (env failed)) :
    (Source.runMods (glob G) frame 4 (body failed) (body failed).mods
      (locals failed selected (by decide +kernel))).run (caller failed)=
      (.error .timeout,caller failed) :=
  entered_timeout G frame (caller failed) selected (by decide +kernel) rfl
example (failed : Bool) : (caller failed).2.fnLocals.1=[.bytes .memory,.bytes .memory] := by rfl
example (failed : Bool) : (caller failed).2.heap.get 0=some ⟨.bytes .memory,.bytes [0x70,0x71,0xff]⟩ := by rfl
example (failed : Bool) : (caller failed).2.ex.journal.length=1 := by rfl
example (failed : Bool) : (caller failed).2.events.length=1 := by rfl
example (failed : Bool) : (caller failed).2.logs.length=1 := by rfl
example : ({frame with contract:="Other"} : Fr).contract≠"Guarded" := by decide +kernel
example (G : Glob (env false)) :
    (Source.callInternal (glob G) frame 8 functionDecl (.cons (.int selected (by decide +kernel)) .nil : Vals (env false).layout [uint]) []).run (caller false)=
      (.ok (Source.mkRet [] .nil),caller false) :=
  invoked G frame (caller false) selected (by decide +kernel) rfl
example (G : Glob (env true)) :
    (Source.callInternal (glob G) {frame with static:=true} 8 functionDecl
      (.cons (.int selected (by decide +kernel)) .nil : Vals (env true).layout [uint]) []).run (caller true)=
      (.error (.revert (data G selected)),caller true) :=
  invoked G {frame with static:=true} (caller true) selected (by decide +kernel) rfl
end Solidity.Yul.World.SourceModifierArgumentControls
