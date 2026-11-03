import Solidity.Yul.World.SourceModifierArgument
import Solidity.Yul.World.SourceModifierFrame
namespace Solidity.Yul.World.SourceModifierFrameChecks
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

open Solidity.Yul.World.SourceModifierFrame

example (failed : Bool) (G : Glob (env failed)) (x : Int)
    (range : IntTy.u256.lo ≤ x ∧ x ≤ IntTy.u256.hi) :
    ((Source.runMods (glob G) frame 7 (body failed) (body failed).mods
      (locals failed x range)).run (caller failed)).2.2.fnLocals=(caller failed).2.fnLocals := by
  let m : RModInv (env failed) (body failed).locals := ⟨modifierDecl failed,[uint],args failed⟩
  have argument : (Source.EM.sub (locals failed x range)
      (Source.evalConvArgs (glob G) frame 6 m.args)).run (caller failed)=
      (.ok (.cons (.int x range) .nil,locals failed x range),caller failed) := by
    cases failed <;> rfl
  have found : (glob G).prog.body ((glob G).dispatchMod frame.contract m.modifier)=some (modifierBody failed) := by
    cases failed <;> rfl
  exact fnLocals_after_arguments (glob G) frame 6 (body failed) (modifierBody failed) m []
    (locals failed x range) (locals failed x range) (caller failed) (caller failed)
    (.cons (.int x range) .nil) argument found rfl

example (failed : Bool) (G : Glob (env failed)) (x : Int)
    (range : IntTy.u256.lo ≤ x ∧ x ≤ IntTy.u256.hi) :
    (Source.runMods (glob G) frame 1 (body failed) (body failed).mods
      (locals failed x range)).run (caller failed)=(.error .timeout,caller failed) := by
  let m : RModInv (env failed) (body failed).locals := ⟨modifierDecl failed,[uint],args failed⟩
  apply argument_halt (glob G) frame 0 (body failed) m []
    (locals failed x range) (caller failed) (caller failed) .timeout
  rfl

example (failed : Bool) : (caller failed).2.fnLocals.1≠(body failed).locals := by
  cases failed <;> decide
example (failed : Bool) : (caller failed).2.ex.journal.length=1 := by rfl
example (failed : Bool) : (caller failed).2.logs.length=1 := by rfl
example (failed : Bool) : (caller failed).2.events.length=1 := by rfl
example (failed : Bool) : (caller failed).2.heap.get 0=some ⟨.bytes .memory,.bytes [0x70,0x71,0xff]⟩ := by rfl
end Solidity.Yul.World.SourceModifierFrameChecks
