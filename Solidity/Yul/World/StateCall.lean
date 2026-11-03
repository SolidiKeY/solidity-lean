import Solidity.Yul.World.IndexedEmitRules
import Solidity.Yul.World.FailureFuel

/-! Selected real typed persistent bool write followed by a typed read/return
or ordinary custom-error revert. Source/ABI/world definitions stay unchanged. -/
namespace Solidity.Yul.World.StateCall
open Solidity.Source
open Solidity.Roadmap (Bytes Word Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion

def flagDecl : Decl := Controls.packedTypedEnv.decls[0]
def env : Env := ⟨[ReturningCall.answerDecl,ReturningCall.errorDecl,flagDecl]⟩
def flagPath : Source.SPath := flagDecl.path

def writeOp (owner : Roadmap.Address) : Op env.layout env.lay env.lay :=
  .account owner (fun ac=>{ac with storage:=ac.storage.set flagPath (some (.bool true))})
def changed {Γ} (s : EMState env Γ) (owner : Roadmap.Address) : EMState env Γ :=
  ⟨s.1,{s.2 with ex:=s.2.ex.apply (writeOp owner)}⟩

def assignment : RExpr env [ReturningCall.uint] .bool :=
  .assign (.state flagDecl rfl rfl) (.bool true)
def readReturn : RExpr env [ReturningCall.uint] ReturningCall.uint :=
  .cond (.state flagDecl rfl)
    (.conv (.const (Q.ofInt ReturningCall.value)) (.inl (by decide)))
    (.conv (.const (Q.ofInt 0)) (.inl (by decide)))

/-- The read/conditional variant reaches the existing horizon, recorded below. -/
def readBody : RBody env :=
  ⟨[],[ReturningCall.uint],false,[ReturningCall.uint],[ReturningCall.uint],
    .stmt (.expr assignment) (.stmt (.retVal rfl readReturn (by decide)) .nil),[]⟩

def body (failed : Bool) : RBody env :=
  ⟨[],[ReturningCall.uint],false,[ReturningCall.uint],[ReturningCall.uint],
    .stmt (.expr assignment) (.stmt
      (if failed then .revertError ReturningCall.errorDecl rfl (.cons (.const (Q.ofInt ReturningCall.value)) (by decide) .nil)
       else .retVal rfl (.const (Q.ofInt ReturningCall.value)) (by decide)) .nil),[]⟩
def glob (failed : Bool) (G : Glob env) : Glob env :=
  {G with prog:={G.prog with contracts:=["Finite"],body:=fun d=>if d.name="answer" then some (body failed) else none}}
def input (G : Glob env) : Bytes := G.selector (sigOf env.layout "answer" [])
def errorData (G : Glob env) : Bytes := G.selector (sigOf env.layout "Denied" [ReturningCall.uint])++ReturningCall.output

theorem assignment_run (G : Glob env) (s : EMState env [ReturningCall.uint]) (cd : Bytes := []) :
    (Source.evalE (glob false G) (ReturningCall.child cd) 4 assignment).run s=
      (.ok (.val (.bool true)),changed s CallerFrameChecks.receiver) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem read_after_write (G : Glob env) (s : EMState env [ReturningCall.uint]) (cd : Bytes := []) :
    (Source.evalE (glob false G) (ReturningCall.child cd) 3 (.state flagDecl rfl)).run (changed s CallerFrameChecks.receiver)=
      (.ok (.val (.bool true)),changed s CallerFrameChecks.receiver) := rfl

theorem return_after_write (G : Glob env) (s : EMState env [ReturningCall.uint]) (cd : Bytes := []) :
    (Source.evalE (glob false G) (ReturningCall.child cd) 4 readReturn).run (changed s CallerFrameChecks.receiver)=
      (.ok (.val (.int (ReturningCall.value : Int) (by decide))),changed s CallerFrameChecks.receiver) := rfl

theorem resolved (failed : Bool) (G : Glob env) : (glob failed G).dispatchFn "Finite" ReturningCall.answerDecl=ReturningCall.answerDecl := rfl

theorem mods_success (G : Glob env) (s : EMState env []) (cd : Bytes := []) :
    (Source.runMods (glob false G) (ReturningCall.child cd) 6 (body false) [] (.cons (.int 0 (by decide)) .nil)).run s=
      (.ok (.cons (.int (ReturningCall.value : Int) (by decide)) .nil),changed s CallerFrameChecks.receiver) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem internal_success (G : Glob env) (s : EMState env []) (cd : Bytes := []) :
    (Source.callInternal (glob false G) (ReturningCall.child cd) 7 ReturningCall.answerDecl .nil [ReturningCall.uint]).run s=
      (.ok (.val (.int (ReturningCall.value : Int) (by decide))),changed s CallerFrameChecks.receiver) := by
  rw [Source.callInternal]
  change ((do
    let l ← Source.runMods (glob false G) (ReturningCall.child cd) 6 (body false) [] (.cons (.int 0 (by decide)) .nil)
    let out ← Source.EM.lift (Source.retVals l 0 [ReturningCall.uint])
    pure (Source.mkRet [ReturningCall.uint] out)).run s)=_
  rw [Source.Hoare.run_bind,mods_success G _ cd]
  rfl

theorem internal_revert (G : Glob env) (s : EMState env []) (cd : Bytes := []) :
    (Source.callInternal (glob true G) (ReturningCall.child cd) 7 ReturningCall.answerDecl .nil [ReturningCall.uint]).run s=
      (.error (.revert (errorData G)),changed s CallerFrameChecks.receiver) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

/-- A genuine entered-body exhaustion control, not a successful return. -/
theorem read_body_timeout (G : Glob env) (s : EMState env []) (cd : Bytes := []) :
    (Source.runMods (glob false G) (ReturningCall.child cd) 6 readBody [] (.cons (.int 0 (by decide)) .nil)).run s=
      (.error .timeout,changed s CallerFrameChecks.receiver) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

end Solidity.Yul.World.StateCall
