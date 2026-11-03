import Solidity.Yul.World.StaticEventPort
import Solidity.Yul.World.StateCallPhysical

/-! A registered event with an actual call-free typed persistent assignment as
its argument. No desired evaluation or outcome premise is used. This is an
owned observation extension; legacy Source logs remain a separate carrier. -/
namespace Solidity.Yul.World.EffectfulEmitSource
open Solidity.Source
open Solidity.Roadmap (Word Bytes Address)

def declaration (indexed anonymous : Bool) : Decl :=
  ⟨.event,"Changed",some "Finite",false,
    .event "Changed" (.cons (.eventParam (.elem .bool) indexed (some "flag")) .nil) anonymous⟩
def env (indexed anonymous : Bool) : Env := ⟨declaration indexed anonymous::StateCall.env.decls⟩
def flagDecl : Decl := StateCall.flagDecl
def path : Source.SPath := flagDecl.path

def assignment (indexed anonymous : Bool) : RExpr (env indexed anonymous) [] .bool :=
  .assign (.state flagDecl rfl rfl) (.bool true)
def args (indexed anonymous : Bool) : RConvArgs (env indexed anonymous) [] [.bool] :=
  .cons (assignment indexed anonymous) (by cases indexed <;> cases anonymous <;> decide) .nil

def statement (indexed anonymous : Bool) : RStmt (env indexed anonymous) [] false ⟨false,false⟩ [] [] :=
  .emit (declaration indexed anonymous) rfl (args indexed anonymous)
def writeOp {indexed anonymous} (owner : Address) :
    Op (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay :=
  .account owner (fun account=>{account with storage:=account.storage.set path (some (.bool true))})
def changed {indexed anonymous Γ} (F : Fr) (s : EMState (env indexed anonymous) Γ) :=
  (s.1,{s.2 with ex:=s.2.ex.apply (writeOp F.this)})
def legacy {indexed anonymous} (G : Glob (env indexed anonymous)) : Bytes :=
  G.selector (sigOf (env indexed anonymous).layout "Changed" [.bool])++
    Source.abiLayout [(false,wordBytes (1 : Word))]
def after {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) :=
  (s.1,{(changed F s).2 with logs:=(F.this,legacy G)::s.2.logs})

theorem registered (indexed anonymous : Bool) :
    (env indexed anonymous).decls.head?=some (declaration indexed anonymous) := rfl

theorem actual {indexed anonymous} (G : Glob (env indexed anonymous)) (F : Fr)
    (normal : F.static=false) (s : EMState (env indexed anonymous) []) :
    (Source.execS G F 9 0 none (statement indexed anonymous) .nil).run s=
      (.ok (.normal .nil),after G F s) := by
  cases F with
  | mk owner sender value st contract checked depth =>
    cases st
    · cases indexed <;> cases anonymous <;> cases G with
      | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl
    · cases normal

theorem static {indexed anonymous} (G : Glob (env indexed anonymous)) (F : Fr)
    (refused : F.static=true) (s : EMState (env indexed anonymous) []) :
    (Source.execS G F 9 0 none (statement indexed anonymous) .nil).run s=(.error (.revert []),s) := by
  cases F with
  | mk owner sender value st contract checked depth =>
    cases st
    · cases refused
    · cases indexed <;> cases anonymous <;> cases G with
      | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

def source {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) :=
  (Source.EM.sub (Source.L0 (env indexed anonymous))
    (Source.execS G F 9 0 none (statement indexed anonymous) .nil)).run s

theorem source_actual {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (normal : F.static=false) (s : EMState (env indexed anonymous) Γ) :
    source G F s=(.ok (.normal .nil,Source.L0 (env indexed anonymous)),after G F s) := by
  unfold source
  rw [Source.run_sub,actual G F normal]
  rfl

theorem source_static {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (refused : F.static=true) (s : EMState (env indexed anonymous) Γ) :
    source G F s=(.error (.revert []),s) := by
  unfold source
  rw [Source.run_sub,static G F refused]

/-- The local assignment is effectful; it is not admissible under the older
pure argument-evaluation contract. All other Source fields are explicit. -/
theorem fields {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) :
    (after G F s).1=s.1 ∧ (after G F s).2.heap=s.2.heap ∧
    (after G F s).2.events=s.2.events ∧ (after G F s).2.fnLocals=s.2.fnLocals ∧
    (after G F s).2.ex.journal=(s.2.ex.apply (writeOp F.this)).journal ∧
    (after G F s).2.logs=(F.this,legacy G)::s.2.logs := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
end Solidity.Yul.World.EffectfulEmitSource
