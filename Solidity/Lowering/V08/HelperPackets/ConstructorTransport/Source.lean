import Solidity.Lowering.V08.CreationPremises

/-! H26 explicit saved initializer followed by a local capture and two writes.
No automatic initialization or admission producer is inferred. -/
namespace Solidity.Lowering.V08.HelperPackets.ConstructorTransport
open Solidity Source
open Solidity.Lowering.V07

def savedSyntax : Syn (.part false) :=
  .stateVar Source.Examples.u256 none none none false "saved" (.some (.lit (.num (.dec 7 0 0))))
def capturedSyntax : Syn (.part false) :=
  .stateVar Source.Examples.u256 none none none false "captured" .none
def constructorSyntax : Syn (.part false) :=
  .constructor ConstructorScalarTransport.params .nil false none (.block
    (.cons (.stmtItem (.simpleStmt (.declVar (.varDecl Source.Examples.u256 none "old")
      (.some (.ident "saved")))))
    (.cons (.stmtItem (.simpleStmt (.exprStmt (.assign .assign (.ident "saved") (.ident "n")))))
    (.cons (.stmtItem (.simpleStmt (.exprStmt (.assign .assign (.ident "captured") (.ident "old"))))) .nil))))
def unit : Syn .unit := .unit (.cons (.contract false "Cell" .none .nil
  (.cons savedSyntax (.cons capturedSyntax (.cons constructorSyntax .nil)))) .nil)
def E : Source.Env := unit.env
def savedDecl : Source.Decl := ⟨.stateVar,"saved",some "Cell",false,savedSyntax⟩
def capturedDecl : Source.Decl := ⟨.stateVar,"captured",some "Cell",false,capturedSyntax⟩
abbrev uint := Source.STy.int Source.IntTy.u256

def body : Source.RBody E :=
  ⟨[uint],[],false,[uint],[uint,uint],
    .stmt (.declInit (.state savedDecl rfl) rfl)
    (.stmt (.expr (.assign (.state savedDecl rfl rfl) (.local (.there .here))))
    (.stmt (.expr (.assign (.state capturedDecl rfl rfl) (.local .here))) .nil)),[]⟩
def program : Source.Program E :=
  {body:=fun _ => none,consts:=fun _ => none,
    inits:=fun c => if c="Cell" then [⟨savedDecl,uint,rfl,.conv (.const (Source.Q.ofInt 7)) (.inl (Source.SemanticsExamples.lit_ok _ _ 7 (by decide +kernel)))⟩] else [],
    ctor:=fun c => if c="Cell" then some body else none,
    ctorLocals:=fun _ => [uint],baseArgs:=fun _ => [],contracts:=["Cell"]}

def global (p : Roadmap.Pipeline) : Source.Glob E :=
  {prog:=program,pipeline:=p,fixed:=Source.SemanticsExamples.toyFixed,
    balance0:=fun _ => ConstructorScalarTransport.word 93,hasCode:=fun _ _ => false,
    callee:=fun _ => .answer (.success []),timestamp:=ConstructorScalarTransport.word 0}
def frame : Source.Fr := {ConstructorScalarTransport.frame with value:=ConstructorScalarTransport.word 0}
abbrev range := ConstructorScalarTransport.range

def locals (n : Int) (h : range n) : Source.Locals E.layout [uint] := .cons (.int n h) .nil

def initial (bytes : Roadmap.Bytes) : Source.St E :=
  {Source.St.init E with
    ex:=(Source.St.init E).ex.run [
      .account frame.sender (fun a => {a with balance:=ConstructorScalarTransport.word 93,nonce:=3}),
      .account frame.this (fun a =>
        {a with
          balance:=ConstructorScalarTransport.word 5
          nonce:=1
          storage:=(a.storage.write savedDecl.path (.int 0 (by decide +kernel))).write
            capturedDecl.path (.int 0 (by decide +kernel))})]
    heap:=(Source.Heap.empty.alloc ⟨.bytes .memory,.bytes bytes⟩).1
    events:=[.call frame.sender (ConstructorScalarTransport.word 0) bytes false]
    logs:=[(frame.this,bytes),(frame.sender,[0,255])]
    fnLocals:=⟨[.bool],.cons (.bool true) .nil⟩}
def write (s : Source.St E) (d : Source.Decl) (n : Int) (h : range n)
    (hd : E.lay frame.this d.path = uint := by rfl) : Source.St E :=
  {s with ex:=s.ex.apply (.account frame.this
    (fun a => {a with storage:=a.storage.write d.path (hd.symm ▸ (Source.Val.int n h : Source.Val E.layout uint))}))}
def initialized (bytes : Roadmap.Bytes) := write (initial bytes) savedDecl 7 (by decide +kernel)
def reached (bytes : Roadmap.Bytes) (n : Int) (h : range n) :=
  write (write (initialized bytes) savedDecl n h) capturedDecl 7 (by decide +kernel)

theorem initialization_actual (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.runInits (global p) frame 16 (program.inits "Cell")).run
      (Source.L0 E,initial bytes) = (.ok (),(Source.L0 E,initialized bytes)) := by
  cases p <;> rfl

theorem source_actual (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (n : Int) (h : range n) :
    (Source.construct (global p) frame 16 "Cell" (locals n h)).run
      (Source.L0 E,initial bytes) = (.ok (),(Source.L0 E,reached bytes n h)) := by
  cases p <;> rfl

theorem source_saved (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    ((reached bytes n h).ex.world.accounts frame.this).storage.read savedDecl.path = some (.int n h) := by rfl

theorem source_captured (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    ((reached bytes n h).ex.world.accounts frame.this).storage.read capturedDecl.path =
      some (.int 7 (by decide +kernel)) := by rfl

theorem source_retained (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    (reached bytes n h).heap = (initial bytes).heap ∧
    (reached bytes n h).events = (initial bytes).events ∧
    (reached bytes n h).logs = (initial bytes).logs ∧
    (reached bytes n h).fnLocals = (initial bytes).fnLocals ∧
    (reached bytes n h).ex.journal.length = 5 := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem source_static (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    (Source.construct (global p) {frame with static:=true} 16 "Cell" (locals n h)).run
      (Source.L0 E,initial bytes) = (.error (.revert []),(Source.L0 E,initial bytes)) := by
  cases p <;> rfl

theorem source_timeout (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    (Source.construct (global p) frame 0 "Cell" (locals n h)).run
      (Source.L0 E,initial bytes) = (.error .timeout,(Source.L0 E,initial bytes)) := by
  cases p <;> rfl
end Solidity.Lowering.V08.HelperPackets.ConstructorTransport
