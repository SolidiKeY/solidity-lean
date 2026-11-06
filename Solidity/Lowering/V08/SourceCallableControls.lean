import Solidity.Lowering.V08.SourceCallable
import Solidity.Lowering.V08.SourceEnvironmentControls

/-! Actual resolved callable fixtures. Declarations, RBody, Program and execution
are the published intrinsic source types. Supplied program bodies are not a
canonical parser/compiler/body certificate; the SourceSpec relation stays open. -/
namespace Solidity.Lowering.V08.SourceCallableControls
open Solidity Source
open SourceCallable
def savedDecl : Source.Decl :=
  { kind := .stateVar, name := "saved", scope := some "C", top := false,
    node := .stateVar (.elem .bool) none none none false "saved" .none }
def scratchDecl : Source.Decl :=
  { kind := .stateVar, name := "scratch", scope := some "C", top := false,
    node := .stateVar (.elem .bool) none none none true "scratch" .none }
def functionDecl : Source.Decl :=
  ⟨.function,"choose",some "C",false,
    .function (.ident "choose")
      (.cons (.param (.elem .bool) none (some "first"))
        (.cons (.param (.elem .bool) none (some "second")) .nil))
      (some .pub) none .nil false none (.cons (.param (.elem .bool) none (some "answer")) .nil) .none⟩
def decoyDecl : Source.Decl :=
  { functionDecl with
    name := "decoy"
    node := .function (.ident "decoy")
      (.cons (.param (.elem .bool) none (some "first"))
        (.cons (.param (.elem .bool) none (some "second")) .nil))
      (some .pub) none .nil false none (.cons (.param (.elem .bool) none (some "answer")) .nil) .none }
def E : Source.Env := ⟨[savedDecl, scratchDecl,functionDecl,decoyDecl]⟩
def sender : Roadmap.Address := ⟨1, by decide +kernel⟩
def self : Roadmap.Address := ⟨2, by decide +kernel⟩
def saved : Source.SPath := ⟨⟨some "C", "saved"⟩, []⟩
def scratch : Source.SPath := ⟨⟨some "C", "scratch"⟩, []⟩
def empty : Source.St E :=
  ⟨⟨⟨fun _ => Source.Account.empty _⟩, Source.Transient.empty, []⟩,
    Source.Heap.empty, [], [], ⟨[], .nil⟩⟩
def populated : Source.St E :=
  { empty with
    ex := empty.ex.run [
      .account sender (fun a => { a with balance := ⟨93, by decide +kernel⟩ }),
      .account self (fun a => { a with balance := ⟨7, by decide +kernel⟩, nonce := 1, code := some 0, storage := a.storage.write saved (.bool true) }),
      .transient self (fun t => t.write scratch (.bool true))]
    heap := (Source.Heap.empty.alloc ⟨.bytes .memory, .bytes [0, 0xff]⟩).1
    events := [.call self ⟨7, by decide +kernel⟩ [0, 0xff] false]
    logs := [(self, [0xab, 0, 0xff])]
    fnLocals := ⟨[.bool], .cons (.bool true) .nil⟩ }
def emptyProgram : Source.Program E :=
  { body := fun _ => none, consts := fun _ => none, inits := fun _ => [],
    ctor := fun _ => none, ctorLocals := fun _ => [], baseArgs := fun _ => [],
    contracts := ["C"] }
def baseGlobal (pipeline : Roadmap.Pipeline) : Source.Glob E :=
  { prog := emptyProgram, pipeline := pipeline, fixed := Roadmap.Controls.toyFixed,
    balance0 := fun _ => ⟨100, by decide +kernel⟩, hasCode := fun _ _ => false,
    callee := fun _ => .answer (.success []), timestamp := ⟨12345, by decide +kernel⟩ }
def frame : Source.Fr :=
  { this := self, sender := sender, value := ⟨7, by decide +kernel⟩,
    static := false, contract := "C" }
def locals : Source.Locals E.layout [.bool] := .cons (.bool true) .nil

theorem populated_snapshot :
    (populated.ex.world.accounts sender).balance.val = 93 ∧
    (populated.ex.world.accounts self).balance.val = 7 ∧
    (populated.ex.world.accounts self).nonce = 1 ∧
    (populated.ex.world.accounts self).code = some 0 ∧
    (populated.ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (populated.ex.transient.cells self).read scratch = some (.bool true) ∧
    populated.ex.journal.length = 3 ∧ populated.heap.next = 1 ∧
    populated.heap.get 0 = some ⟨.bytes .memory, .bytes [0, 0xff]⟩ ∧
    populated.events = [.call self ⟨7, by decide +kernel⟩ [0, 0xff] false] ∧
    populated.logs = [(self, [0xab, 0, 0xff])] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def binary : Roadmap.Bytes := [0,255,128]
def callerFrame : Source.Fr := { frame with checked:=false }
def bodyFirst : Source.RBody E :=
  { ps:=[.bool,.bool],rs:=[.bool],inModifier:=false,
    locals:=[.bool,.bool,.bool],out:=[.bool,.bool,.bool],
    items:=.stmt (.expr (SourceKeccak.literal binary))
      (.stmt (.retVal rfl (.local (.there (.there .here))) rfl) .nil) }
def bodySecond : Source.RBody E :=
  { bodyFirst with
    items := .stmt (.expr (SourceKeccak.literal binary))
      (.stmt (.retVal rfl (.local (.there .here)) rfl) .nil) }
def program : Source.Program E :=
  { emptyProgram with body:=fun d=>if d.name="choose" then some bodyFirst
      else if d.name="decoy" then some bodySecond else none }
def global (pipeline : Roadmap.Pipeline) : Source.Glob E :=
  { baseGlobal pipeline with prog:=program }
def params (first second : Bool) : Source.Vals E.layout [.bool,.bool] :=
  .cons (.bool first) (.cons (.bool second) .nil)
def initial (first second : Bool) : Source.Locals E.layout [.bool,.bool,.bool] :=
  .cons (.bool false) (.cons (.bool second) (.cons (.bool first) .nil))
def returned (first second : Bool) : Source.Locals E.layout [.bool,.bool,.bool] :=
  .cons (.bool first) (.cons (.bool second) (.cons (.bool first) .nil))

theorem declaration_member : functionDecl ∈ E.decls := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem signature : functionDecl.fnSig E = some ([.bool,.bool],[.bool]) := rfl
theorem selected (pipeline : Roadmap.Pipeline) :
    (global pipeline).prog.body ((global pipeline).dispatchFn callerFrame.contract functionDecl) =
      some bodyFirst := rfl
theorem selected_decoy (pipeline : Roadmap.Pipeline) :
    (global pipeline).prog.body ((global pipeline).dispatchFn callerFrame.contract decoyDecl) =
      some bodySecond := rfl

theorem zero_returns (horizon : Nat) :
    (Source.zeroVals (horizon+24) [.bool] : Source.EM E [] _).run (Source.L0 E,populated) =
      (.ok (.cons (.bool false) .nil),(Source.L0 E,populated)) := rfl

theorem reached_frame (first second : Bool) :
    (Source.Vals.cons (.bool false) .nil).onto ((params first second).onto (Source.L0 E)) =
      initial first second := rfl

theorem body_execute (pipeline : Roadmap.Pipeline) (horizon : Nat) (first second : Bool) :
    (Source.runMods (global pipeline) {callerFrame with checked:=true} (horizon+24)
      bodyFirst bodyFirst.mods (initial first second)).run (Source.L0 E,populated) =
      (.ok (returned first second),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := rfl

theorem call_execute (pipeline : Roadmap.Pipeline) (horizon : Nat) (first second : Bool) :
    (Source.callInternal (global pipeline) callerFrame (horizon+25) functionDecl
      (params first second) [.bool]).run (Source.L0 E,populated) =
      (.ok (.val (.bool first)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  complete (global pipeline) callerFrame (horizon+24) functionDecl (params first second)
    bodyFirst (selected pipeline) (.cons (.bool false) .nil) rfl (returned first second)
    (.cons (.val (.bool first)) .nil) populated populated _ (zero_returns horizon)
    (body_execute pipeline horizon first second) rfl

def setFalse : RExpr E [.bool] .bool := .assign (.local .here) (.bool false)
def arguments : RConvArgs E [.bool] [.bool,.bool] :=
  .cons setFalse rfl (.cons (.local .here) rfl .nil)
def reorderedArguments : RConvArgs E [.bool] [.bool,.bool] :=
  .cons (.local .here) rfl (.cons setFalse rfl .nil)
def expression : RExpr E [.bool] .bool := .call functionDecl signature arguments
def reorderedExpression : RExpr E [.bool] .bool := .call functionDecl signature reorderedArguments

theorem arguments_execute (global : Source.Glob E) (horizon : Nat) :
    (Source.evalConvArgs global callerFrame (horizon+25) arguments).run (locals,populated) =
      (.ok (params false false),(.cons (.bool false) .nil,populated)) := rfl

theorem reordered_arguments_execute (global : Source.Glob E) (horizon : Nat) :
    (Source.evalConvArgs global callerFrame (horizon+25) reorderedArguments).run (locals,populated) =
      (.ok (params true false),(.cons (.bool false) .nil,populated)) := rfl

theorem expression_execute (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.evalE (global pipeline) callerFrame (horizon+26) expression).run (locals,populated) =
      (.ok (.val (.bool false)),(.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) :=
  expression_complete (global pipeline) callerFrame (horizon+25) functionDecl signature arguments
    locals (.cons (.bool false) .nil) (params false false) (.val (.bool false)) populated populated _
    (arguments_execute (global pipeline) horizon) (call_execute pipeline horizon false false)

theorem reordered_expression_execute (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.evalE (global pipeline) callerFrame (horizon+26) reorderedExpression).run (locals,populated) =
      (.ok (.val (.bool true)),(.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) :=
  expression_complete (global pipeline) callerFrame (horizon+25) functionDecl signature reorderedArguments
    locals (.cons (.bool false) .nil) (params true false) (.val (.bool true)) populated populated _
    (reordered_arguments_execute (global pipeline) horizon) (call_execute pipeline horizon true false)

theorem wrong_argument_order (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) callerFrame 26 expression).run (locals,populated) ≠
    (Source.evalE (global pipeline) callerFrame 26 reorderedExpression).run (locals,populated) := by
  rw [expression_execute pipeline 0,reordered_expression_execute pipeline 0]
  intro same
  have result:=congrArg Prod.fst same
  cases result

theorem no_callee_local_leak (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) callerFrame 26 reorderedExpression).run (locals,populated) ≠
      (.ok (.val (.bool true)),(locals,SourceKeccak.afterLiteral populated binary)) := by
  rw [reordered_expression_execute pipeline 0]
  intro same
  have result:=congrArg (fun r=>r.2.1) same
  cases result

theorem retained_machine :
    (SourceKeccak.afterLiteral populated binary).ex = populated.ex ∧
    (SourceKeccak.afterLiteral populated binary).events = populated.events ∧
    (SourceKeccak.afterLiteral populated binary).logs = populated.logs ∧
    (SourceKeccak.afterLiteral populated binary).fnLocals = populated.fnLocals ∧
    (SourceKeccak.afterLiteral populated binary).heap.next = 2 ∧
    (SourceKeccak.afterLiteral populated binary).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (SourceKeccak.afterLiteral populated binary).heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem body_signature : functionDecl.fnSig E = some (bodyFirst.ps,bodyFirst.rs) := rfl

theorem checked_context : ({callerFrame with checked:=true} : Source.Fr) =
    { this:=self,sender:=sender,value:=⟨7,by decide +kernel⟩,static:=false,
      contract:="C",checked:=true,depth:=0 } := rfl

def missingGlobal (pipeline : Roadmap.Pipeline) : Source.Glob E := baseGlobal pipeline

theorem missing_expression (pipeline : Roadmap.Pipeline) :
    (Source.evalE (missingGlobal pipeline) callerFrame 26 expression).run (locals,populated) =
      (.error (.stuck "function without a body"),(.cons (.bool false) .nil,populated)) :=
  expression_failure (missingGlobal pipeline) callerFrame 25 functionDecl signature arguments
    locals (.cons (.bool false) .nil) (params false false) populated populated populated
    (.stuck "function without a body") (arguments_execute (missingGlobal pipeline) 0)
    (missing_body _ _ 24 _ _ _ rfl)

/-- A deliberately mismatched supplied body table; not SourceSpec admission. -/
def mismatchedBody : Source.RBody E :=
  { ps:=[],rs:=[],inModifier:=false,locals:=[],out:=[],items:=.nil }
def mismatchedGlobal (pipeline : Roadmap.Pipeline) : Source.Glob E :=
  { baseGlobal pipeline with prog := { emptyProgram with body:=fun _=>some mismatchedBody } }

theorem mismatched_expression (pipeline : Roadmap.Pipeline) :
    (Source.evalE (mismatchedGlobal pipeline) callerFrame 26 expression).run (locals,populated) =
      (.error (.stuck "call frame"),(.cons (.bool false) .nil,populated)) :=
  expression_failure (mismatchedGlobal pipeline) callerFrame 25 functionDecl signature arguments
    locals (.cons (.bool false) .nil) (params false false) populated populated populated
    (.stuck "call frame") (arguments_execute (mismatchedGlobal pipeline) 0)
    (wrong_frame _ _ 24 _ _ mismatchedBody rfl (.cons (.bool false) .nil) (by decide +kernel)
      populated populated (zero_returns 0))

def sourceZero : RExpr E [.bool] (.int IntTy.u256) :=
  .conv (.const (Q.ofInt 0)) (.inl rfl)
def sourceOne : RExpr E [.bool] (.int IntTy.u256) :=
  .conv (.const (Q.ofInt 1)) (.inl rfl)
def badArgument : RExpr E [.bool] .bool :=
  .compare .eq (.binary .div sourceOne sourceZero) sourceZero
def failingArguments : RConvArgs E [.bool] [.bool,.bool] :=
  .cons setFalse rfl (.cons badArgument rfl .nil)

theorem arguments_fail (pipeline : Roadmap.Pipeline) :
    (Source.evalConvArgs (global pipeline) callerFrame 25 failingArguments).run (locals,populated) =
      (.error (.revert (Source.panicData .divZero)),(.cons (.bool false) .nil,populated)) := by
  cases pipeline <;> rfl

theorem argument_failure_skips_body (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) callerFrame 26
      (.call functionDecl signature failingArguments)).run (locals,populated) =
      (.error (.revert (Source.panicData .divZero)),(.cons (.bool false) .nil,populated)) :=
  argument_failure (global pipeline) callerFrame 25 functionDecl signature failingArguments
    locals (.cons (.bool false) .nil) populated populated (.revert (Source.panicData .divZero))
    (arguments_fail pipeline)

/-- A well-typed failing return expression, rather than a fictitious failing
extraction from an already matching typed return frame. -/
def overflowReturn : RExpr E [.bool,.bool,.bool] .bool :=
  .compare .eq
    (.binary .add
      (.conv (.const (Q.ofInt 255)) (.inl (by decide +kernel)) : RExpr E _ (.int IntTy.u8))
      (.conv (.const (Q.ofInt 1)) (.inl (by decide +kernel))))
    (.conv (.const (Q.ofInt 0)) (.inl (by decide +kernel)))
def failingBody : Source.RBody E :=
  { bodyFirst with
    items:=.stmt (.expr (SourceKeccak.literal binary)) (.stmt (.retVal rfl overflowReturn rfl) .nil) }
def failingGlobal (pipeline : Roadmap.Pipeline) : Source.Glob E :=
  { baseGlobal pipeline with prog:={emptyProgram with body:=fun _=>some failingBody} }

theorem failing_return_body (pipeline : Roadmap.Pipeline) :
    (Source.runMods (failingGlobal pipeline) {callerFrame with checked:=true} 24
      failingBody failingBody.mods (initial false false)).run (Source.L0 E,populated) =
      (.error (.revert (Source.panicData .arithmetic)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  cases pipeline <;> rfl

theorem failing_return_call (pipeline : Roadmap.Pipeline) :
    (Source.callInternal (failingGlobal pipeline) callerFrame 25 functionDecl
      (params false false) [.bool]).run (Source.L0 E,populated) =
      (.error (.revert (Source.panicData .arithmetic)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  body_failure (failingGlobal pipeline) callerFrame 24 functionDecl (params false false)
    failingBody rfl (.cons (.bool false) .nil) rfl populated populated _
    (.revert (Source.panicData .arithmetic)) (zero_returns 0) (failing_return_body pipeline)

theorem failing_return_expression (pipeline : Roadmap.Pipeline) :
    (Source.evalE (failingGlobal pipeline) callerFrame 26 expression).run (locals,populated) =
      (.error (.revert (Source.panicData .arithmetic)),
        (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) :=
  expression_failure (failingGlobal pipeline) callerFrame 25 functionDecl signature arguments
    locals (.cons (.bool false) .nil) (params false false) populated populated _
    (.revert (Source.panicData .arithmetic)) (arguments_execute (failingGlobal pipeline) 0)
    (failing_return_call pipeline)

theorem call_timeout (pipeline : Roadmap.Pipeline) :
    (Source.callInternal (global pipeline) callerFrame 0 functionDecl (params true false) [.bool]).run
      (Source.L0 E,populated) = (.error .timeout,(Source.L0 E,populated)) :=
  zero_horizon _ _ _ _ _

theorem expression_timeout (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) callerFrame 0 expression).run (locals,populated) =
      (.error .timeout,(locals,populated)) := rfl

theorem argument_timeout (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) callerFrame 1 expression).run (locals,populated) =
      (.error .timeout,(locals,populated)) := rfl

theorem decoy_body_execute (pipeline : Roadmap.Pipeline) (first second : Bool) :
    (Source.runMods (global pipeline) {callerFrame with checked:=true} 24 bodySecond bodySecond.mods
      (initial first second)).run (Source.L0 E,populated) =
      (.ok (.cons (.bool second) (.cons (.bool second) (.cons (.bool first) .nil))),
        (Source.L0 E,SourceKeccak.afterLiteral populated binary)) := rfl

theorem decoy_call_execute (pipeline : Roadmap.Pipeline) :
    (Source.callInternal (global pipeline) callerFrame 25 decoyDecl (params true false) [.bool]).run
      (Source.L0 E,populated) =
      (.ok (.val (.bool false)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  complete (global pipeline) callerFrame 24 decoyDecl (params true false) bodySecond
    (selected_decoy pipeline) (.cons (.bool false) .nil) rfl
    (.cons (.bool false) (.cons (.bool false) (.cons (.bool true) .nil)))
    (.cons (.val (.bool false)) .nil) populated populated _ (zero_returns 0)
    (decoy_body_execute pipeline true false) rfl

theorem wrong_declaration (pipeline : Roadmap.Pipeline) :
    (Source.callInternal (global pipeline) callerFrame 25 functionDecl (params true false) [.bool]).run
      (Source.L0 E,populated) ≠
    (Source.callInternal (global pipeline) callerFrame 25 decoyDecl (params true false) [.bool]).run
      (Source.L0 E,populated) := by
  rw [call_execute pipeline 0,decoy_call_execute]
  intro same
  have result:=congrArg Prod.fst same
  cases result

theorem return_panic_bytes (pipeline : Roadmap.Pipeline) :
    (Source.evalE (failingGlobal pipeline) callerFrame 26 expression).run (locals,populated) =
      (.error (.revert (Semantics.encodePanic 0x11)),
        (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) := by
  rw [failing_return_expression,panicData_transport]
  rfl

theorem argument_panic_bytes (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) callerFrame 26
      (.call functionDecl signature failingArguments)).run (locals,populated) =
      (.error (.revert (Semantics.encodePanic 0x12)),(.cons (.bool false) .nil,populated)) := by
  rw [argument_failure_skips_body,panicData_transport]
  rfl

theorem wrong_failure_boundary (pipeline : Roadmap.Pipeline) :
    (Source.evalE (failingGlobal pipeline) callerFrame 26 expression).run (locals,populated) ≠
    (Source.evalE (global pipeline) callerFrame 26
      (.call functionDecl signature failingArguments)).run (locals,populated) := by
  rw [failing_return_expression,argument_failure_skips_body]
  intro same
  have wrong:=congrArg (fun result=>result.2.2.heap.next) same
  change 2=1 at wrong
  contradiction

#print axioms decoy_body_execute
#print axioms decoy_call_execute
#print axioms wrong_declaration
#print axioms return_panic_bytes
#print axioms argument_panic_bytes
#print axioms wrong_failure_boundary

#print axioms body_signature
#print axioms checked_context
#print axioms missing_expression
#print axioms mismatched_expression
#print axioms arguments_fail
#print axioms argument_failure_skips_body
#print axioms failing_return_body
#print axioms failing_return_call
#print axioms failing_return_expression
#print axioms call_timeout
#print axioms expression_timeout
#print axioms argument_timeout

#print axioms populated_snapshot
#print axioms declaration_member
#print axioms signature
#print axioms selected
#print axioms selected_decoy
#print axioms zero_returns
#print axioms reached_frame
#print axioms body_execute
#print axioms call_execute
#print axioms arguments_execute
#print axioms reordered_arguments_execute
#print axioms expression_execute
#print axioms reordered_expression_execute
#print axioms wrong_argument_order
#print axioms no_callee_local_leak
#print axioms retained_machine
end Solidity.Lowering.V08.SourceCallableControls
