import Solidity.Lowering.V08.SourceDispatch
import Solidity.Lowering.V08.SourceEnvironmentControls

/-! Actual free/library internal source calls observing ambient caller fields.
No deployed library account, SourceSpec or target library-body certificate is
claimed; source roles and projected intrinsic environment observations separate. -/
namespace Solidity.Lowering.V08.SourceDispatchControls
open Solidity Source
open SourceDispatch SourceCallable
def savedDecl : Source.Decl :=
  { kind := .stateVar, name := "saved", scope := some "C", top := false,
    node := .stateVar (.elem .bool) none none none false "saved" .none }
def scratchDecl : Source.Decl :=
  { kind := .stateVar, name := "scratch", scope := some "C", top := false,
    node := .stateVar (.elem .bool) none none none true "scratch" .none }
def parameters : Source.Syn (.list .param) :=
  .cons (.param (.elem .bool) none (some "first"))
    (.cons (.param (.elem .bool) none (some "second")) .nil)
def results : Source.Syn (.list .param) :=
  .cons (.param (.elem .address) none (some "sender"))
    (.cons (.param (.elem (.int false 256 (by decide +kernel))) none (some "value")) .nil)
def freeDecl : Source.Decl :=
  ⟨.function,"ambientFree",none,true,
    .function (.ident "ambientFree") parameters none none .nil false none results .none⟩
def libraryFunction : Source.Decl :=
  ⟨.function,"ambientLib",some "L",false,
    .function (.ident "ambientLib") parameters (some .internal) none .nil false none results .none⟩
def libraryDecl : Source.Decl :=
  ⟨.library,"L",none,true,.library "L" (.cons libraryFunction.node .nil)⟩
def callerDecoy : Source.Decl :=
  { libraryFunction with
    scope:=some "C"
    node:=.function (.ident "ambientLib") parameters (some .pub) none .nil false none results .none }
def contractDecl : Source.Decl :=
  ⟨.contract,"C",none,true,.contract false "C" .none .nil
    (.cons savedDecl.node (.cons scratchDecl.node (.cons callerDecoy.node .nil)))⟩
def E : Source.Env := ⟨[contractDecl,savedDecl,scratchDecl,libraryDecl,libraryFunction,freeDecl,callerDecoy]⟩
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
def returnTypes : List STy := [.address false,.int IntTy.u256]
def params : Source.Vals E.layout [.bool,.bool] := .cons (.bool true) (.cons (.bool false) .nil)
def zeroReturns : Source.Vals E.layout returnTypes :=
  .cons (.address ⟨0,by decide +kernel⟩)
    (.cons (SourceEnvironment.sourceWord ⟨0,by decide +kernel⟩) .nil)
def actualReturns : Source.Vals E.layout returnTypes :=
  .cons (.address sender) (.cons (SourceEnvironment.sourceWord frame.value) .nil)
def body : Source.RBody E :=
  { ps:=[.bool,.bool],rs:=returnTypes,inModifier:=false,
    locals:=[.int IntTy.u256,.address false,.bool,.bool],
    out:=[.int IntTy.u256,.address false,.bool,.bool],
    items:=.stmt (.expr (SourceKeccak.literal binary))
      (.stmt (.retTuple (.cons (.magic .msg "sender" rfl) rfl
        (.cons (.magic .msg "value" rfl) rfl .nil))) .nil) }
def zeroExpr : RExpr E [.int IntTy.u256,.address false,.bool,.bool] (.int IntTy.u256) :=
  .conv (.const (Q.ofInt 0)) (.inl rfl)
def decoyBody : Source.RBody E :=
  { body with
    items:=.stmt (.expr (SourceKeccak.literal binary))
      (.stmt (.retTuple (.cons (.addressLit (List.replicate 39 0 ++ [2])) rfl
        (.cons zeroExpr rfl .nil))) .nil) }
def program : Source.Program E :=
  { emptyProgram with
    body:=fun d=>if d.name=="ambientLib" && d.scope==some "C" then some decoyBody
      else if d.name=="ambientFree" || d.name=="ambientLib" then some body else none }
def global (pipeline : Roadmap.Pipeline) : Source.Glob E :=
  { baseGlobal pipeline with prog:=program }
def result : Source.RVal E.layout (STy.ret returnTypes) :=
  .tuple actualReturns.toR

theorem free_member : freeDecl ∈ E.decls := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
theorem library_member : libraryFunction ∈ E.decls := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))
theorem library_role : DeclarationRoles.roleOf? libraryDecl = some .libraryCode := rfl
theorem free_signature : freeDecl.fnSig E = some ([.bool,.bool],returnTypes) := rfl
theorem library_signature : libraryFunction.fnSig E = some ([.bool,.bool],returnTypes) := rfl

theorem caller_chain : E.linearize frame.contract = some ["C"] := rfl

theorem selected_free (pipeline : Roadmap.Pipeline) :
    (global pipeline).prog.body ((global pipeline).dispatchFn frame.contract freeDecl) = some body := by
  rw [free_body _ _ _ rfl]
  rfl

theorem selected_library (pipeline : Roadmap.Pipeline) :
    (global pipeline).prog.body ((global pipeline).dispatchFn frame.contract libraryFunction) = some body := by
  rw [outside_body _ _ _ (by rfl)]
  rfl

theorem initialization :
    (Source.zeroVals 24 returnTypes : Source.EM E [] _).run (Source.L0 E,populated) =
      (.ok zeroReturns,(Source.L0 E,populated)) := rfl

theorem body_execute (pipeline : Roadmap.Pipeline) :
    (Source.runMods (global pipeline) {frame with checked:=true} 24 body body.mods
      (zeroReturns.onto (params.onto (Source.L0 E)))).run (Source.L0 E,populated) =
      (.ok (actualReturns.onto (params.onto (Source.L0 E))),
        (Source.L0 E,SourceKeccak.afterLiteral populated binary)) := rfl

theorem free_call (pipeline : Roadmap.Pipeline) :
    (Source.callInternal (global pipeline) frame 25 freeDecl params returnTypes).run (Source.L0 E,populated) =
      (.ok result,(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  complete (global pipeline) frame 24 freeDecl params body (selected_free pipeline) zeroReturns rfl
    (actualReturns.onto (params.onto (Source.L0 E))) actualReturns.toR populated populated _
    initialization (body_execute pipeline) rfl

theorem library_call (pipeline : Roadmap.Pipeline) :
    (Source.callInternal (global pipeline) frame 25 libraryFunction params returnTypes).run (Source.L0 E,populated) =
      (.ok result,(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  complete (global pipeline) frame 24 libraryFunction params body (selected_library pipeline) zeroReturns rfl
    (actualReturns.onto (params.onto (Source.L0 E))) actualReturns.toR populated populated _
    initialization (body_execute pipeline) rfl

def changedFrame : Source.Fr := { frame with sender:=self,value:=⟨0,by decide +kernel⟩ }
def changedReturns : Source.Vals E.layout returnTypes :=
  .cons (.address self) (.cons (SourceEnvironment.sourceWord changedFrame.value) .nil)
def changedResult : Source.RVal E.layout (STy.ret returnTypes) := .tuple changedReturns.toR

theorem changed_body_execute (pipeline : Roadmap.Pipeline) :
    (Source.runMods (global pipeline) {changedFrame with checked:=true} 24 body body.mods
      (zeroReturns.onto (params.onto (Source.L0 E)))).run (Source.L0 E,populated) =
      (.ok (changedReturns.onto (params.onto (Source.L0 E))),
        (Source.L0 E,SourceKeccak.afterLiteral populated binary)) := rfl

theorem changed_library_call (pipeline : Roadmap.Pipeline) :
    (Source.callInternal (global pipeline) changedFrame 25 libraryFunction params returnTypes).run
      (Source.L0 E,populated) =
      (.ok changedResult,(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  complete (global pipeline) changedFrame 24 libraryFunction params body (selected_library pipeline)
    zeroReturns rfl (changedReturns.onto (params.onto (Source.L0 E))) changedReturns.toR
    populated populated _ initialization (changed_body_execute pipeline) rfl

theorem decoy_body_execute (pipeline : Roadmap.Pipeline) :
    (Source.runMods (global pipeline) {frame with checked:=true} 24 decoyBody decoyBody.mods
      (zeroReturns.onto (params.onto (Source.L0 E)))).run (Source.L0 E,populated) =
      (.ok (changedReturns.onto (params.onto (Source.L0 E))),
        (Source.L0 E,SourceKeccak.afterLiteral populated binary)) := rfl

theorem caller_decoy_call (pipeline : Roadmap.Pipeline) :
    (Source.callInternal (global pipeline) frame 25 callerDecoy params returnTypes).run
      (Source.L0 E,populated) =
      (.ok changedResult,(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  complete (global pipeline) frame 24 callerDecoy params decoyBody rfl zeroReturns rfl
    (changedReturns.onto (params.onto (Source.L0 E))) changedReturns.toR
    populated populated _ initialization (decoy_body_execute pipeline) rfl

/-- A typed result observer, not a decoder or additional value/state layer. -/
def senderOf (output : Except Source.Halt (Source.RVal E.layout (STy.ret returnTypes))) : Nat :=
  match output with
  | .ok (.tuple (.cons (.val (.address sender)) _)) => sender.val
  | _ => 0

theorem wrong_ambient_context (pipeline : Roadmap.Pipeline) :
    (Source.callInternal (global pipeline) frame 25 libraryFunction params returnTypes).run
      (Source.L0 E,populated) ≠
    (Source.callInternal (global pipeline) changedFrame 25 libraryFunction params returnTypes).run
      (Source.L0 E,populated) := by
  rw [library_call,changed_library_call]
  intro same
  have wrong:=congrArg (fun r=>senderOf r.1) same
  change 1=2 at wrong
  contradiction

theorem wrong_virtual_selection (pipeline : Roadmap.Pipeline) :
    (Source.callInternal (global pipeline) frame 25 libraryFunction params returnTypes).run
      (Source.L0 E,populated) ≠
    (Source.callInternal (global pipeline) frame 25 callerDecoy params returnTypes).run
      (Source.L0 E,populated) := by
  rw [library_call,caller_decoy_call]
  intro same
  have wrong:=congrArg (fun r=>senderOf r.1) same
  change 1=2 at wrong
  contradiction

theorem complete_machine :
    (SourceKeccak.afterLiteral populated binary).ex = populated.ex ∧
    (SourceKeccak.afterLiteral populated binary).events = populated.events ∧
    (SourceKeccak.afterLiteral populated binary).logs = populated.logs ∧
    (SourceKeccak.afterLiteral populated binary).fnLocals = populated.fnLocals ∧
    (SourceKeccak.afterLiteral populated binary).heap.next = 2 ∧
    (SourceKeccak.afterLiteral populated binary).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (SourceKeccak.afterLiteral populated binary).heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem no_second_payment (pipeline : Roadmap.Pipeline) :
    (((Source.callInternal (global pipeline) frame 25 libraryFunction params returnTypes).run
      (Source.L0 E,populated)).2.2.ex.world.accounts sender).balance.val = 93 ∧
    (((Source.callInternal (global pipeline) frame 25 libraryFunction params returnTypes).run
      (Source.L0 E,populated)).2.2.ex.world.accounts self).balance.val = 7 := by
  rw [library_call]
  exact ⟨rfl,rfl⟩

theorem wrong_extra_payment (pipeline : Roadmap.Pipeline) :
    (((Source.callInternal (global pipeline) frame 25 libraryFunction params returnTypes).run
      (Source.L0 E,populated)).2.2.ex.world.accounts sender).balance.val ≠ 86 := by
  rw [(no_second_payment pipeline).1]
  decide +kernel

theorem exact_context : ({frame with checked:=true} : Source.Fr) =
    { this:=self,sender:=sender,value:=⟨7,by decide +kernel⟩,static:=false,
      contract:="C",checked:=true,depth:=0 } := rfl

/-- Actual source callable results and existing typed intrinsic environment reads.
The target state is explicitly PROJECTED, not a runtime admission/linkage claim. -/
theorem projected_observations {K : Type} {contracts : K → Contract} {C : Contract} {Δ : Ctx}
    (pipeline : Roadmap.Pipeline) (target : ContractWorld.World contracts) (state : State C Δ)
    (responses : List (Semantics.ExtKey × Semantics.ExtResult)) (input : Roadmap.Bytes) :
    (Source.callInternal (global pipeline) frame 25 libraryFunction params returnTypes).run
      (Source.L0 E,populated) =
        (.ok result,(Source.L0 E,SourceKeccak.afterLiteral populated binary)) ∧
    (Solidity.Val.simple (.env .msgSender rfl) : Solidity.Val C Δ .uint).evalT
      (EnvironmentProjection.stateEnvironment populated.ex.world target
        (SourceEnvironment.frameRequest (global pipeline) frame input) responses state) =
      .ok (EnvironmentProjection.liftAddress sender).1 ∧
    (Solidity.Val.simple (.env .msgValue rfl) : Solidity.Val C Δ .uint).evalT
      (EnvironmentProjection.stateEnvironment populated.ex.world target
        (SourceEnvironment.frameRequest (global pipeline) frame input) responses state) =
      .ok (EnvironmentProjection.liftWord frame.value) := ⟨library_call pipeline,rfl,rfl⟩

theorem library_declaration_member : libraryDecl ∈ E.decls := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- Additional ordered observation of an actual run; raw results and complete
states above are retained, not replaced by this partial observer. -/
def sourceContextObservation (pipeline : Roadmap.Pipeline) : Option (List Int) := do
  let execution := (Source.callInternal (global pipeline) frame 25 libraryFunction params returnTypes).run
    (Source.L0 E,populated)
  let raw ← execution.1.toOption
  let values ← (Source.unRet returnTypes raw).toOption
  let plain ← values.toVals.toOption
  let returned := plain.onto (Source.L0 E)
  let value ← (returned.getAt 0 (.int IntTy.u256)).toOption
  let who ← (returned.getAt 1 (.address false)).toOption
  let valueWord ← value.word
  let addressWord ← who.word
  pure [(addressWord.val:Int),(valueWord.val:Int),((global pipeline).timestamp.val:Int),
    (frame.this.val:Int),(((execution.2.2.ex.world.accounts self).balance.val):Int)]

theorem source_context_observation (pipeline : Roadmap.Pipeline) :
    sourceContextObservation pipeline = some [1,7,12345,2,7] := by
  simp only [sourceContextObservation,library_call]
  rfl

/-- An independently executed ordinary paid target read witnesses the SAME
ambient observations. This is not execution/linkage of a compiled library body. -/
theorem actual_context_agreement (pipeline : Roadmap.Pipeline) :
    sourceContextObservation pipeline = some [1,7,12345,2,7] ∧
    SourceEnvironmentControls.contextObservation.toOption =
      some (some (93,7,3,9),[1,7,12345,2,7]) :=
  ⟨source_context_observation pipeline,SourceEnvironmentControls.actual_paid_context⟩

theorem initialization_after_free :
    (Source.zeroVals 24 returnTypes : Source.EM E [] _).run
      (Source.L0 E,SourceKeccak.afterLiteral populated binary) =
      (.ok zeroReturns,(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := rfl

theorem body_after_free (pipeline : Roadmap.Pipeline) :
    (Source.runMods (global pipeline) {frame with checked:=true} 24 body body.mods
      (zeroReturns.onto (params.onto (Source.L0 E)))).run
      (Source.L0 E,SourceKeccak.afterLiteral populated binary) =
      (.ok (actualReturns.onto (params.onto (Source.L0 E))),
        (Source.L0 E,SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) binary)) := rfl

theorem library_after_free (pipeline : Roadmap.Pipeline) :
    (Source.callInternal (global pipeline) frame 25 libraryFunction params returnTypes).run
      (Source.L0 E,SourceKeccak.afterLiteral populated binary) =
      (.ok result,(Source.L0 E,SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) binary)) :=
  complete (global pipeline) frame 24 libraryFunction params body (selected_library pipeline) zeroReturns rfl
    (actualReturns.onto (params.onto (Source.L0 E))) actualReturns.toR
    (SourceKeccak.afterLiteral populated binary) (SourceKeccak.afterLiteral populated binary) _
    initialization_after_free (body_after_free pipeline) rfl

/-- Both exact statuses, results and boundaries, with the second call at the
ACTUALLY reached first boundary. No extra reset is inserted between calls. -/
theorem consecutive_calls (pipeline : Roadmap.Pipeline) :
    ((Source.callInternal (global pipeline) frame 25 freeDecl params returnTypes).run (Source.L0 E,populated),
      (Source.callInternal (global pipeline) frame 25 libraryFunction params returnTypes).run
        ((Source.callInternal (global pipeline) frame 25 freeDecl params returnTypes).run
          (Source.L0 E,populated)).2) =
    ((.ok result,(Source.L0 E,SourceKeccak.afterLiteral populated binary)),
      (.ok result,(Source.L0 E,SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) binary))) := by
  rw [free_call,library_after_free]

theorem repeated_complete_machine :
    (SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) binary).ex = populated.ex ∧
    (SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) binary).events = populated.events ∧
    (SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) binary).logs = populated.logs ∧
    (SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) binary).fnLocals = populated.fnLocals ∧
    (SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) binary).heap.next = 3 ∧
    (SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) binary).heap.get 0 =
      some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) binary).heap.get 1 =
      some ⟨.bytes .memory,.bytes binary⟩ ∧
    (SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) binary).heap.get 2 =
      some ⟨.bytes .memory,.bytes binary⟩ := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem wrong_internal_transient_reset (pipeline : Roadmap.Pipeline) :
    (((Source.callInternal (global pipeline) frame 25 libraryFunction params returnTypes).run
      (Source.L0 E,SourceKeccak.afterLiteral populated binary)).2.2.ex.transient.cells self).read scratch ≠ none := by
  rw [library_after_free]
  change (some (.bool true) : Option (Source.Val E.layout .bool)) ≠ none
  intro impossible
  cases impossible

#print axioms initialization_after_free
#print axioms body_after_free
#print axioms library_after_free
#print axioms consecutive_calls
#print axioms repeated_complete_machine
#print axioms wrong_internal_transient_reset

#print axioms library_declaration_member
#print axioms source_context_observation
#print axioms actual_context_agreement

#print axioms changed_body_execute
#print axioms changed_library_call
#print axioms decoy_body_execute
#print axioms caller_decoy_call
#print axioms wrong_ambient_context
#print axioms wrong_virtual_selection
#print axioms complete_machine
#print axioms wrong_extra_payment
#print axioms exact_context
#print axioms no_second_payment
#print axioms projected_observations

#print axioms populated_snapshot
#print axioms free_member
#print axioms library_member
#print axioms library_role
#print axioms free_signature
#print axioms library_signature
#print axioms caller_chain
#print axioms selected_free
#print axioms selected_library
#print axioms initialization
#print axioms body_execute
#print axioms free_call
#print axioms library_call
end Solidity.Lowering.V08.SourceDispatchControls
