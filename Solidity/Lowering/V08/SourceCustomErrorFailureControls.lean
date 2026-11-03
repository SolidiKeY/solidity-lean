import Solidity.Lowering.V08.SourceCustomErrorFailures
import Solidity.Lowering.V08.SourceCustomErrorControls
namespace Solidity.Lowering.V08.SourceCustomErrorFailureControls
open Solidity Source
open SourceCustomErrorControls

def panicArguments : RConvArgs E [.bool] [STy.bytes32,.bool,.bool] :=
  .cons (SourceKeccak.literal binary) rfl
    (.cons setFalse rfl
      (.cons (.compare .eq (.binary .div sourceOne sourceZero) sourceZero) rfl .nil))

def panicTail : RConvArgs E [.bool] [.bool,.bool] :=
  .cons setFalse rfl (.cons (.compare .eq (.binary .div sourceOne sourceZero) sourceZero) rfl .nil)

theorem converted_hash_head (pipeline : Roadmap.Pipeline) (static : Bool) :
    (do Source.getV (← Source.convRV {frame with static:=static} 11 STy.bytes32
      (← Source.evalE (global pipeline) {frame with static:=static} 11 (SourceKeccak.literal binary))) :
      Source.EM E [.bool] _).run (locals,populated) =
      (.ok (digest pipeline),(locals,SourceKeccak.afterLiteral populated binary)) := rfl

theorem changed_local_tail_failure (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalConvArgs (global pipeline) {frame with static:=static} 11 panicTail).run
      (locals,SourceKeccak.afterLiteral populated binary) =
      (.error (.revert (Source.panicData .divZero)),
        (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) := by
  cases pipeline <;> rfl

theorem argument_prefix_then_failure (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalConvArgs (global pipeline) {frame with static:=static} 12 panicArguments).run
      (locals,populated) =
      (.error (.revert (Source.panicData .divZero)),
        (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) := by
  exact SourceCustomErrorFailures.converted_tail_failure (global pipeline) {frame with static:=static} 11
    (SourceKeccak.literal binary) rfl panicTail locals locals (.cons (.bool false) .nil)
    populated _ _ (digest pipeline) (.revert (Source.panicData .divZero))
    (converted_hash_head pipeline static) (changed_local_tail_failure pipeline static)

theorem argument_failure_boundary (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 13 0 none
      (.revertError errorDeclaration rfl panicArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,populated) =
      (.error (.revert (Source.panicData .divZero)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  SourceCustomErrorFailures.arguments_failure (global pipeline) {frame with static:=static} 12
    errorDeclaration rfl panicArguments locals (.cons (.bool false) .nil) populated _
    (.revert (Source.panicData .divZero)) (argument_prefix_then_failure pipeline static)

theorem observed_argument_failure (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.EM.attempt (Source.execS (global pipeline) {frame with static:=static} 13 0 none
      (.revertError errorDeclaration rfl panicArguments : RStmt E [] false .body [.bool] [.bool]) locals)).run
      (Source.L0 E,populated) =
      (.ok (.error (.revert (Source.panicData .divZero))),
        (Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  SourceCustomErrorFailures.attempt_failure _ _ _ _ _ _ (argument_failure_boundary pipeline static)

theorem wrong_argument_reset (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 13 0 none
      (.revertError errorDeclaration rfl panicArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,populated) ≠ (.error (.revert (Source.panicData .divZero)),(Source.L0 E,populated)) := by
  rw [argument_failure_boundary]
  intro same
  have next := congrArg (fun result => result.2.2.heap.next) same
  exact (by decide +kernel : (2 : Nat) ≠ 1) next

def nestedPanic : RStmt E [] false .body [.bool] [.bool] :=
  .block (.stmt (.expr setFalse) (.stmt
    (.block (.stmt (.revertError errorDeclaration rfl panicArguments) .nil)) .nil))

theorem nested_panic_execution (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 21 0 none nestedPanic locals).run
      (Source.L0 E,populated) =
      (.error (.revert (Source.panicData .divZero)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  cases pipeline <;> rfl

theorem nested_timeout (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 2 0 none nestedPanic locals).run
      (Source.L0 E,populated) = (.error .timeout,(Source.L0 E,populated)) := rfl

theorem rethrow_binary (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 2 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl 1) .nil)).run (Source.L0 E,SourceKeccak.afterLiteral populated binary) =
      (.error (.revert binary),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  SourceCustomErrorFailures.rethrow_bytes (global pipeline) {frame with static:=static} 1 .here
    (.cons (.memRef rfl 1) .nil) (SourceKeccak.afterLiteral populated binary) 1 binary rfl rfl

/-- No catch dispatch is fabricated: this is the published canonical rethrow
path, at an actually allocated bytes object, and EM.attempt observes its halt. -/
theorem observed_rethrow (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.EM.attempt (Source.execS (global pipeline) {frame with static:=static} 2 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl 1) .nil))).run (Source.L0 E,SourceKeccak.afterLiteral populated binary) =
      (.ok (.error (.revert binary)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  SourceCustomErrorFailures.attempt_failure _ _ _ _ _ _ (rethrow_binary pipeline static)

theorem wrong_truncated_selector (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 11 0 none statement locals).run
      (Source.L0 E,populated) ≠
      (.error (.revert ([0,255,128] ++ encoded pipeline)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  rw [actual_execution]
  intro same
  have payload := Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  have length := congrArg List.length payload
  rw [exact_payload_length,List.length_append,encoded_length] at length
  exact (by decide +kernel : (100 : Nat) ≠ 99) length

/-- A real resolved struct constructor succeeds. The published encoder then
explicitly returns stuck for its reference: an unsupported aggregate encoder,
not a malformed/dangling heap or an invented EVM revert. -/
def recordDecl : Source.Decl :=
  {kind:=.struct,name:="Record",scope:=some "C",top:=false,
   node:=.struct "Record" (.structMember (.elem .bool) "flag") .nil}
def recordName : Source.DeclName := ⟨some "C","Record"⟩
def recordError : Source.Decl :=
  {kind:=.error,name:="RecordError",scope:=some "C",top:=false,
   node:=.error "RecordError" (.cons (.errorParam (.elem (.fixedBytes 32 (by decide +kernel))) none)
     (.cons (.errorParam (.userType ⟨"Record",[]⟩) none) .nil))}
def E2 : Source.Env := ⟨[savedDecl,scratchDecl,recordDecl,recordError]⟩
def empty2 : Source.St E2 :=
  ⟨⟨⟨fun _ => Source.Account.empty _⟩, Source.Transient.empty, []⟩,
    Source.Heap.empty, [], [], ⟨[], .nil⟩, Source.FailureExecution.Cursor.empty⟩
def populated2 : Source.St E2 :=
  { empty2 with
    ex := empty2.ex.run [
      .account sender (fun a => { a with balance := ⟨93, by decide +kernel⟩ }),
      .account self (fun a => { a with balance := ⟨7, by decide +kernel⟩, nonce := 1, code := some 0, storage := a.storage.write saved (.bool true) }),
      .transient self (fun t => t.write scratch (.bool true))]
    heap := (Source.Heap.empty.alloc ⟨.bytes .memory, .bytes [0, 0xff]⟩).1
    events := [.call self ⟨7, by decide +kernel⟩ [0, 0xff] false]
    logs := [(self, [0xab, 0, 0xff])]
    fnLocals := ⟨[.bool], .cons (.bool true) .nil⟩ }
def program2 : Source.Program E2 :=
  { body := fun _ => none, consts := fun _ => none, inits := fun _ => [],
    ctor := fun _ => none, ctorLocals := fun _ => [], baseArgs := fun _ => [],
    contracts := ["C"] }
def global2 (pipeline : Roadmap.Pipeline) : Source.Glob E2 :=
  { prog := program2, pipeline := pipeline, fixed := Roadmap.Controls.toyFixed,
    balance0 := fun _ => ⟨100, by decide +kernel⟩, hasCode := fun _ _ => false,
    callee := fun _ => .answer (.success []), timestamp := ⟨12345, by decide +kernel⟩ }
def frame2 : Source.Fr :=
  { this := self, sender := sender, value := ⟨7, by decide +kernel⟩,
    static := false, contract := "C" }
def locals2 : Source.Locals E2.layout [.bool] := .cons (.bool true) .nil

theorem record_populated_snapshot :
    (populated2.ex.world.accounts sender).balance.val = 93 ∧
    (populated2.ex.world.accounts self).balance.val = 7 ∧
    (populated2.ex.world.accounts self).nonce = 1 ∧
    (populated2.ex.world.accounts self).code = some 0 ∧
    (populated2.ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (populated2.ex.transient.cells self).read scratch = some (.bool true) ∧
    populated2.ex.journal.length = 3 ∧ populated2.heap.next = 1 ∧
    populated2.heap.get 0 = some ⟨.bytes .memory, .bytes [0, 0xff]⟩ ∧
    populated2.events = [.call self ⟨7, by decide +kernel⟩ [0, 0xff] false] ∧
    populated2.logs = [(self, [0xab, 0, 0xff])] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def recordExpr : RExpr E2 [.bool] (.struct .memory recordName) :=
  .structNew rfl (.cons (.assign (.local .here) (.bool false)) rfl .nil)
def recordArgs : RConvArgs E2 [.bool] [STy.bytes32,.struct .memory recordName] :=
  .cons (SourceKeccak.literal binary) rfl (.cons recordExpr rfl .nil)
def recordValues (pipeline : Roadmap.Pipeline) : Source.Vals E2.layout [STy.bytes32,.struct .memory recordName] :=
  .cons (Source.mkBytes (n:=32) (h:=by decide +kernel) (Source.wordBytes ((global2 pipeline).fixed.hash binary)))
    (.cons (.memRef rfl 2) .nil)
def recordState : Source.St E2 :=
  let middle := SourceKeccak.afterLiteral populated2 binary
  {middle with heap := (middle.heap.alloc ⟨.struct .memory recordName,.struct (.cons (.val (.bool false)) .nil)⟩).1}
def recordStatement : RStmt E2 [] false .body [.bool] [.bool] :=
  .revertError recordError rfl recordArgs

theorem record_members : recordDecl ∈ E2.decls ∧ recordError ∈ E2.decls := by
  exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

theorem record_arguments (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalConvArgs (global2 pipeline) {frame2 with static:=static} 14 recordArgs).run (locals2,populated2) =
      (.ok (recordValues pipeline),(.cons (.bool false) .nil,recordState)) := rfl

theorem record_encoding_failure (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.encodeVals {frame2 with static:=static} 14 false (recordValues pipeline).toR : Source.EM E2 [] _).run
      (Source.L0 E2,recordState) =
      (.error (.stuck "not ABI-encodable"),(Source.L0 E2,recordState)) := rfl

theorem record_execution_failure (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global2 pipeline) {frame2 with static:=static} 15 0 none recordStatement locals2).run
      (Source.L0 E2,populated2) = (.error (.stuck "not ABI-encodable"),(Source.L0 E2,recordState)) :=
  SourceCustomErrorFailures.encoding_failure (global2 pipeline) {frame2 with static:=static} 14
    recordError rfl recordArgs locals2 (.cons (.bool false) .nil) populated2 _ _
    (recordValues pipeline) (.stuck "not ABI-encodable")
    (record_arguments pipeline static) (record_encoding_failure pipeline static)

theorem record_complete_state :
    recordState.ex = populated2.ex ∧ recordState.events = populated2.events ∧
    recordState.logs = populated2.logs ∧ recordState.fnLocals = populated2.fnLocals ∧
    recordState.heap.next = 3 ∧
    recordState.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    recordState.heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ ∧
    recordState.heap.get 2 = some ⟨.struct .memory recordName,.struct (.cons (.val (.bool false)) .nil)⟩ :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem wrong_encoding_rollback (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global2 pipeline) {frame2 with static:=static} 15 0 none recordStatement locals2).run
      (Source.L0 E2,populated2) ≠ (.error (.stuck "not ABI-encodable"),(Source.L0 E2,populated2)) := by
  rw [record_execution_failure]
  intro same
  have next := congrArg (fun result => result.2.2.heap.next) same
  exact (by decide +kernel : (3 : Nat) ≠ 1) next

theorem encoding_failure_not_plain_revert (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global2 pipeline) {frame2 with static:=static} 15 0 none recordStatement locals2).run
      (Source.L0 E2,populated2) ≠ (.error (.revert []),(Source.L0 E2,recordState)) := by
  rw [record_execution_failure]
  intro same
  have status := Except.error.inj (congrArg Prod.fst same)
  cases status

theorem record_zero_horizon (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global2 pipeline) {frame2 with static:=static} 0 0 none recordStatement locals2).run
      (Source.L0 E2,populated2) = (.error .timeout,(Source.L0 E2,populated2)) := rfl

theorem nested_intrinsic_panic_bytes (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 21 0 none nestedPanic locals).run
      (Source.L0 E,populated) =
      (.error (.revert (Semantics.encodePanic 0x12)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  rw [nested_panic_execution,Solidity.Lowering.V08.panicData_transport]
  rfl

theorem rethrow_not_panic (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 2 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl 1) .nil)).run (Source.L0 E,SourceKeccak.afterLiteral populated binary) ≠
      (.error (.revert (Source.panicData .divZero)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  rw [rethrow_binary]
  intro same
  have data := Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  exact (by decide +kernel : binary ≠ Source.panicData .divZero) data

#print axioms nested_intrinsic_panic_bytes
#print axioms rethrow_not_panic

#print axioms argument_prefix_then_failure
#print axioms argument_failure_boundary
#print axioms observed_argument_failure
#print axioms wrong_argument_reset
#print axioms nested_panic_execution
#print axioms nested_timeout
#print axioms rethrow_binary
#print axioms observed_rethrow
#print axioms wrong_truncated_selector
#print axioms record_populated_snapshot
#print axioms record_members
#print axioms record_arguments
#print axioms record_encoding_failure
#print axioms record_execution_failure
#print axioms record_complete_state
#print axioms wrong_encoding_rollback
#print axioms encoding_failure_not_plain_revert
#print axioms record_zero_horizon
#print axioms converted_hash_head
#print axioms changed_local_tail_failure
end Solidity.Lowering.V08.SourceCustomErrorFailureControls
