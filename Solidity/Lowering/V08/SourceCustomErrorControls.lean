import Solidity.Lowering.V08.SourceCustomErrors
import Solidity.Lowering.V08.SourceEnvironmentControls
namespace Solidity.Lowering.V08.SourceCustomErrorControls
open Solidity Source
open SourceCustomErrors
def savedDecl : Source.Decl :=
  { kind := .stateVar, name := "saved", scope := some "C", top := false,
    node := .stateVar (.elem .bool) none none none false "saved" .none }
def scratchDecl : Source.Decl :=
  { kind := .stateVar, name := "scratch", scope := some "C", top := false,
    node := .stateVar (.elem .bool) none none none true "scratch" .none }
def errorDeclaration : Source.Decl :=
  { kind:=.error,name:="Bad",scope:=some "C",top:=false,
    node:=.error "Bad"
      (.cons (.errorParam (.elem (.fixedBytes 32 (by decide +kernel))) (some "digest"))
        (.cons (.errorParam (.elem .bool) (some "set"))
          (.cons (.errorParam (.elem .bool) (some "read")) .nil))) }
def E : Source.Env := ⟨[savedDecl,scratchDecl,errorDeclaration]⟩
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
def program : Source.Program E :=
  { body := fun _ => none, consts := fun _ => none, inits := fun _ => [],
    ctor := fun _ => none, ctorLocals := fun _ => [], baseArgs := fun _ => [],
    contracts := ["C"] }
def global (pipeline : Roadmap.Pipeline) : Source.Glob E :=
  { prog := program, pipeline := pipeline, fixed := Roadmap.Controls.toyFixed,
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
def setFalse : RExpr E [.bool] .bool := .assign (.local .here) (.bool false)
def arguments : RConvArgs E [.bool] [STy.bytes32,.bool,.bool] :=
  .cons (SourceKeccak.literal binary) rfl
    (.cons setFalse rfl (.cons (.local .here) rfl .nil))
def statement : RStmt E [] false .body [.bool] [.bool] :=
  .revertError errorDeclaration rfl arguments

theorem error_member : errorDeclaration ∈ E.decls := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem assign_false (pipeline : Roadmap.Pipeline) (static : Bool) (horizon : Nat)
    (state : Source.St E) :
    (Source.evalE (global pipeline) {frame with static := static} (horizon+3) setFalse).run
      (locals,state) = (.ok (.val (.bool false)),(.cons (.bool false) .nil,state)) := rfl

theorem read_false (pipeline : Roadmap.Pipeline) (static : Bool) (horizon : Nat)
    (state : Source.St E) :
    (Source.evalE (global pipeline) {frame with static := static} (horizon+1)
      (.local .here : RExpr E [.bool] .bool)).run (.cons (.bool false) .nil,state) =
      (.ok (.val (.bool false)),(.cons (.bool false) .nil,state)) := rfl

def digest (pipeline : Roadmap.Pipeline) : Source.Val E.layout STy.bytes32 :=
  Source.mkBytes (n:=32) (h:=by decide +kernel) (Source.wordBytes ((global pipeline).fixed.hash binary))
def values (pipeline : Roadmap.Pipeline) : Source.Vals E.layout [STy.bytes32,.bool,.bool] :=
  .cons (digest pipeline) (.cons (.bool false) (.cons (.bool false) .nil))

theorem arguments_execute (pipeline : Roadmap.Pipeline) (static : Bool) (horizon : Nat) :
    (Source.evalConvArgs (global pipeline) {frame with static := static} (horizon+10) arguments).run
      (locals,populated) =
      (.ok (values pipeline),(.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) := by
  simp only [arguments, Source.evalConvArgs, Source.convRV, Source.getV, setFalse,
    ↓reduceDIte, bind, pure, ExceptT.bind, ExceptT.pure,
    ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind]
  rfl

def digestWord (pipeline : Roadmap.Pipeline) : Roadmap.Word :=
  Source.toWord (Source.beValue
    (Source.fitBytes 32 (Source.wordBytes ((global pipeline).fixed.hash binary)) ++
      List.replicate (32-(Source.fitBytes 32 (Source.wordBytes ((global pipeline).fixed.hash binary))).length) 0))
def zeroWord : Roadmap.Bytes := Source.wordBytes (Source.toWord 0)
def oneWord : Roadmap.Bytes := Source.wordBytes (Source.toWord 1)
def encoded (pipeline : Roadmap.Pipeline) : Roadmap.Bytes :=
  Source.abiLayout [(false,Source.wordBytes (digestWord pipeline)),(false,zeroWord),(false,zeroWord)]

theorem encoding_execute (pipeline : Roadmap.Pipeline) (static : Bool) (horizon : Nat) :
    (Source.encodeVals {frame with static:=static} (horizon+10) false (values pipeline).toR :
      Source.EM E [] _).run (Source.L0 E,SourceKeccak.afterLiteral populated binary) =
      (.ok (encoded pipeline),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := rfl

theorem signature_utf8 : "Bad(bytes32,bool,bool)".toUTF8.toList = [66,97,100,40,98,121,116,101,115,51,50,44,98,111,111,108,44,98,111,111,108,41] := by
  change ((⟨#[66,97,100,40,98,121,116,101,115,51,50,44,98,111,111,108,44,98,111,111,108,41]⟩ : ByteArray).toList) = _
  have size : (⟨#[66,97,100,40,98,121,116,101,115,51,50,44,98,111,111,108,44,98,111,111,108,41]⟩ : ByteArray).size = 22 := rfl
  unfold ByteArray.toList
  repeat' (rw [ByteArray.toList.loop]; simp only [size,Nat.reduceLT,Nat.reduceAdd,if_true,if_false])
  rfl

theorem signature_bytes :
    Source.asciiBytes (Source.sigOf E.layout errorDeclaration.name [STy.bytes32,.bool,.bool]) =
      "Bad(bytes32,bool,bool)".toUTF8.toList := by
  rw [signature_utf8]
  rfl

theorem actual_execution (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 11 0 none statement locals).run
      (Source.L0 E,populated) =
      (.error (.revert ((global pipeline).selector
        (Source.sigOf E.layout errorDeclaration.name [STy.bytes32,.bool,.bool]) ++ encoded pipeline)),
        (Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  execute (global pipeline) {frame with static:=static} 10 errorDeclaration rfl arguments
    locals (.cons (.bool false) .nil) populated _ _ (values pipeline) (encoded pipeline)
    (arguments_execute pipeline static 0) (encoding_execute pipeline static 0)

theorem intrinsic_selector_payload (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 11 0 none statement locals).run
      (Source.L0 E,populated) =
      (.error (.revert (Semantics.selectorBytes (Semantics.customSelector "Bad(bytes32,bool,bool)") ++ encoded pipeline)),
        (Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  rw [actual_execution,selector_of_bytes (global pipeline) Roadmap.Controls.toyFixed_keccak
    _ "Bad(bytes32,bool,bool)" signature_bytes]

theorem encoded_length (pipeline : Roadmap.Pipeline) : (encoded pipeline).length = 96 := by
  simp only [encoded,SourceEmit.three_static,List.length_append,zeroWord,Source.wordBytes_length]

theorem exact_payload_length (pipeline : Roadmap.Pipeline) :
    ((global pipeline).selector (Source.sigOf E.layout errorDeclaration.name [STy.bytes32,.bool,.bool]) ++
      encoded pipeline).length = 100 := by
  rw [List.length_append,SourceCustomErrors.selector_length,encoded_length]

theorem complete_machine :
    (SourceKeccak.afterLiteral populated binary).ex = populated.ex ∧
    (SourceKeccak.afterLiteral populated binary).events = populated.events ∧
    (SourceKeccak.afterLiteral populated binary).logs = populated.logs ∧
    (SourceKeccak.afterLiteral populated binary).fnLocals = populated.fnLocals ∧
    (SourceKeccak.afterLiteral populated binary).heap.next = 2 ∧
    (SourceKeccak.afterLiteral populated binary).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (SourceKeccak.afterLiteral populated binary).heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem zero_horizon (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) frame 0 0 none statement locals).run (Source.L0 E,populated) =
      (.error .timeout,(Source.L0 E,populated)) := rfl

def reversedArguments : RConvArgs E [.bool] [STy.bytes32,.bool,.bool] :=
  .cons (SourceKeccak.literal binary) rfl (.cons (.local .here) rfl (.cons setFalse rfl .nil))
def reversedValues (pipeline : Roadmap.Pipeline) : Source.Vals E.layout [STy.bytes32,.bool,.bool] :=
  .cons (digest pipeline) (.cons (.bool true) (.cons (.bool false) .nil))
def reversedEncoded (pipeline : Roadmap.Pipeline) : Roadmap.Bytes :=
  Source.abiLayout [(false,Source.wordBytes (digestWord pipeline)),(false,oneWord),(false,zeroWord)]

theorem reversed_arguments (pipeline : Roadmap.Pipeline) :
    (Source.evalConvArgs (global pipeline) frame 10 reversedArguments).run (locals,populated) =
      (.ok (reversedValues pipeline),(.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) := rfl

theorem reversed_encoding (pipeline : Roadmap.Pipeline) :
    (Source.encodeVals frame 10 false (reversedValues pipeline).toR : Source.EM E [] _).run
      (Source.L0 E,SourceKeccak.afterLiteral populated binary) =
      (.ok (reversedEncoded pipeline),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := rfl

theorem reversed_execution (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) frame 11 0 none
      (.revertError errorDeclaration rfl reversedArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,populated) =
      (.error (.revert ((global pipeline).selector
        (Source.sigOf E.layout errorDeclaration.name [STy.bytes32,.bool,.bool]) ++ reversedEncoded pipeline)),
        (Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  execute (global pipeline) frame 10 errorDeclaration rfl reversedArguments locals
    (.cons (.bool false) .nil) populated _ _ (reversedValues pipeline) (reversedEncoded pipeline)
    (reversed_arguments pipeline) (reversed_encoding pipeline)

theorem wrong_argument_order (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) frame 11 0 none statement locals).run (Source.L0 E,populated) ≠
    (Source.execS (global pipeline) frame 11 0 none
      (.revertError errorDeclaration rfl reversedArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,populated) := by
  have actual := actual_execution pipeline false
  change (Source.execS (global pipeline) frame 11 0 none statement locals).run _ = _ at actual
  rw [actual,reversed_execution]
  intro same
  have payload := Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  have data := List.append_cancel_left payload
  simp only [encoded,reversedEncoded,SourceEmit.three_static] at data
  have tail := List.append_cancel_left data
  exact (by decide +kernel : zeroWord ++ zeroWord ≠ oneWord ++ zeroWord) tail

theorem static_is_not_plain_revert (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) {frame with static:=true} 11 0 none statement locals).run
      (Source.L0 E,populated) ≠ (.error (.revert []),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  intro same
  have actual := actual_execution pipeline true
  have outcomes := (congrArg Prod.fst actual).symm.trans (congrArg Prod.fst same)
  have payload := Source.Halt.revert.inj (Except.error.inj outcomes)
  have length := congrArg List.length payload
  rw [exact_payload_length] at length
  change 100=0 at length
  exact (by decide +kernel : (100 : Nat) ≠ 0) length

theorem argument_timeout (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) frame 1 0 none statement locals).run (Source.L0 E,populated) =
      (.error .timeout,(Source.L0 E,populated)) := rfl

def sourceZero : RExpr E [.bool] (.int IntTy.u256) := .conv (.const (Q.ofInt 0)) (.inl rfl)
def sourceOne : RExpr E [.bool] (.int IntTy.u256) := .conv (.const (Q.ofInt 1)) (.inl rfl)
def failingArguments : RConvArgs E [.bool] [STy.bytes32,.bool,.bool] :=
  .cons (SourceKeccak.literal binary) rfl
    (.cons (.compare .eq (.binary .div sourceOne sourceZero) sourceZero) rfl (.cons (.local .here) rfl .nil))

theorem panic_before_payload (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 11 0 none
      (.revertError errorDeclaration rfl failingArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,populated) =
      (.error (.revert (Source.panicData .divZero)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  cases pipeline <;> rfl

#print axioms signature_utf8
#print axioms reversed_arguments
#print axioms reversed_encoding
#print axioms reversed_execution
#print axioms wrong_argument_order
#print axioms static_is_not_plain_revert
#print axioms argument_timeout
#print axioms panic_before_payload

#print axioms populated_snapshot
#print axioms error_member
#print axioms assign_false
#print axioms read_false
#print axioms arguments_execute
#print axioms encoding_execute
#print axioms signature_bytes
#print axioms actual_execution
#print axioms intrinsic_selector_payload
#print axioms encoded_length
#print axioms exact_payload_length
#print axioms complete_machine
#print axioms zero_horizon
end Solidity.Lowering.V08.SourceCustomErrorControls
