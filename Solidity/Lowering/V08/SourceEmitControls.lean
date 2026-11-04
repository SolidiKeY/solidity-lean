import Solidity.Lowering.V08.SourceEmit
import Solidity.Lowering.V08.SourceEnvironmentControls

/-! Actual typed event declaration and populated source machine. The program
bodies/globals remain supplied fixture data; no SourceSpec admission is inferred. -/
namespace Solidity.Lowering.V08.SourceEmitControls
open Solidity Source
open SourceEmit
def savedDecl : Source.Decl :=
  { kind := .stateVar, name := "saved", scope := some "C", top := false,
    node := .stateVar (.elem .bool) none none none false "saved" .none }
def scratchDecl : Source.Decl :=
  { kind := .stateVar, name := "scratch", scope := some "C", top := false,
    node := .stateVar (.elem .bool) none none none true "scratch" .none }
def eventDeclaration : Source.Decl :=
  { kind := .event, name := "HashThenLocal", scope := some "C", top := false,
    node := .event "HashThenLocal"
      (.cons (.eventParam (.elem (.fixedBytes 32 (by decide +kernel))) false (some "digest"))
        (.cons (.eventParam (.elem .bool) false (some "set"))
          (.cons (.eventParam (.elem .bool) false (some "read")) .nil))) false }
def bytesEvent : Source.Decl :=
  { kind:=.event,name:="RawBytes",scope:=some "C",top:=false,
    node:=.event "RawBytes" (.cons (.eventParam (.elem .bytes) false (some "raw")) .nil) false }
def E : Source.Env := ⟨[savedDecl, scratchDecl, eventDeclaration, bytesEvent]⟩
def sender : Roadmap.Address := ⟨1, by decide +kernel⟩
def self : Roadmap.Address := ⟨2, by decide +kernel⟩
def saved : Source.SPath := ⟨⟨some "C", "saved"⟩, []⟩
def scratch : Source.SPath := ⟨⟨some "C", "scratch"⟩, []⟩
def empty : Source.St E :=
  ⟨⟨⟨fun _ => Source.Account.empty _⟩, Source.Transient.empty, []⟩,
    Source.Heap.empty, [], [], ⟨[], .nil⟩, Source.FailureExecution.Cursor.empty⟩
def populated : Source.St E :=
  { empty with
    ex := empty.ex.run [
      .account sender (fun a => { a with balance := 93 }),
      .account self (fun a => { a with balance := 7, nonce := 1, code := some 0, storage := a.storage.write saved (.bool true) }),
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
    (populated.ex.world.accounts sender).balance = 93 ∧
    (populated.ex.world.accounts self).balance = 7 ∧
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
  .emit eventDeclaration rfl arguments

theorem event_member : eventDeclaration ∈ E.decls := by
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

theorem emit_execute (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.execS (global pipeline) frame (horizon+11) 0 none statement locals).run
      (Source.L0 E,populated) =
      (.ok (.normal (.cons (.bool false) .nil)),
        (Source.L0 E,logged (global pipeline) frame eventDeclaration [STy.bytes32,.bool,.bool]
          (encoded pipeline) (SourceKeccak.afterLiteral populated binary))) :=
  exec_success (global pipeline) frame (horizon+10) eventDeclaration rfl arguments
    locals (.cons (.bool false) .nil) populated _ _ (values pipeline) (encoded pipeline)
    (arguments_execute pipeline false horizon) (encoding_execute pipeline false horizon) rfl

theorem static_after_effects (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.execS (global pipeline) {frame with static:=true} (horizon+11) 0 none statement locals).run
      (Source.L0 E,populated) =
      (.error (.revert []),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  exec_static (global pipeline) {frame with static:=true} (horizon+10) eventDeclaration rfl arguments
    locals (.cons (.bool false) .nil) populated _ _ (values pipeline) (encoded pipeline)
    (arguments_execute pipeline true horizon) (encoding_execute pipeline true horizon) rfl

theorem retained_after_static :
    (SourceKeccak.afterLiteral populated binary).ex = populated.ex ∧
    (SourceKeccak.afterLiteral populated binary).events = populated.events ∧
    (SourceKeccak.afterLiteral populated binary).logs = populated.logs ∧
    (SourceKeccak.afterLiteral populated binary).fnLocals = populated.fnLocals ∧
    (SourceKeccak.afterLiteral populated binary).heap.next = 2 ∧
    (SourceKeccak.afterLiteral populated binary).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (SourceKeccak.afterLiteral populated binary).heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem erased_success_retains_effects (pipeline : Roadmap.Pipeline) :
    eraseLogs (logged (global pipeline) frame eventDeclaration [STy.bytes32,.bool,.bool]
      (encoded pipeline) (SourceKeccak.afterLiteral populated binary)) =
      eraseLogs (SourceKeccak.afterLiteral populated binary) :=
  logged_erasure _ _ _ _ _ _

theorem wrong_static_snapshot (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) {frame with static:=true} 11 0 none statement locals).run
      (Source.L0 E,populated) ≠ (.error (.revert []),(Source.L0 E,populated)) := by
  rw [static_after_effects pipeline 0]
  intro same
  have wrong := congrArg (fun result => result.2.2.heap.next) same
  change 2 = 1 at wrong
  contradiction

theorem zero_horizon (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) frame 0 0 none statement locals).run (Source.L0 E,populated) =
      (.error .timeout,(Source.L0 E,populated)) := rfl

/-- Even a positive statement horizon can time out in its argument step. -/
theorem argument_timeout (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) frame 1 0 none statement locals).run (Source.L0 E,populated) =
      (.error .timeout,(Source.L0 E,populated)) := rfl

def reorderedArguments : RConvArgs E [.bool] [STy.bytes32,.bool,.bool] :=
  .cons (SourceKeccak.literal binary) rfl
    (.cons (.local .here) rfl (.cons setFalse rfl .nil))
def reorderedValues (pipeline : Roadmap.Pipeline) : Source.Vals E.layout [STy.bytes32,.bool,.bool] :=
  .cons (digest pipeline) (.cons (.bool true) (.cons (.bool false) .nil))
def reorderedEncoded (pipeline : Roadmap.Pipeline) : Roadmap.Bytes :=
  Source.abiLayout [(false,Source.wordBytes (digestWord pipeline)),(false,oneWord),(false,zeroWord)]

theorem reordered_arguments_execute (pipeline : Roadmap.Pipeline) :
    (Source.evalConvArgs (global pipeline) frame 10 reorderedArguments).run (locals,populated) =
      (.ok (reorderedValues pipeline),(.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) := rfl

theorem reordered_encoding_execute (pipeline : Roadmap.Pipeline) :
    (Source.encodeVals frame 10 false (reorderedValues pipeline).toR : Source.EM E [] _).run
      (Source.L0 E,SourceKeccak.afterLiteral populated binary) =
      (.ok (reorderedEncoded pipeline),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := rfl

theorem exact_ordered_bytes (pipeline : Roadmap.Pipeline) :
    encoded pipeline = Source.wordBytes (digestWord pipeline) ++ (zeroWord ++ zeroWord) ∧
    reorderedEncoded pipeline = Source.wordBytes (digestWord pipeline) ++ (oneWord ++ zeroWord) := by
  exact ⟨three_static _ _ _,three_static _ _ _⟩

theorem wrong_argument_order (pipeline : Roadmap.Pipeline) : encoded pipeline ≠ reorderedEncoded pipeline := by
  rw [(exact_ordered_bytes pipeline).1,(exact_ordered_bytes pipeline).2]
  intro same
  have tails := List.append_cancel_left same
  have distinct : zeroWord ++ zeroWord ≠ oneWord ++ zeroWord := by decide +kernel
  exact distinct tails

def sourceZero : RExpr E [.bool] (.int IntTy.u256) :=
  .conv (.const (Source.Q.ofInt 0)) (.inl rfl)
def sourceOne : RExpr E [.bool] (.int IntTy.u256) :=
  .conv (.const (Source.Q.ofInt 1)) (.inl rfl)
def failingArgument : RExpr E [.bool] .bool :=
  .compare .eq (.binary .div sourceOne sourceZero) sourceZero
def failingArguments : RConvArgs E [.bool] [STy.bytes32,.bool,.bool] :=
  .cons (SourceKeccak.literal binary) rfl
    (.cons failingArgument rfl (.cons (.local .here) rfl .nil))

theorem panic_arguments (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalConvArgs (global pipeline) {frame with static:=static} 10 failingArguments).run
      (locals,populated) =
      (.error (.revert (Source.panicData .divZero)),(locals,SourceKeccak.afterLiteral populated binary)) := by
  cases pipeline <;> rfl

theorem panic_before_static (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 11 0 none
      (.emit eventDeclaration rfl failingArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,populated) =
      (.error (.revert (Source.panicData .divZero)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  exec_argument_failure (global pipeline) {frame with static:=static} 10 eventDeclaration rfl failingArguments
    locals locals populated _ (.revert (Source.panicData .divZero)) (panic_arguments pipeline static)

theorem intrinsic_panic_observation (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 11 0 none
      (.emit eventDeclaration rfl failingArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,populated) =
      (.error (.revert (Semantics.encodePanic 0x12)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  rw [panic_before_static,panicData_transport]
  rfl

theorem nonempty_panic : Source.panicData .divZero ≠ [] := by decide +kernel

theorem digest_word (pipeline : Roadmap.Pipeline) :
    digestWord pipeline = (global pipeline).fixed.hash binary := by
  apply Fin.ext
  simp only [digestWord,Source.fitBytes,List.take_left' (Source.wordBytes_length _),
    Source.wordBytes_length,Nat.sub_self,List.replicate_zero,List.append_nil,
    Source.wordBytes_value,Source.toWord,Nat.mod_eq_of_lt ((global pipeline).fixed.hash binary).isLt]

theorem encoded_intrinsic (pipeline : Roadmap.Pipeline) :
    encoded pipeline = Semantics.wordBytes (keccakBytes [0,255,128]).1.toNat ++
      (Semantics.wordBytes 0 ++ Semantics.wordBytes 0) := by
  rw [(exact_ordered_bytes pipeline).1,digest_word]
  have bytes := CryptoObservations.fixed_keccak_bytes (global pipeline).fixed
    Roadmap.Controls.toyFixed_keccak binary
  change Source.wordBytes ((global pipeline).fixed.hash binary) =
    Semantics.wordBytes (keccakBytes [0,255,128]).1.toNat at bytes
  rw [bytes]
  rfl

theorem reordered_emit_execute (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) frame 11 0 none
      (.emit eventDeclaration rfl reorderedArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,populated) =
      (.ok (.normal (.cons (.bool false) .nil)),
        (Source.L0 E,logged (global pipeline) frame eventDeclaration [STy.bytes32,.bool,.bool]
          (reorderedEncoded pipeline) (SourceKeccak.afterLiteral populated binary))) :=
  exec_success (global pipeline) frame 10 eventDeclaration rfl reorderedArguments locals
    (.cons (.bool false) .nil) populated _ _ (reorderedValues pipeline) (reorderedEncoded pipeline)
    (reordered_arguments_execute pipeline) (reordered_encoding_execute pipeline) rfl

theorem wrong_ordered_execution (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) frame 11 0 none statement locals).run (Source.L0 E,populated) ≠
    (Source.execS (global pipeline) frame 11 0 none
      (.emit eventDeclaration rfl reorderedArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,populated) := by
  rw [emit_execute pipeline 0,reordered_emit_execute]
  intro same
  exact wrong_argument_order pipeline (logged_payload_injective _ _ _ _ _ _ _
    (congrArg (fun result => result.2.2) same))

/-! Deliberately malformed heap reference: a negative encoding control, NOT an
admitted SourceSpec machine. Successful populated cases above remain separate. -/
def danglingLocals : Source.Locals E.layout [.bytes .memory] :=
  .cons (.memRef rfl 99) .nil
def danglingArguments : RConvArgs E [.bytes .memory] [.bytes .memory] :=
  .cons (.local .here) rfl .nil
def danglingValues : Source.Vals E.layout [.bytes .memory] :=
  .cons (.memRef rfl 99) .nil

theorem dangling_arguments_execute (pipeline : Roadmap.Pipeline) :
    (Source.evalConvArgs (global pipeline) {frame with static:=true} 3 danglingArguments).run
      (danglingLocals,populated) = (.ok danglingValues,(danglingLocals,populated)) := rfl

theorem dangling_encoding_execute :
    (Source.encodeVals {frame with static:=true} 3 false danglingValues.toR : Source.EM E [] _).run
      (Source.L0 E,populated) =
      (.error (.stuck "dangling memory reference"),(Source.L0 E,populated)) := rfl

theorem encoding_failure_before_static (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) {frame with static:=true} 4 0 none
      (.emit bytesEvent rfl danglingArguments : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
        danglingLocals).run (Source.L0 E,populated) =
      (.error (.stuck "dangling memory reference"),(Source.L0 E,populated)) :=
  exec_encoding_failure (global pipeline) {frame with static:=true} 3 bytesEvent rfl danglingArguments
    danglingLocals danglingLocals populated populated populated danglingValues
    (.stuck "dangling memory reference") (dangling_arguments_execute pipeline) dangling_encoding_execute

theorem wrong_encoding_halt (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) {frame with static:=true} 4 0 none
      (.emit bytesEvent rfl danglingArguments : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
        danglingLocals).run (Source.L0 E,populated) ≠
      (.error (.revert []),(Source.L0 E,populated)) := by
  rw [encoding_failure_before_static]
  intro same
  have result := congrArg Prod.fst same
  cases result

#print axioms dangling_arguments_execute
#print axioms dangling_encoding_execute
#print axioms encoding_failure_before_static
#print axioms wrong_encoding_halt

#print axioms digest_word
#print axioms encoded_intrinsic
#print axioms reordered_emit_execute
#print axioms wrong_ordered_execution

#print axioms panic_arguments
#print axioms panic_before_static
#print axioms intrinsic_panic_observation
#print axioms nonempty_panic

#print axioms encoding_execute
#print axioms emit_execute
#print axioms static_after_effects
#print axioms retained_after_static
#print axioms erased_success_retains_effects
#print axioms wrong_static_snapshot
#print axioms zero_horizon
#print axioms argument_timeout
#print axioms reordered_arguments_execute
#print axioms reordered_encoding_execute
#print axioms exact_ordered_bytes
#print axioms wrong_argument_order

#print axioms populated_snapshot
#print axioms event_member
#print axioms assign_false
#print axioms read_false
#print axioms arguments_execute
end Solidity.Lowering.V08.SourceEmitControls
