import Solidity.Lowering.V08.SourceTransientEmitControls
import Solidity.Lowering.V08.SourceAbi

/-! Actual valid dynamic-memory event arguments in the SAME existing event
Env. Literal conversion allocates; the published byte reader/encoder consumes
the reached reference. No decoder, encoder, interpreter or admission bound. -/
namespace Solidity.Lowering.V08.SourceTransientBytesEmitControls
open Solidity Source
open SourceEmitControls
open SourceTransientEmitControls (opening written)

def arguments (bytes : Roadmap.Bytes) : RConvArgs E [.bool] [.bytes .memory] :=
  .cons (.str bytes) rfl .nil
def values : Source.Vals E.layout [.bytes .memory] := .cons (.memRef rfl 1) .nil
def afterArgument (bytes : Roadmap.Bytes) : Source.St E := SourceKeccak.afterLiteral written bytes
def encoded (bytes : Roadmap.Bytes) : Roadmap.Bytes := Source.abiLayout [(true,bytes)]
def eventSelector (pipeline : Roadmap.Pipeline) : Roadmap.Bytes :=
  (global pipeline).selector (sigOf E.layout bytesEvent.name [.bytes .memory])
def completed (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceEmit.logged (global pipeline) frame bytesEvent [.bytes .memory] (encoded bytes) (afterArgument bytes)
def headPayload (state : Source.St E) : Option Roadmap.Bytes := state.logs.head?.map Prod.snd

theorem bytes_event_member : bytesEvent ∈ E.decls :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem arguments_reached (pipeline : Roadmap.Pipeline) (static : Bool)
    (bytes : Roadmap.Bytes) (fuel : Nat) :
    (Source.evalConvArgs (global pipeline) {frame with static:=static} (fuel+10) (arguments bytes)).run
      (locals,written) = (.ok values,(locals,afterArgument bytes)) := rfl

theorem memory_reached (bytes : Roadmap.Bytes) :
    (afterArgument bytes).heap.next = 2 ∧
    (afterArgument bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (afterArgument bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ := ⟨rfl,rfl,rfl⟩

theorem encoding_reached (static : Bool) (bytes : Roadmap.Bytes) (fuel : Nat) :
    (Source.encodeVals {frame with static:=static} (fuel+10) false values.toR : Source.EM E [] _).run
      (Source.L0 E,afterArgument bytes) = (.ok (encoded bytes),(Source.L0 E,afterArgument bytes)) := rfl

theorem emit_reached (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (fuel : Nat) :
    (Source.execS (global pipeline) frame (fuel+11) 1 none
      (.emit bytesEvent rfl (arguments bytes) : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,written) = (.ok (.normal locals),(Source.L0 E,completed pipeline bytes)) :=
  SourceEmit.exec_success (global pipeline) frame (fuel+10) bytesEvent rfl (arguments bytes)
    locals locals written (afterArgument bytes) (afterArgument bytes) values (encoded bytes)
    (arguments_reached pipeline false bytes fuel) (encoding_reached false bytes fuel) rfl

theorem direct_static (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (fuel : Nat) :
    (Source.execS (global pipeline) {frame with static:=true} (fuel+11) 1 none
      (.emit bytesEvent rfl (arguments bytes) : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,written) = (.error (.revert []),(Source.L0 E,afterArgument bytes)) :=
  SourceEmit.exec_static (global pipeline) {frame with static:=true} (fuel+10) bytesEvent rfl (arguments bytes)
    locals locals written (afterArgument bytes) (afterArgument bytes) values (encoded bytes)
    (arguments_reached pipeline true bytes fuel) (encoding_reached true bytes fuel) rfl

def items (bytes : Roadmap.Bytes) : RItems E [] false .body [.bool] [.bool] :=
  .stmt (.expr SourceTransientEmitControls.setScratch) (.stmt (.emit bytesEvent rfl (arguments bytes)) .nil)
def execution (pipeline : Roadmap.Pipeline) (static : Bool) (bytes : Roadmap.Bytes) (horizon : Nat := 13) :=
  Source.execItems (global pipeline) {frame with static:=static} horizon 1 none (items bytes) locals

theorem sequence_complete (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (fuel : Nat) :
    (execution pipeline false bytes (fuel+13)).run (Source.L0 E,opening) =
      (.ok (.normal locals),(Source.L0 E,completed pipeline bytes)) := by
  have prefixRun := SourceTransientEmitControls.assignment_statement pipeline fuel
  have event := emit_reached pipeline bytes fuel
  change (Source.execItems (global pipeline) frame (fuel+13) 1 none
    (.stmt (.expr SourceTransientEmitControls.setScratch)
      (.stmt (.emit bytesEvent rfl (arguments bytes)) .nil) : RItems E [] false .body [.bool] [.bool])
    locals).run (Source.L0 E,opening) = _
  simp only [ExceptT.run] at prefixRun event
  simp only [Source.execItems,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
    ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,prefixRun,event,
    Source.Out.up,Source.EM.lift,Except.pure] <;> rfl

theorem prefix_static_refusal (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (execution pipeline true bytes).run (Source.L0 E,opening) =
      (.error (.revert []),(Source.L0 E,opening)) := rfl

theorem zero_timeout (pipeline : Roadmap.Pipeline) (static : Bool) (bytes : Roadmap.Bytes) :
    (execution pipeline static bytes 0).run (Source.L0 E,opening) =
      (.error .timeout,(Source.L0 E,opening)) := rfl

theorem prefix_argument_timeout (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (execution pipeline false bytes 4).run (Source.L0 E,opening) =
      (.error .timeout,(Source.L0 E,written)) := rfl

theorem payload_transport (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    eventSelector pipeline ++ encoded bytes = eventSelector pipeline ++
      (Semantics.wordBytes 32 ++ (Semantics.wordBytes bytes.length ++ Semantics.pad32 bytes)) := by
  rw [encoded,SourceAbi.single_dynamic_bytes]

theorem complete_vector (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((completed pipeline bytes).ex.world.accounts sender).balance = 93 ∧
    ((completed pipeline bytes).ex.world.accounts self).balance = 7 ∧
    ((completed pipeline bytes).ex.world.accounts self).code = some 0 ∧
    ((completed pipeline bytes).ex.world.accounts self).nonce = 1 ∧
    ((completed pipeline bytes).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (opening.ex.transient.cells self).read scratch = some (.bool false) ∧
    ((completed pipeline bytes).ex.transient.cells self).read scratch = some (.bool true) ∧
    ((completed pipeline bytes).ex.transient.cells sender).read scratch = some (.bool true) ∧
    opening.ex.journal.length = 1 ∧ (completed pipeline bytes).ex.journal.length = 2 ∧
    (completed pipeline bytes).heap.next = 2 ∧
    (completed pipeline bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (completed pipeline bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (completed pipeline bytes).events = populated.events ∧
    (completed pipeline bytes).logs = (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (completed pipeline bytes).fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def boundary33 : Roadmap.Bytes := List.replicate 33 254

theorem boundary_cases (pipeline : Roadmap.Pipeline) :
    (execution pipeline false []).run (Source.L0 E,opening) =
      (.ok (.normal locals),(Source.L0 E,completed pipeline [])) ∧
    (execution pipeline false binary).run (Source.L0 E,opening) =
      (.ok (.normal locals),(Source.L0 E,completed pipeline binary)) ∧
    (execution pipeline false boundary33).run (Source.L0 E,opening) =
      (.ok (.normal locals),(Source.L0 E,completed pipeline boundary33)) :=
  ⟨sequence_complete pipeline [] 0,sequence_complete pipeline binary 0,sequence_complete pipeline boundary33 0⟩

theorem boundary_lengths : ((encoded []).length,(encoded binary).length,(encoded boundary33).length) =
    (64,96,128) := by decide +kernel

theorem actual_payload (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    headPayload ((execution pipeline false bytes).run (Source.L0 E,opening)).2.2 =
      some (eventSelector pipeline ++ encoded bytes) := by
  rw [sequence_complete pipeline bytes 0]
  rfl

theorem wrong_length (pipeline : Roadmap.Pipeline) :
    headPayload ((execution pipeline false binary).run (Source.L0 E,opening)).2.2 ≠
      some (eventSelector pipeline ++ (encoded binary).set 63 2) := by
  rw [actual_payload]
  intro same
  exact (by decide +kernel : encoded binary ≠ (encoded binary).set 63 2)
    (List.append_cancel_left (Option.some.inj same))

theorem wrong_padding (pipeline : Roadmap.Pipeline) :
    headPayload ((execution pipeline false binary).run (Source.L0 E,opening)).2.2 ≠
      some (eventSelector pipeline ++ (encoded binary).set 95 1) := by
  rw [actual_payload]
  intro same
  exact (by decide +kernel : encoded binary ≠ (encoded binary).set 95 1)
    (List.append_cancel_left (Option.some.inj same))

theorem wrong_byte_order (pipeline : Roadmap.Pipeline) :
    headPayload ((execution pipeline false binary).run (Source.L0 E,opening)).2.2 ≠
      headPayload ((execution pipeline false binary.reverse).run (Source.L0 E,opening)).2.2 := by
  rw [actual_payload,actual_payload]
  intro same
  exact (by decide +kernel : encoded binary ≠ encoded binary.reverse)
    (List.append_cancel_left (Option.some.inj same))

def referenceArguments : RConvArgs E [.bytes .memory] [.bytes .memory] := .cons (.local .here) rfl .nil
def referenceLocals (address : Nat) : Source.Locals E.layout [.bytes .memory] := .cons (.memRef rfl address) .nil

def stale (pipeline : Roadmap.Pipeline) := Source.execS (global pipeline) frame 11 1 none
  (.emit bytesEvent rfl referenceArguments : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
  (referenceLocals 0)

/-- Pointer0 is valid, but reads the old two-byte object rather than fresh1. -/
theorem stale_reached (pipeline : Roadmap.Pipeline) :
    (stale pipeline).run (Source.L0 E,written) =
      (.ok (.normal (referenceLocals 0)),(Source.L0 E,
        SourceEmit.logged (global pipeline) frame bytesEvent [.bytes .memory] (encoded [0,255]) written)) := by
  have args : (Source.evalConvArgs (global pipeline) frame 10 referenceArguments).run (referenceLocals 0,written) =
      (.ok (.cons (.memRef rfl 0) .nil),(referenceLocals 0,written)) := rfl
  have encoding : (Source.encodeVals frame 10 false
      ((.cons (.memRef rfl 0) .nil : Source.Vals E.layout [.bytes .memory]).toR) : Source.EM E [] _).run
      (Source.L0 E,written) = (.ok (encoded [0,255]),(Source.L0 E,written)) := rfl
  exact SourceEmit.exec_success (global pipeline) frame 10 bytesEvent rfl referenceArguments
    (referenceLocals 0) (referenceLocals 0) written written written (.cons (.memRef rfl 0) .nil)
    (encoded [0,255]) args encoding rfl

theorem fresh_not_stale (pipeline : Roadmap.Pipeline) :
    headPayload ((execution pipeline false binary).run (Source.L0 E,opening)).2.2 ≠
      headPayload ((stale pipeline).run (Source.L0 E,written)).2.2 := by
  rw [actual_payload,stale_reached]
  change some (eventSelector pipeline ++ encoded binary) ≠ some (eventSelector pipeline ++ encoded [0,255])
  intro same
  exact (by decide +kernel : encoded binary ≠ encoded [0,255])
    (List.append_cancel_left (Option.some.inj same))

theorem wrong_reference (pipeline : Roadmap.Pipeline) :
    (Source.evalConvArgs (global pipeline) frame 10 (arguments binary)).run (locals,written) ≠
      (.ok (.cons (.memRef rfl 0) .nil),(locals,afterArgument binary)) := by
  have actual : (Source.evalConvArgs (global pipeline) frame 10 (arguments binary)).run (locals,written) =
      (.ok values,(locals,afterArgument binary)) := arguments_reached pipeline false binary 0
  rw [actual]
  intro same
  have valsEq := Except.ok.inj (congrArg Prod.fst same)
  have addresses := congrArg (fun vs : Source.Vals E.layout [.bytes .memory] =>
    match vs with | .cons (.memRef _ address) _ => address | _ => 0) valsEq
  change 1 = 0 at addresses
  cases addresses

/-- Deliberately malformed pointer99 is a negative fixture, not SourceSpec admission. -/
theorem dangling_error (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 4 1 none
      (.emit bytesEvent rfl danglingArguments : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
        danglingLocals).run (Source.L0 E,written) =
      (.error (.stuck "dangling memory reference"),(Source.L0 E,written)) := by
  have args : (Source.evalConvArgs (global pipeline) {frame with static:=static} 3 danglingArguments).run
      (danglingLocals,written) = (.ok danglingValues,(danglingLocals,written)) := rfl
  have encoding : (Source.encodeVals {frame with static:=static} 3 false danglingValues.toR : Source.EM E [] _).run
      (Source.L0 E,written) = (.error (.stuck "dangling memory reference"),(Source.L0 E,written)) := rfl
  exact SourceEmit.exec_encoding_failure (global pipeline) {frame with static:=static} 3 bytesEvent rfl danglingArguments
    danglingLocals danglingLocals written written written danglingValues (.stuck "dangling memory reference") args encoding

theorem static_boundary_contrast (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((Source.execS (global pipeline) {frame with static:=true} 11 1 none
      (.emit bytesEvent rfl (arguments bytes) : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,written)).2.2.heap.next = 2 ∧
    ((execution pipeline true bytes).run (Source.L0 E,opening)).2.2.heap.next = 1 := by
  rw [direct_static pipeline bytes 0,prefix_static_refusal]
  exact ⟨rfl,rfl⟩

theorem erased_execution (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    let result := (execution pipeline false bytes).run (Source.L0 E,opening)
    (result.1,result.2.1,SourceEmit.eraseLogs result.2.2) =
      (.ok (.normal locals),Source.L0 E,SourceEmit.eraseLogs (afterArgument bytes)) := by
  have erased : SourceEmit.eraseLogs (completed pipeline bytes) = SourceEmit.eraseLogs (afterArgument bytes) :=
    SourceEmit.logged_erasure (global pipeline) frame bytesEvent [.bytes .memory] (encoded bytes) (afterArgument bytes)
  simp only [sequence_complete pipeline bytes 0,erased]

theorem rollback_logged (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    {completed pipeline bytes with ex:=SourceTransientEmitControls.mark.rollback (completed pipeline bytes).ex} =
      SourceEmit.logged (global pipeline) frame bytesEvent [.bytes .memory] (encoded bytes)
        (SourceKeccak.afterLiteral opening bytes) := by
  change {completed pipeline bytes with ex:=SourceTransientEmitControls.mark.rollback written.ex} = _
  rw [SourceTransientEmitControls.rollback_execution_component]
  rfl

theorem wrong_automatic_rollback (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.execS (global pipeline) {frame with static:=true} 11 1 none
      (.emit bytesEvent rfl (arguments bytes) : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,written) ≠ (.error (.revert []),(Source.L0 E,SourceKeccak.afterLiteral opening bytes)) := by
  rw [direct_static pipeline bytes 0]
  intro same
  have journals := congrArg (fun result => result.2.2.ex.journal.length) same
  change 2 = 1 at journals
  cases journals

theorem end_fields (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (SourceTransient.endExecution (completed pipeline bytes)).ex.world = (completed pipeline bytes).ex.world ∧
    (SourceTransient.endExecution (completed pipeline bytes)).ex.journal = [] ∧
    (SourceTransient.endExecution (completed pipeline bytes)).heap = (completed pipeline bytes).heap ∧
    (SourceTransient.endExecution (completed pipeline bytes)).events = (completed pipeline bytes).events ∧
    (SourceTransient.endExecution (completed pipeline bytes)).logs = (completed pipeline bytes).logs ∧
    (SourceTransient.endExecution (completed pipeline bytes)).fnLocals = (completed pipeline bytes).fnLocals :=
  SourceTransient.end_execution_fields (completed pipeline bytes)

theorem end_reads (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,SourceTransient.endExecution (completed pipeline bytes)) =
      (.ok (.val (.bool false)),(locals,SourceTransient.endExecution (completed pipeline bytes))) ∧
    (Source.evalE (global pipeline) {frame with this:=sender} 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,SourceTransient.endExecution (completed pipeline bytes)) =
      (.ok (.val (.bool false)),(locals,SourceTransient.endExecution (completed pipeline bytes))) := ⟨rfl,rfl⟩

#print axioms bytes_event_member
#print axioms arguments_reached
#print axioms memory_reached
#print axioms encoding_reached
#print axioms emit_reached
#print axioms direct_static
#print axioms sequence_complete
#print axioms prefix_static_refusal
#print axioms zero_timeout
#print axioms prefix_argument_timeout
#print axioms payload_transport
#print axioms complete_vector
#print axioms boundary_cases
#print axioms boundary_lengths
#print axioms actual_payload
#print axioms wrong_length
#print axioms wrong_padding
#print axioms wrong_byte_order
#print axioms stale_reached
#print axioms fresh_not_stale
#print axioms wrong_reference
#print axioms dangling_error
#print axioms static_boundary_contrast
#print axioms erased_execution
#print axioms rollback_logged
#print axioms wrong_automatic_rollback
#print axioms end_fields
#print axioms end_reads
end Solidity.Lowering.V08.SourceTransientBytesEmitControls
