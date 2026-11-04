import Solidity.Lowering.V08.SourceEmitControls
import Solidity.Lowering.V08.SourceTransient

/-! Actual event execution at reached transient/caller state. One existing
SourceEmitControls declaration environment is used throughout. Source journal
rollback, log erasure and transaction end are separate published operations. -/
namespace Solidity.Lowering.V08.SourceTransientEmitControls
open Solidity Source
open SourceEmit SourceEmitControls

def opening : Source.St E := SourceTransient.transientUpdate
  (SourceTransient.endExecution populated) sender scratch (.bool true)
def written : Source.St E := SourceTransient.transientUpdate opening self scratch (.bool true)
def setScratch : RExpr E [.bool] .bool := .assign (.state scratchDecl rfl rfl) (.bool true)
def afterArgs : Source.St E := SourceKeccak.afterLiteral written binary

def completed (pipeline : Roadmap.Pipeline) : Source.St E :=
  logged (global pipeline) frame eventDeclaration [STy.bytes32,.bool,.bool] (encoded pipeline) afterArgs
def reorderedCompleted (pipeline : Roadmap.Pipeline) : Source.St E :=
  logged (global pipeline) frame eventDeclaration [STy.bytes32,.bool,.bool] (reorderedEncoded pipeline) afterArgs
def eventPayload (pipeline : Roadmap.Pipeline) : Roadmap.Bytes :=
  (global pipeline).selector (sigOf E.layout eventDeclaration.name [STy.bytes32,.bool,.bool]) ++ encoded pipeline

theorem assignment_statement (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.execS (global pipeline) frame (fuel+12) 1 none
      (.expr setScratch : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,opening) = (.ok (.normal locals),(Source.L0 E,written)) := rfl

/-- Proved at the reached state, never by applying a fixed-populated equation. -/
theorem arguments_reached (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat) :
    (Source.evalConvArgs (global pipeline) {frame with static:=static} (fuel+10) arguments).run
      (locals,written) =
      (.ok (values pipeline),(.cons (.bool false) .nil,afterArgs)) := by
  simp only [arguments,Source.evalConvArgs,Source.convRV,Source.getV,setFalse,
    ↓reduceDIte,bind,pure,ExceptT.bind,ExceptT.pure,
    ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind]
  rfl

theorem encoding_reached (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat) :
    (Source.encodeVals {frame with static:=static} (fuel+10) false (values pipeline).toR :
      Source.EM E [] _).run (Source.L0 E,afterArgs) =
      (.ok (encoded pipeline),(Source.L0 E,afterArgs)) := rfl

theorem emit_reached (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.execS (global pipeline) frame (fuel+11) 1 none statement locals).run
      (Source.L0 E,written) =
      (.ok (.normal (.cons (.bool false) .nil)),(Source.L0 E,completed pipeline)) :=
  SourceEmit.exec_success (global pipeline) frame (fuel+10) eventDeclaration rfl arguments
    locals (.cons (.bool false) .nil) written afterArgs afterArgs (values pipeline) (encoded pipeline)
    (arguments_reached pipeline false fuel) (encoding_reached pipeline false fuel) rfl

/-- Direct static emit still executes arguments and encoding before rejection. -/
theorem direct_static (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.execS (global pipeline) {frame with static:=true} (fuel+11) 1 none statement locals).run
      (Source.L0 E,written) = (.error (.revert []),(Source.L0 E,afterArgs)) :=
  SourceEmit.exec_static (global pipeline) {frame with static:=true} (fuel+10) eventDeclaration rfl arguments
    locals (.cons (.bool false) .nil) written afterArgs afterArgs (values pipeline) (encoded pipeline)
    (arguments_reached pipeline true fuel) (encoding_reached pipeline true fuel) rfl

def items (args : RConvArgs E [.bool] [STy.bytes32,.bool,.bool]) :
    RItems E [] false .body [.bool] [.bool] :=
  .stmt (.expr setScratch) (.stmt (.emit eventDeclaration rfl args) .nil)
def execution (pipeline : Roadmap.Pipeline) (static reordered : Bool) (horizon : Nat := 13) :=
  Source.execItems (global pipeline) {frame with static:=static} horizon 1 none
    (items (if reordered then reorderedArguments else arguments)) locals

theorem sequence_complete (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (execution pipeline false false (fuel+13)).run (Source.L0 E,opening) =
      (.ok (.normal (.cons (.bool false) .nil)),(Source.L0 E,completed pipeline)) := by
  have prefixRun := assignment_statement pipeline fuel
  have event :
      (Source.execS (global pipeline) frame (fuel+11) 1 none
        (.emit eventDeclaration rfl arguments : RStmt E [] false .body [.bool] [.bool]) locals).run
        (Source.L0 E,written) =
        (.ok (.normal (.cons (.bool false) .nil)),(Source.L0 E,completed pipeline)) :=
    emit_reached pipeline fuel
  change (Source.execItems (global pipeline) frame (fuel+13) 1 none
    (.stmt (.expr setScratch) (.stmt (.emit eventDeclaration rfl arguments) .nil) :
      RItems E [] false .body [.bool] [.bool]) locals).run (Source.L0 E,opening) = _
  simp only [ExceptT.run] at prefixRun event
  simp only [Source.execItems,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
    ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,prefixRun,event,
    Source.Out.up,Source.EM.lift,Except.pure] <;> rfl

theorem prefix_static_refusal (pipeline : Roadmap.Pipeline) (reordered : Bool) :
    (execution pipeline true reordered).run (Source.L0 E,opening) =
      (.error (.revert []),(Source.L0 E,opening)) := rfl

theorem zero_horizon (pipeline : Roadmap.Pipeline) (static reordered : Bool) :
    (execution pipeline static reordered 0).run (Source.L0 E,opening) =
      (.error .timeout,(Source.L0 E,opening)) := rfl

theorem direct_argument_timeout (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) frame 1 1 none statement locals).run (Source.L0 E,written) =
      (.error .timeout,(Source.L0 E,written)) := rfl

theorem prefix_argument_timeout (pipeline : Roadmap.Pipeline) :
    (execution pipeline false false 4).run (Source.L0 E,opening) =
      (.error .timeout,(Source.L0 E,written)) := rfl

theorem reordered_arguments_reached (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalConvArgs (global pipeline) frame (fuel+10) reorderedArguments).run (locals,written) =
      (.ok (reorderedValues pipeline),(.cons (.bool false) .nil,afterArgs)) := rfl

theorem reordered_encoding_reached (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.encodeVals frame (fuel+10) false (reorderedValues pipeline).toR : Source.EM E [] _).run
      (Source.L0 E,afterArgs) = (.ok (reorderedEncoded pipeline),(Source.L0 E,afterArgs)) := rfl

theorem reordered_emit_reached (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.execS (global pipeline) frame (fuel+11) 1 none
      (.emit eventDeclaration rfl reorderedArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,written) =
      (.ok (.normal (.cons (.bool false) .nil)),(Source.L0 E,reorderedCompleted pipeline)) :=
  SourceEmit.exec_success (global pipeline) frame (fuel+10) eventDeclaration rfl reorderedArguments
    locals (.cons (.bool false) .nil) written afterArgs afterArgs (reorderedValues pipeline) (reorderedEncoded pipeline)
    (reordered_arguments_reached pipeline fuel) (reordered_encoding_reached pipeline fuel) rfl

theorem reordered_sequence_complete (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (execution pipeline false true (fuel+13)).run (Source.L0 E,opening) =
      (.ok (.normal (.cons (.bool false) .nil)),(Source.L0 E,reorderedCompleted pipeline)) := by
  have prefixRun := assignment_statement pipeline fuel
  have event := reordered_emit_reached pipeline fuel
  have frameEq : {frame with static:=false} = frame := rfl
  simp only [ExceptT.run] at prefixRun event
  simp only [execution,items,frameEq,↓reduceIte,Source.execItems,bind,pure,ExceptT.bind,
    ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,
    prefixRun,event,Source.Out.up,Source.EM.lift,Except.pure] <;> rfl

theorem wrong_actual_order (pipeline : Roadmap.Pipeline) :
    (execution pipeline false false).run (Source.L0 E,opening) ≠
      (execution pipeline false true).run (Source.L0 E,opening) := by
  rw [sequence_complete pipeline 0,reordered_sequence_complete pipeline 0]
  intro same
  exact wrong_argument_order pipeline (logged_payload_injective _ _ _ _ _ _ _
    (congrArg (fun result => result.2.2) same))

theorem complete_vector (pipeline : Roadmap.Pipeline) :
    ((completed pipeline).ex.world.accounts sender).balance = 93 ∧
    ((completed pipeline).ex.world.accounts self).balance = 7 ∧
    ((completed pipeline).ex.world.accounts self).code = some 0 ∧
    ((completed pipeline).ex.world.accounts self).nonce = 1 ∧
    ((completed pipeline).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (opening.ex.transient.cells self).read scratch = some (.bool false) ∧
    ((completed pipeline).ex.transient.cells self).read scratch = some (.bool true) ∧
    ((completed pipeline).ex.transient.cells sender).read scratch = some (.bool true) ∧
    opening.ex.journal.length = 1 ∧ (completed pipeline).ex.journal.length = 2 ∧
    (completed pipeline).heap.next = 2 ∧
    (completed pipeline).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (completed pipeline).heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ ∧
    (completed pipeline).events = populated.events ∧
    (completed pipeline).logs = (self,eventPayload pipeline) :: populated.logs ∧
    (completed pipeline).fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem payload_observation (pipeline : Roadmap.Pipeline) :
    eventPayload pipeline =
      (global pipeline).selector (sigOf E.layout eventDeclaration.name [STy.bytes32,.bool,.bool]) ++
      (Semantics.wordBytes (keccakBytes [0,255,128]).1.toNat ++ (Semantics.wordBytes 0 ++ Semantics.wordBytes 0)) := by
  unfold eventPayload
  rw [SourceEmitControls.encoded_intrinsic]

theorem erased_execution (pipeline : Roadmap.Pipeline) :
    let result := (execution pipeline false false).run (Source.L0 E,opening)
    (result.1,result.2.1,eraseLogs result.2.2) =
      (.ok (.normal (.cons (.bool false) .nil)),Source.L0 E,eraseLogs afterArgs) := by
  have erased : eraseLogs (completed pipeline) = eraseLogs afterArgs :=
    SourceEmit.logged_erasure (global pipeline) frame eventDeclaration [STy.bytes32,.bool,.bool]
      (encoded pipeline) afterArgs
  simp only [sequence_complete pipeline 0,erased]

theorem erased_not_opening (pipeline : Roadmap.Pipeline) : eraseLogs (completed pipeline) ≠ eraseLogs opening := by
  intro same
  have heaps := congrArg (fun state : Source.St E => state.heap.next) same
  change 2 = 1 at heaps
  cases heaps

def mark : Source.CallFrame := opening.ex.enter self sender frame.value binary false

theorem rollback_execution_component : mark.rollback written.ex = opening.ex := by
  exact Source.rollback_run opening.ex [.transient self (fun cells => cells.set scratch (some (.bool true)))]
    self sender frame.value binary false

/-- Journal rollback does NOT undo Source logs or heap. No EVM-log adequacy claim. -/
theorem rollback_logged (pipeline : Roadmap.Pipeline) :
    {completed pipeline with ex:=mark.rollback (completed pipeline).ex} =
      logged (global pipeline) frame eventDeclaration [STy.bytes32,.bool,.bool]
        (encoded pipeline) (SourceKeccak.afterLiteral opening binary) := by
  change {completed pipeline with ex:=mark.rollback written.ex} = _
  rw [rollback_execution_component]
  rfl

theorem rollback_static :
    {afterArgs with ex:=mark.rollback afterArgs.ex} = SourceKeccak.afterLiteral opening binary := by
  change {afterArgs with ex:=mark.rollback written.ex} = _
  rw [rollback_execution_component]
  rfl

theorem wrong_automatic_rollback (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) {frame with static:=true} 11 1 none statement locals).run
      (Source.L0 E,written) ≠ (.error (.revert []),(Source.L0 E,SourceKeccak.afterLiteral opening binary)) := by
  rw [direct_static pipeline 0]
  intro same
  have journals := congrArg (fun result => result.2.2.ex.journal.length) same
  change 2 = 1 at journals
  cases journals

theorem static_boundary_contrast (pipeline : Roadmap.Pipeline) :
    ((Source.execS (global pipeline) {frame with static:=true} 11 1 none statement locals).run
      (Source.L0 E,written)).2.2.heap.next = 2 ∧
    ((execution pipeline true false).run (Source.L0 E,opening)).2.2.heap.next = 1 := by
  rw [direct_static pipeline 0,prefix_static_refusal]
  exact ⟨rfl,rfl⟩

theorem end_fields (pipeline : Roadmap.Pipeline) :
    (SourceTransient.endExecution (completed pipeline)).ex.world = (completed pipeline).ex.world ∧
    (SourceTransient.endExecution (completed pipeline)).ex.journal = [] ∧
    (SourceTransient.endExecution (completed pipeline)).heap = (completed pipeline).heap ∧
    (SourceTransient.endExecution (completed pipeline)).events = (completed pipeline).events ∧
    (SourceTransient.endExecution (completed pipeline)).logs = (completed pipeline).logs ∧
    (SourceTransient.endExecution (completed pipeline)).fnLocals = (completed pipeline).fnLocals :=
  SourceTransient.end_execution_fields (completed pipeline)

theorem end_reads (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,SourceTransient.endExecution (completed pipeline)) =
      (.ok (.val (.bool false)),(locals,SourceTransient.endExecution (completed pipeline))) ∧
    (Source.evalE (global pipeline) {frame with this:=sender} 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,SourceTransient.endExecution (completed pipeline)) =
      (.ok (.val (.bool false)),(locals,SourceTransient.endExecution (completed pipeline))) := ⟨rfl,rfl⟩

#print axioms assignment_statement
#print axioms arguments_reached
#print axioms encoding_reached
#print axioms emit_reached
#print axioms direct_static
#print axioms sequence_complete
#print axioms prefix_static_refusal
#print axioms zero_horizon
#print axioms direct_argument_timeout
#print axioms prefix_argument_timeout
#print axioms reordered_arguments_reached
#print axioms reordered_encoding_reached
#print axioms reordered_emit_reached
#print axioms reordered_sequence_complete
#print axioms wrong_actual_order
#print axioms complete_vector
#print axioms payload_observation
#print axioms erased_execution
#print axioms erased_not_opening
#print axioms rollback_execution_component
#print axioms rollback_logged
#print axioms rollback_static
#print axioms wrong_automatic_rollback
#print axioms static_boundary_contrast
#print axioms end_fields
#print axioms end_reads
end Solidity.Lowering.V08.SourceTransientEmitControls
