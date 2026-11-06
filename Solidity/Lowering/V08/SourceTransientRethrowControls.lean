import Solidity.Lowering.V08.SourcePrefixedRethrowControls

/-! Actual resolved statement/item composition. Source errors retain reached
state; explicit journal rollback and transaction end are separate operations.
No compiler, callback, catch, SourceSpec or runtime-frame adequacy is inferred. -/
namespace Solidity.Lowering.V08.SourceTransientRethrowControls
open Solidity Source
open SourceCustomErrorControls

def opening : Source.St E :=
  SourceTransient.transientUpdate SourceAbiControls.transientOpening sender scratch (.bool true)
def written : Source.St E := SourceTransient.transientUpdate opening self scratch (.bool true)
def payload (packed : Bool) (bytes : Roadmap.Bytes) : Roadmap.Bytes :=
  if packed then bytes else Source.abiLayout [(true,bytes)]
def after (packed : Bool) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceKeccak.afterLiteral written (payload packed bytes)

/-- A real parameter-preserving item list: assignment, declaration, rethrow. -/
def sequence (packed : Bool) (bytes : Roadmap.Bytes) :
    RItems E [] false .body [.bool] [.bytes .memory,.bool] :=
  .stmt (.expr SourceAbiControls.setScratch)
    (.stmt (.declInit (SourceAbi.literal packed bytes) rfl)
      (.stmt (.rethrow .here) .nil))

def execution (pipeline : Roadmap.Pipeline) (static packed : Bool) (bytes : Roadmap.Bytes)
    (horizon : Nat := 10) :=
  Source.execItems (global pipeline) {frame with static:=static} horizon 1 none
    (sequence packed bytes) locals

theorem assignment_statement (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.execS (global pipeline) frame (fuel+9) 1 none
      (.expr SourceAbiControls.setScratch : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,opening) = (.ok (.normal locals),(Source.L0 E,written)) := rfl

/-- The declaration receives the producer's actual allocator identity. -/
theorem declaration_statement (pipeline : Roadmap.Pipeline) (static packed : Bool)
    (bytes : Roadmap.Bytes) (fuel : Nat) :
    (Source.execS (global pipeline) {frame with static:=static} (fuel+8) 1 none
      (.declInit (SourceAbi.literal packed bytes) rfl :
        RStmt E [] false .body [.bool] [.bytes .memory,.bool]) locals).run
      (Source.L0 E,written) =
      (.ok (.normal (.cons (.memRef rfl 1) locals)),(Source.L0 E,after packed bytes)) := by
  have expression := SourceAbi.literal_execution (global pipeline) {frame with static:=static}
    (fuel+3) packed bytes locals written
  simp only [ExceptT.run] at expression
  simp only [Source.execS,Source.EM.sub,Source.convRV,Source.getV,Source.RVal.get,
    Source.EM.lift,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,expression,↓reduceDIte] <;> rfl

/-- No whole-execution premise: the three actual statements are discharged. -/
theorem sequence_complete (pipeline : Roadmap.Pipeline) (packed : Bool)
    (bytes : Roadmap.Bytes) (fuel : Nat) :
    (execution pipeline false packed bytes (fuel+10)).run (Source.L0 E,opening) =
      (.error (.revert (payload packed bytes)),(Source.L0 E,after packed bytes)) := by
  have prefixRun := assignment_statement pipeline fuel
  have allocation := declaration_statement pipeline false packed bytes fuel
  have frameEq : {frame with static:=false} = frame := rfl
  rw [frameEq] at allocation
  have rethrowRun :
      (Source.execS (global pipeline) frame (fuel+7) 1 none
        (.rethrow .here : RStmt E [] false .body [.bytes .memory,.bool] [.bytes .memory,.bool])
        (.cons (.memRef rfl 1) locals)).run (Source.L0 E,after packed bytes) =
        (.error (.revert (payload packed bytes)),(Source.L0 E,after packed bytes)) :=
    SourceCustomErrorFailures.rethrow_bytes (global pipeline) frame (fuel+6)
    (Source.Idx.here : Source.Idx [.bytes .memory,.bool] (.bytes .memory))
    (.cons (.memRef rfl 1) locals) (after packed bytes) 1 (payload packed bytes) rfl
    (SourceRethrow.allocated_object written (payload packed bytes))
  simp only [ExceptT.run] at prefixRun allocation rethrowRun
  simp only [execution,sequence,frameEq,Source.execItems,bind,pure,ExceptT.bind,
    ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,
    prefixRun,allocation,rethrowRun]

/-- Application to the real enclosing resolved block statement. -/
theorem block_execution (pipeline : Roadmap.Pipeline) (packed : Bool)
    (bytes : Roadmap.Bytes) (fuel : Nat) :
    (Source.execS (global pipeline) frame (fuel+11) 1 none
      (.block (sequence packed bytes) : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,opening) =
      (.error (.revert (payload packed bytes)),(Source.L0 E,after packed bytes)) := by
  have items := sequence_complete pipeline packed bytes fuel
  change (Source.execItems (global pipeline) frame (fuel+10) 1 none
    (sequence packed bytes) locals).run (Source.L0 E,opening) = _ at items
  simp only [ExceptT.run] at items
  simp only [Source.execS,items,bind,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind] <;> rfl

theorem static_before_allocation (pipeline : Roadmap.Pipeline) (packed : Bool)
    (bytes : Roadmap.Bytes) :
    (execution pipeline true packed bytes).run (Source.L0 E,opening) =
      (.error (.revert []),(Source.L0 E,opening)) := rfl

theorem prefix_timeout (pipeline : Roadmap.Pipeline) (packed : Bool)
    (bytes : Roadmap.Bytes) :
    (execution pipeline false packed bytes 5).run (Source.L0 E,opening) =
      (.error .timeout,(Source.L0 E,written)) := rfl

theorem zero_timeout (pipeline : Roadmap.Pipeline) (static packed : Bool)
    (bytes : Roadmap.Bytes) :
    (execution pipeline static packed bytes 0).run (Source.L0 E,opening) =
      (.error .timeout,(Source.L0 E,opening)) := rfl

/-- Complete pre/post observation; execution equality above retains all fields. -/
theorem complete_vector (packed : Bool) (bytes : Roadmap.Bytes) :
    ((after packed bytes).ex.world.accounts sender).balance = 93 ∧
    ((after packed bytes).ex.world.accounts self).balance = 7 ∧
    ((after packed bytes).ex.world.accounts self).code = some 0 ∧
    ((after packed bytes).ex.world.accounts self).nonce = 1 ∧
    ((after packed bytes).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (opening.ex.transient.cells self).read scratch = some (.bool false) ∧
    ((after packed bytes).ex.transient.cells self).read scratch = some (.bool true) ∧
    ((after packed bytes).ex.transient.cells sender).read scratch = some (.bool true) ∧
    opening.ex.journal.length = 1 ∧ (after packed bytes).ex.journal.length = 2 ∧
    (after packed bytes).heap.next = 2 ∧
    (after packed bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (after packed bytes).heap.get 1 = some ⟨.bytes .memory,.bytes (payload packed bytes)⟩ ∧
    (after packed bytes).events = populated.events ∧
    (after packed bytes).logs = populated.logs ∧
    (after packed bytes).fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem same_invocation_read (pipeline : Roadmap.Pipeline) (packed : Bool) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,after packed bytes) =
      (.ok (.val (.bool true)),(locals,after packed bytes)) := rfl

theorem other_owner_read (pipeline : Roadmap.Pipeline) (packed : Bool) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {frame with this:=sender} 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,after packed bytes) =
      (.ok (.val (.bool true)),(locals,after packed bytes)) := rfl

theorem other_path_read (pipeline : Roadmap.Pipeline) (packed : Bool) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state savedDecl rfl : RExpr E [.bool] .bool)).run (locals,after packed bytes) =
      (.ok (.val (.bool true)),(locals,after packed bytes)) := rfl

/-- The public enter mark predates only the self operation, preserving sender's
caller prefix. Source failure does not invoke this operation automatically. -/
def mark : Source.CallFrame := opening.ex.enter self sender frame.value binary false

theorem rollback_execution_component : mark.rollback written.ex = opening.ex := by
  exact Source.rollback_run opening.ex
    [.transient self (fun cells => cells.set scratch (some (.bool true)))]
    self sender frame.value binary false

theorem rollback_complete_state (packed : Bool) (bytes : Roadmap.Bytes) :
    {after packed bytes with ex:=mark.rollback (after packed bytes).ex} =
      SourceKeccak.afterLiteral opening (payload packed bytes) := by
  change {after packed bytes with ex:=mark.rollback written.ex} = _
  rw [rollback_execution_component]
  rfl

theorem rollback_vector (packed : Bool) (bytes : Roadmap.Bytes) :
    let final := {after packed bytes with ex:=mark.rollback (after packed bytes).ex}
    (final.ex.transient.cells self).read scratch = some (.bool false) ∧
    (final.ex.transient.cells sender).read scratch = some (.bool true) ∧
    final.ex.journal.length = 1 ∧ final.heap.next = 2 ∧
    final.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    final.heap.get 1 = some ⟨.bytes .memory,.bytes (payload packed bytes)⟩ ∧
    final.ex.world = populated.ex.world ∧ final.events = populated.events ∧
    final.logs = populated.logs ∧ final.fnLocals = populated.fnLocals := by
  rw [rollback_complete_state]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem end_preserves_fields (packed : Bool) (bytes : Roadmap.Bytes) :
    (SourceTransient.endExecution (after packed bytes)).ex.world = (after packed bytes).ex.world ∧
    (SourceTransient.endExecution (after packed bytes)).ex.journal = [] ∧
    (SourceTransient.endExecution (after packed bytes)).heap = (after packed bytes).heap ∧
    (SourceTransient.endExecution (after packed bytes)).events = (after packed bytes).events ∧
    (SourceTransient.endExecution (after packed bytes)).logs = (after packed bytes).logs ∧
    (SourceTransient.endExecution (after packed bytes)).fnLocals = (after packed bytes).fnLocals :=
  SourceTransient.end_execution_fields (after packed bytes)

theorem end_reads (pipeline : Roadmap.Pipeline) (packed : Bool) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,SourceTransient.endExecution (after packed bytes)) =
      (.ok (.val (.bool false)),(locals,SourceTransient.endExecution (after packed bytes))) ∧
    (Source.evalE (global pipeline) {frame with this:=sender} 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,SourceTransient.endExecution (after packed bytes)) =
      (.ok (.val (.bool false)),(locals,SourceTransient.endExecution (after packed bytes))) := ⟨rfl,rfl⟩

theorem wrong_automatic_rollback (pipeline : Roadmap.Pipeline) (packed : Bool) (bytes : Roadmap.Bytes) :
    (execution pipeline false packed bytes).run (Source.L0 E,opening) ≠
      (.error (.revert (payload packed bytes)),
        (Source.L0 E,SourceKeccak.afterLiteral opening (payload packed bytes))) := by
  rw [sequence_complete pipeline packed bytes 0]
  intro same
  have journals := congrArg (fun result => result.2.2.ex.journal.length) same
  change 2 = 1 at journals
  cases journals

theorem wrong_payload (pipeline : Roadmap.Pipeline) :
    (execution pipeline false true binary).run (Source.L0 E,opening) ≠
      (.error (.revert [0,255,127]),(Source.L0 E,after true binary)) := by
  rw [sequence_complete pipeline true binary 0]
  intro same
  cases same

theorem literal_cases (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (execution pipeline false packed []).run (Source.L0 E,opening) =
      (.error (.revert (payload packed [])),(Source.L0 E,after packed [])) ∧
    (execution pipeline false packed binary).run (Source.L0 E,opening) =
      (.error (.revert (payload packed binary)),(Source.L0 E,after packed binary)) ∧
    (execution pipeline false packed SourceAbiControls.long33).run (Source.L0 E,opening) =
      (.error (.revert (payload packed SourceAbiControls.long33)),(Source.L0 E,after packed SourceAbiControls.long33)) :=
  ⟨sequence_complete pipeline packed [] 0,sequence_complete pipeline packed binary 0,
    sequence_complete pipeline packed SourceAbiControls.long33 0⟩

#print axioms complete_vector
#print axioms same_invocation_read
#print axioms other_owner_read
#print axioms other_path_read
#print axioms rollback_execution_component
#print axioms rollback_complete_state
#print axioms rollback_vector
#print axioms end_preserves_fields
#print axioms end_reads
#print axioms wrong_automatic_rollback
#print axioms wrong_payload
#print axioms literal_cases
#print axioms assignment_statement
#print axioms declaration_statement
#print axioms sequence_complete
#print axioms block_execution
#print axioms static_before_allocation
#print axioms prefix_timeout
#print axioms zero_timeout
end Solidity.Lowering.V08.SourceTransientRethrowControls
