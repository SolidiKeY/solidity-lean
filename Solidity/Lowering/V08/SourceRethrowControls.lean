import Solidity.Lowering.V08.SourceRethrow
import Solidity.Lowering.V08.SourceAbiControls

/-! Populated allocation/rethrow controls. Complete Source machine equalities
retain world/transient/journal/heap/events/logs/fnLocals. No Source catch selection
or target rollback is claimed. All predecessors' byte/vector controls remain. -/
namespace Solidity.Lowering.V08.SourceRethrowControls
open Solidity Source
open SourceCustomErrorControls

def after (bytes : Roadmap.Bytes) : Source.St E := SourceKeccak.afterLiteral populated bytes

theorem complete (pipeline : Roadmap.Pipeline) (static : Bool) (bytes : Roadmap.Bytes) :
    (SourceRethrow.allocated (global pipeline) {frame with static:=static} 4 1 bytes).run
      (locals,populated) = (.error (.revert bytes),(locals,after bytes)) :=
  SourceRethrow.literal_rethrow (global pipeline) {frame with static:=static} 0 0 bytes locals populated

theorem payload_cases (pipeline : Roadmap.Pipeline) (static : Bool) :
    (SourceRethrow.allocated (global pipeline) {frame with static:=static} 4 1 []).run
      (locals,populated) = (.error (.revert []),(locals,after [])) ∧
    (SourceRethrow.allocated (global pipeline) {frame with static:=static} 4 1 binary).run
      (locals,populated) = (.error (.revert binary),(locals,after binary)) ∧
    (SourceRethrow.allocated (global pipeline) {frame with static:=static} 4 1 SourceAbiControls.long33).run
      (locals,populated) = (.error (.revert SourceAbiControls.long33),(locals,after SourceAbiControls.long33)) :=
  ⟨complete pipeline static [],complete pipeline static binary,complete pipeline static SourceAbiControls.long33⟩

/-- The entire existing ordered field vector is retained, with both old/new
objects and exact allocator. Complete machine equality above covers all fields. -/
theorem complete_vector (bytes : Roadmap.Bytes) :
    ((after bytes).ex.world.accounts sender).balance = 93 ∧
    ((after bytes).ex.world.accounts self).balance = 7 ∧
    ((after bytes).ex.world.accounts self).code = some 0 ∧
    ((after bytes).ex.world.accounts self).nonce = 1 ∧
    ((after bytes).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    ((after bytes).ex.transient.cells self).read scratch = some (.bool true) ∧
    (after bytes).ex.journal.length = 3 ∧ (after bytes).heap.next = 2 ∧
    (after bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (after bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (after bytes).events = populated.events ∧ (after bytes).logs = populated.logs ∧
    (after bytes).fnLocals = populated.fnLocals :=
  SourceAbiControls.literal_vector true bytes

/-- A real successful source prefix changes the caller local, then the
allocation/rethrow preserves that reached local rather than restoring true. -/
def withWrite (pipeline : Roadmap.Pipeline) (static : Bool) (bytes : Roadmap.Bytes) :
    Source.EM E [.bool] (Source.Out E.layout [.bytes .memory] [.bytes .memory] × Source.Locals E.layout []) := do
  let _ ← Source.evalE (global pipeline) {frame with static:=static} 3 setFalse
  SourceRethrow.allocated (global pipeline) {frame with static:=static} 4 1 bytes

theorem reached_write (pipeline : Roadmap.Pipeline) (static : Bool) (bytes : Roadmap.Bytes) :
    (withWrite pipeline static bytes).run (locals,populated) =
      (.error (.revert bytes),(.cons (.bool false) .nil,after bytes)) := by
  have write := SourceCustomErrorControls.assign_false pipeline static 0 populated
  have done := SourceRethrow.literal_rethrow (global pipeline) {frame with static:=static}
    0 0 bytes (.cons (.bool false) .nil) populated
  simp only [ExceptT.run] at write done
  simp only [withWrite,bind,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,write,done,after]

theorem old_pointer (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 1 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl 0) .nil)).run (Source.L0 E,after binary) =
        (.error (.revert [0,255]),(Source.L0 E,after binary)) :=
  SourceCustomErrorFailures.rethrow_bytes (global pipeline) {frame with static:=static}
    0 .here _ _ 0 [0,255] rfl rfl

theorem statement_low (pipeline : Roadmap.Pipeline) (static : Bool) :
    (SourceRethrow.allocated (global pipeline) {frame with static:=static} 4 0 binary).run
      (locals,populated) = (.error .timeout,(locals,after binary)) :=
  SourceRethrow.statement_timeout (global pipeline) {frame with static:=static} 0 binary locals populated

theorem allocation_low (pipeline : Roadmap.Pipeline) (static : Bool) :
    (SourceRethrow.allocated (global pipeline) {frame with static:=static} 0 1 binary).run
      (locals,populated) = (.error .timeout,(locals,populated)) :=
  SourceRethrow.allocation_timeout (global pipeline) {frame with static:=static} 1 binary locals populated

theorem wrong_payload (pipeline : Roadmap.Pipeline) (static : Bool) :
    (SourceRethrow.allocated (global pipeline) {frame with static:=static} 4 1 binary).run
      (locals,populated) ≠ (.error (.revert [0,128,255]),(locals,after binary)) := by
  rw [complete]
  intro same
  have bytes : binary = [0,128,255] := Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  exact (by decide +kernel : binary ≠ [0,128,255]) bytes

theorem wrong_unallocated_state (pipeline : Roadmap.Pipeline) (static : Bool) :
    (SourceRethrow.allocated (global pipeline) {frame with static:=static} 4 1 []).run
      (locals,populated) ≠ (.error (.revert []),(locals,populated)) := by
  rw [complete]
  intro same
  have heaps := congrArg (fun result => result.2.2.heap.next) same
  change 2 = 1 at heaps
  cases heaps

theorem wrong_reverted_local (pipeline : Roadmap.Pipeline) (static : Bool) :
    (withWrite pipeline static binary).run (locals,populated) ≠
      (.error (.revert binary),(locals,after binary)) := by
  rw [reached_write]
  intro same
  have observedLocal := congrArg (fun result => result.2.1.get (Source.Idx.here : Source.Idx [.bool] .bool)) same
  cases observedLocal

theorem timeout_is_not_empty_revert : (Source.Halt.timeout) ≠ .revert [] := by decide +kernel

theorem intrinsic_empty {C : Contract} {Δ : Ctx} (state : State C Δ) :
    (Stmt.revertData [.bytes []] : Stmt C Δ Δ).runC state = .error .revert :=
  SourceRethrow.intrinsic_rethrow [] state

theorem intrinsic_binary {C : Contract} {Δ : Ctx} (state : State C Δ) :
    (Stmt.revertData [.bytes binary] : Stmt C Δ Δ).runC state = .error (.revertWith binary) :=
  SourceRethrow.intrinsic_rethrow binary state

theorem old_pointer_not_fresh (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 1 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl 0) .nil)).run (Source.L0 E,after binary) ≠
        (.error (.revert binary),(Source.L0 E,after binary)) := by
  rw [old_pointer]
  intro same
  have bytes : [0,255] = binary := Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  exact (by decide +kernel : [0,255] ≠ binary) bytes

theorem intrinsic_long33 {C : Contract} {Δ : Ctx} (state : State C Δ) :
    (Stmt.revertData [.bytes SourceAbiControls.long33] : Stmt C Δ Δ).runC state =
      .error (.revertWith SourceAbiControls.long33) :=
  SourceRethrow.intrinsic_rethrow SourceAbiControls.long33 state

#print axioms old_pointer_not_fresh
#print axioms intrinsic_long33

#print axioms complete
#print axioms payload_cases
#print axioms complete_vector
#print axioms reached_write
#print axioms old_pointer
#print axioms statement_low
#print axioms allocation_low
#print axioms wrong_payload
#print axioms wrong_unallocated_state
#print axioms wrong_reverted_local
#print axioms timeout_is_not_empty_revert
#print axioms intrinsic_empty
#print axioms intrinsic_binary
def mixedAfter (pipeline : Roadmap.Pipeline) : Source.St E :=
  SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
    (SourceAbiControls.data true pipeline)

def mixed (pipeline : Roadmap.Pipeline) (static : Bool) (horizon : Nat := 17) :
    Source.EM E [.bool] (Source.Out E.layout [.bytes .memory] [.bytes .memory] × Source.Locals E.layout []) :=
  SourceRethrow.fromExpression (global pipeline) {frame with static:=static} horizon 1
    (.abiEncode .encodePacked SourceAbiControls.arguments)

/-- Real argument write/read/hash and both allocations are reached before
canonical rethrow reads the actual returned pointer2, not the older pointer1. -/
theorem mixed_complete (pipeline : Roadmap.Pipeline) (static : Bool) :
    (mixed pipeline static).run (locals,populated) =
      (.error (.revert (SourceAbiControls.data true pipeline)),
        (.cons (.bool false) .nil,mixedAfter pipeline)) := by
  have evaluation := SourceAbiControls.mixed_complete pipeline static true
  have memory := SourceRethrow.allocated_object (SourceKeccak.afterLiteral populated binary)
    (SourceAbiControls.data true pipeline)
  exact SourceRethrow.expression_rethrow (global pipeline) {frame with static:=static}
    17 0 (.abiEncode .encodePacked SourceAbiControls.arguments)
    locals (.cons (.bool false) .nil) populated (mixedAfter pipeline) 2
    (SourceAbiControls.data true pipeline) evaluation memory

theorem mixed_vector (pipeline : Roadmap.Pipeline) :
    ((mixedAfter pipeline).ex.world.accounts sender).balance = 93 ∧
    ((mixedAfter pipeline).ex.world.accounts self).balance = 7 ∧
    ((mixedAfter pipeline).ex.world.accounts self).code = some 0 ∧
    ((mixedAfter pipeline).ex.world.accounts self).nonce = 1 ∧
    ((mixedAfter pipeline).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    ((mixedAfter pipeline).ex.transient.cells self).read scratch = some (.bool true) ∧
    (mixedAfter pipeline).ex.journal.length = 3 ∧ (mixedAfter pipeline).heap.next = 3 ∧
    (mixedAfter pipeline).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (mixedAfter pipeline).heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ ∧
    (mixedAfter pipeline).heap.get 2 = some ⟨.bytes .memory,.bytes (SourceAbiControls.data true pipeline)⟩ ∧
    (mixedAfter pipeline).events = populated.events ∧ (mixedAfter pipeline).logs = populated.logs ∧
    (mixedAfter pipeline).fnLocals = populated.fnLocals :=
  SourceAbiControls.mixed_vector pipeline true

theorem mixed_transport {C : Contract} {Δ : Ctx} (pipeline : Roadmap.Pipeline)
    (static : Bool) (target : State C Δ) :
    (mixed pipeline static).run (locals,populated) =
      (.error (.revert (SourceAbiControls.data true pipeline)),
        (.cons (.bool false) .nil,mixedAfter pipeline)) ∧
    (Stmt.revertData [.bytes (SourceAbiControls.data true pipeline)] : Stmt C Δ Δ).runC target =
      .error (.revertWith (SourceAbiControls.data true pipeline)) := by
  constructor
  · exact mixed_complete pipeline static
  · rw [SourceRethrow.intrinsic_rethrow]
    rfl

theorem wrong_mixed_encoding (pipeline : Roadmap.Pipeline) (static : Bool) :
    (mixed pipeline static).run (locals,populated) ≠
      (.error (.revert (SourceAbiControls.data false pipeline)),
        (.cons (.bool false) .nil,mixedAfter pipeline)) := by
  rw [mixed_complete]
  intro same
  have bytes := Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  have lengths := congrArg List.length bytes
  rw [(SourceAbiControls.mixed_lengths pipeline).2,
    (SourceAbiControls.mixed_lengths pipeline).1] at lengths
  cases lengths

/-- At this actual expression horizon the local write happened, but the hash
and both allocations did not. This timeout is propagated, not replaced by rethrow. -/
theorem mixed_timeout_after_effects (pipeline : Roadmap.Pipeline) (static : Bool) :
    (mixed pipeline static 6).run (locals,populated) =
      (.error .timeout,(.cons (.bool false) .nil,populated)) :=
  SourceRethrow.expression_failure (global pipeline) {frame with static:=static} 6 1
    (.abiEncode .encodePacked SourceAbiControls.arguments) locals (.cons (.bool false) .nil)
    populated populated .timeout (SourceAbiControls.insufficient_after_effects pipeline static true)

#print axioms mixed_complete
#print axioms mixed_vector
#print axioms mixed_transport
#print axioms wrong_mixed_encoding
#print axioms mixed_timeout_after_effects

end Solidity.Lowering.V08.SourceRethrowControls
