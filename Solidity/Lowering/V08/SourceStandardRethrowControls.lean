import Solidity.Lowering.V08.SourceStandardRethrow
import Solidity.Lowering.V08.SourceRethrowControls

/-! Populated STANDARD encoding/rethrow applications over actual Source execution.
All existing producers and full vectors are retained. Supplied intrinsic execution
is separate from compiler selection/catch/frame/bytecode adequacy. -/
namespace Solidity.Lowering.V08.SourceStandardRethrowControls
open Solidity Source
open SourceCustomErrorControls

def after (pipeline : Roadmap.Pipeline) : Source.St E :=
  SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
    (SourceAbiControls.data false pipeline)
def reversedAfter (pipeline : Roadmap.Pipeline) : Source.St E :=
  SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
    (SourceAbiControls.reversedData pipeline)
def standard (pipeline : Roadmap.Pipeline) (static : Bool)
    (expressionHorizon : Nat := 17) (statementHorizon : Nat := 1) :=
  SourceRethrow.fromExpression (global pipeline) {frame with static:=static}
    expressionHorizon statementHorizon (.abiEncode .encode SourceAbiControls.arguments)
def reversed (pipeline : Roadmap.Pipeline) (static : Bool) :=
  SourceRethrow.fromExpression (global pipeline) {frame with static:=static}
    17 1 (.abiEncode .encode SourceAbiControls.reversedArguments)

/-- A projection only for word observations below; full result/state equalities
are separately proved and never inferred from this lossy observer. -/
def revertBytes {E : Source.Env} {Γ : RCtx} {α : Type}
    (result : Source.R α × (Source.Locals E.layout Γ × Source.St E)) : Option Roadmap.Bytes :=
  match result.1 with
  | .error (.revert bytes) => some bytes
  | _ => none

theorem standard_complete (pipeline : Roadmap.Pipeline) (static : Bool) :
    (standard pipeline static).run (locals,populated) =
      (.error (.revert (SourceAbiControls.data false pipeline)),
        (.cons (.bool false) .nil,after pipeline)) :=
  SourceRethrow.expression_rethrow (global pipeline) {frame with static:=static} 17 0
    (.abiEncode .encode SourceAbiControls.arguments) locals (.cons (.bool false) .nil)
    populated (after pipeline) 2 (SourceAbiControls.data false pipeline)
    (SourceAbiControls.mixed_complete pipeline static false)
    (SourceRethrow.allocated_object (SourceKeccak.afterLiteral populated binary) _)

theorem standard_vector (pipeline : Roadmap.Pipeline) :
    ((after pipeline).ex.world.accounts sender).balance.val = 93 ∧
    ((after pipeline).ex.world.accounts self).balance.val = 7 ∧
    ((after pipeline).ex.world.accounts self).code = some 0 ∧
    ((after pipeline).ex.world.accounts self).nonce = 1 ∧
    ((after pipeline).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    ((after pipeline).ex.transient.cells self).read scratch = some (.bool true) ∧
    (after pipeline).ex.journal.length = 3 ∧ (after pipeline).heap.next = 3 ∧
    (after pipeline).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (after pipeline).heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ ∧
    (after pipeline).heap.get 2 = some ⟨.bytes .memory,.bytes (SourceAbiControls.data false pipeline)⟩ ∧
    (after pipeline).events = populated.events ∧ (after pipeline).logs = populated.logs ∧
    (after pipeline).fnLocals = populated.fnLocals :=
  SourceAbiControls.mixed_vector pipeline false

theorem reversed_complete (pipeline : Roadmap.Pipeline) (static : Bool) :
    (reversed pipeline static).run (locals,populated) =
      (.error (.revert (SourceAbiControls.reversedData pipeline)),
        (.cons (.bool false) .nil,reversedAfter pipeline)) :=
  SourceRethrow.expression_rethrow (global pipeline) {frame with static:=static} 17 0
    (.abiEncode .encode SourceAbiControls.reversedArguments) locals (.cons (.bool false) .nil)
    populated (reversedAfter pipeline) 2 (SourceAbiControls.reversedData pipeline)
    (SourceAbiControls.reversed_execution pipeline static)
    (SourceRethrow.allocated_object (SourceKeccak.afterLiteral populated binary) _)

theorem reversed_vector (pipeline : Roadmap.Pipeline) :
    ((reversedAfter pipeline).ex.world.accounts sender).balance.val = 93 ∧
    ((reversedAfter pipeline).ex.world.accounts self).balance.val = 7 ∧
    ((reversedAfter pipeline).ex.world.accounts self).code = some 0 ∧
    ((reversedAfter pipeline).ex.world.accounts self).nonce = 1 ∧
    ((reversedAfter pipeline).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    ((reversedAfter pipeline).ex.transient.cells self).read scratch = some (.bool true) ∧
    (reversedAfter pipeline).ex.journal.length = 3 ∧ (reversedAfter pipeline).heap.next = 3 ∧
    (reversedAfter pipeline).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (reversedAfter pipeline).heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ ∧
    (reversedAfter pipeline).heap.get 2 = some ⟨.bytes .memory,.bytes (SourceAbiControls.reversedData pipeline)⟩ ∧
    (reversedAfter pipeline).events = populated.events ∧ (reversedAfter pipeline).logs = populated.logs ∧
    (reversedAfter pipeline).fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem exact_size (pipeline : Roadmap.Pipeline) (static : Bool) :
    (revertBytes ((standard pipeline static).run (locals,populated))).map List.length = some 320 := by
  rw [standard_complete]
  change some (SourceAbiControls.data false pipeline).length = some 320
  exact congrArg some (SourceAbiControls.mixed_lengths pipeline).1

theorem full_offset_words (pipeline : Roadmap.Pipeline) (static : Bool) :
    (revertBytes ((standard pipeline static).run (locals,populated))).map (fun bytes => bytes.take 32) =
      some (Source.wordBytes (Source.toWord 160)) ∧
    (revertBytes ((standard pipeline static).run (locals,populated))).map (fun bytes => (bytes.drop 96).take 32) =
      some (Source.wordBytes (Source.toWord 224)) ∧
    (revertBytes ((reversed pipeline static).run (locals,populated))).map (fun bytes => (bytes.drop 96).take 32) =
      some (Source.wordBytes (Source.toWord 256)) := by
  rw [standard_complete,reversed_complete]
  exact ⟨congrArg some (SourceAbiControls.complete_offset_words pipeline).1,
    congrArg some (SourceAbiControls.complete_offset_words pipeline).2.1,
    congrArg some (SourceAbiControls.complete_offset_words pipeline).2.2⟩

theorem standard_not_packed (pipeline : Roadmap.Pipeline) (static : Bool) :
    (standard pipeline static).run (locals,populated) ≠
      (SourceRethrowControls.mixed pipeline static).run (locals,populated) := by
  rw [standard_complete,SourceRethrowControls.mixed_complete]
  intro same
  have bytes := Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  have lengths := congrArg List.length bytes
  rw [(SourceAbiControls.mixed_lengths pipeline).1,(SourceAbiControls.mixed_lengths pipeline).2] at lengths
  cases lengths

theorem standard_not_reversed (pipeline : Roadmap.Pipeline) (static : Bool) :
    (standard pipeline static).run (locals,populated) ≠
      (reversed pipeline static).run (locals,populated) := by
  rw [standard_complete,reversed_complete]
  intro same
  exact SourceAbiControls.different_ordered_bytes pipeline
    (Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same)))

theorem stale_hash_pointer (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 1 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl 1) .nil)).run (Source.L0 E,after pipeline) =
        (.error (.revert binary),(Source.L0 E,after pipeline)) :=
  SourceCustomErrorFailures.rethrow_bytes (global pipeline) {frame with static:=static}
    0 .here _ _ 1 binary rfl rfl

theorem stale_not_standard (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 1 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl 1) .nil)).run (Source.L0 E,after pipeline) ≠
        (.error (.revert (SourceAbiControls.data false pipeline)),(Source.L0 E,after pipeline)) := by
  rw [stale_hash_pointer]
  intro same
  have bytes := Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  have lengths := congrArg List.length bytes
  rw [(SourceAbiControls.mixed_lengths pipeline).1] at lengths
  change 3 = 320 at lengths
  cases lengths

theorem intrinsic_transport {C : Contract} {Δ : Ctx} (pipeline : Roadmap.Pipeline)
    (static : Bool) (target : State C Δ) :
    (standard pipeline static).run (locals,populated) =
      (.error (.revert (SourceAbiControls.data false pipeline)),(.cons (.bool false) .nil,after pipeline)) ∧
    (Stmt.revertData [.bytes (SourceAbiControls.data false pipeline)] : Stmt C Δ Δ).runC target =
      .error (THalt.ofData (SourceAbiControls.data false pipeline)) :=
  ⟨standard_complete pipeline static,SourceRethrow.intrinsic_rethrow _ target⟩

theorem allocation_timeout (pipeline : Roadmap.Pipeline) (static : Bool) :
    (standard pipeline static 0).run (locals,populated) = (.error .timeout,(locals,populated)) :=
  SourceRethrow.expression_failure (global pipeline) {frame with static:=static} 0 1
    (.abiEncode .encode SourceAbiControls.arguments) locals locals populated populated .timeout rfl

theorem argument_timeout (pipeline : Roadmap.Pipeline) (static : Bool) :
    (standard pipeline static 6).run (locals,populated) =
      (.error .timeout,(.cons (.bool false) .nil,populated)) :=
  SourceRethrow.expression_failure (global pipeline) {frame with static:=static} 6 1
    (.abiEncode .encode SourceAbiControls.arguments) locals (.cons (.bool false) .nil)
    populated populated .timeout (SourceAbiControls.insufficient_after_effects pipeline static false)

theorem statement_timeout (pipeline : Roadmap.Pipeline) (static : Bool) :
    (standard pipeline static 17 0).run (locals,populated) =
      (.error .timeout,(.cons (.bool false) .nil,after pipeline)) :=
  SourceStandardRethrow.expression_statement_timeout (global pipeline) {frame with static:=static}
    17 (.abiEncode .encode SourceAbiControls.arguments) locals (.cons (.bool false) .nil)
    populated (after pipeline) 2 (SourceAbiControls.mixed_complete pipeline static false)

theorem literal_complete (pipeline : Roadmap.Pipeline) (static : Bool) (bytes : Roadmap.Bytes) :
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} 4 1 bytes).run (locals,populated) =
      (.error (.revert (Source.abiLayout [(true,bytes)])),
       (locals,SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)]))) :=
  SourceStandardRethrow.literal_execution (global pipeline) {frame with static:=static} 0 0 bytes locals populated

theorem literal_cases (pipeline : Roadmap.Pipeline) (static : Bool) :
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} 4 1 []).run (locals,populated) =
      (.error (.revert (Source.abiLayout [(true,[])])),(locals,SourceKeccak.afterLiteral populated (Source.abiLayout [(true,[])]))) ∧
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} 4 1 binary).run (locals,populated) =
      (.error (.revert (Source.abiLayout [(true,binary)])),(locals,SourceKeccak.afterLiteral populated (Source.abiLayout [(true,binary)]))) ∧
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} 4 1 SourceAbiControls.long33).run (locals,populated) =
      (.error (.revert (Source.abiLayout [(true,SourceAbiControls.long33)])),
       (locals,SourceKeccak.afterLiteral populated (Source.abiLayout [(true,SourceAbiControls.long33)]))) :=
  ⟨literal_complete pipeline static [],literal_complete pipeline static binary,
    literal_complete pipeline static SourceAbiControls.long33⟩

theorem literal_vector (bytes : Roadmap.Bytes) :
    ((SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).ex.world.accounts sender).balance.val = 93 ∧
    ((SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).ex.world.accounts self).balance.val = 7 ∧
    ((SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).ex.world.accounts self).code = some 0 ∧
    ((SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).ex.world.accounts self).nonce = 1 ∧
    ((SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    ((SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).ex.transient.cells self).read scratch = some (.bool true) ∧
    (SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).ex.journal.length = 3 ∧
    (SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).heap.next = 2 ∧
    (SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).heap.get 1 = some ⟨.bytes .memory,.bytes (Source.abiLayout [(true,bytes)])⟩ ∧
    (SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).events = populated.events ∧
    (SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).logs = populated.logs ∧
    (SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).fnLocals = populated.fnLocals :=
  SourceAbiControls.literal_vector false bytes

theorem literal_payload_lengths (pipeline : Roadmap.Pipeline) (static : Bool) :
    ((revertBytes ((SourceStandardRethrow.literal (global pipeline) {frame with static:=static} 4 1 []).run (locals,populated))).map List.length,
     (revertBytes ((SourceStandardRethrow.literal (global pipeline) {frame with static:=static} 4 1 binary).run (locals,populated))).map List.length,
     (revertBytes ((SourceStandardRethrow.literal (global pipeline) {frame with static:=static} 4 1 SourceAbiControls.long33).run (locals,populated))).map List.length) =
      (some 64,some 96,some 128) := by
  rw [literal_complete,literal_complete,literal_complete]
  exact congrArg (fun sizes : Nat × Nat × Nat => (some sizes.1,some sizes.2.1,some sizes.2.2))
    SourceAbiControls.empty_binary_unaligned_lengths

theorem empty_not_raw_empty (pipeline : Roadmap.Pipeline) (static : Bool) :
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} 4 1 []).run (locals,populated) ≠
      (.error (.revert []),(locals,SourceKeccak.afterLiteral populated (Source.abiLayout [(true,[])]))) := by
  rw [literal_complete]
  intro same
  have bytes := Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  have lengths := congrArg List.length bytes
  have actual : (Source.abiLayout [(true,[])]).length = 64 :=
    congrArg Prod.fst SourceAbiControls.empty_binary_unaligned_lengths
  rw [actual] at lengths
  cases lengths

#print axioms standard_complete
#print axioms standard_vector
#print axioms reversed_complete
#print axioms reversed_vector
#print axioms exact_size
#print axioms full_offset_words
#print axioms standard_not_packed
#print axioms standard_not_reversed
#print axioms stale_hash_pointer
#print axioms stale_not_standard
#print axioms intrinsic_transport
#print axioms allocation_timeout
#print axioms argument_timeout
#print axioms statement_timeout
#print axioms literal_complete
#print axioms literal_cases
#print axioms literal_vector
#print axioms literal_payload_lengths
#print axioms empty_not_raw_empty
end Solidity.Lowering.V08.SourceStandardRethrowControls
