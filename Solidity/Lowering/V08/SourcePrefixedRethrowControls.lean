import Solidity.Lowering.V08.SourceStandardRethrowControls

/-! Further G21 reference-value application. Existing selector/signature Source
producers are consumed; no signature-profile premise, decoder/emitter, compiler
selection, catch/frame adequacy or world rollback is inferred. -/
namespace Solidity.Lowering.V08.SourcePrefixedRethrowControls
open Solidity Source
open SourceCustomErrorControls

def signaturePrefix (pipeline : Roadmap.Pipeline) : Roadmap.Bytes :=
  (Source.wordBytes ((global pipeline).fixed.hash [])).take 4

def after (prefixData : Roadmap.Bytes) (pipeline : Roadmap.Pipeline) : Source.St E :=
  SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
    (prefixData ++ SourceAbiControls.data false pipeline)

def memoryAfter (pipeline : Roadmap.Pipeline) : Source.St E :=
  SourceKeccak.afterLiteral (SourceKeccak.afterLiteral (SourceAbiControls.afterSignature populated) binary)
    (signaturePrefix pipeline ++ SourceAbiControls.data false pipeline)

def selector (pipeline : Roadmap.Pipeline) (static : Bool) :=
  SourceRethrow.fromExpression (global pipeline) {frame with static:=static} 18 1
    (.abiEncode .encodeWithSelector SourceAbiControls.selectorArgs)

def signature (pipeline : Roadmap.Pipeline) (static : Bool) :=
  SourceRethrow.fromExpression (global pipeline) {frame with static:=static} 18 1
    (.abiEncode .encodeWithSignature SourceAbiControls.signatureArgs)

def memorySignature (pipeline : Roadmap.Pipeline) (static : Bool)
    (expressionHorizon : Nat := 18) (statementHorizon : Nat := 1) :=
  SourceRethrow.fromExpression (global pipeline) {frame with static:=static}
    expressionHorizon statementHorizon (.abiEncode .encodeWithSignature SourceAbiControls.memorySignatureArgs)

theorem selector_complete (pipeline : Roadmap.Pipeline) (static : Bool) :
    (selector pipeline static).run (locals,populated) =
      (.error (.revert (SourceAbiControls.selectorBytes ++ SourceAbiControls.data false pipeline)),
       (.cons (.bool false) .nil,after SourceAbiControls.selectorBytes pipeline)) :=
  SourceRethrow.expression_rethrow (global pipeline) {frame with static:=static} 18 0
    (.abiEncode .encodeWithSelector SourceAbiControls.selectorArgs) locals (.cons (.bool false) .nil)
    populated _ 2 _ (SourceAbiControls.selector_mixed_complete pipeline static)
    (SourceRethrow.allocated_object (SourceKeccak.afterLiteral populated binary) _)

theorem signature_complete (pipeline : Roadmap.Pipeline) (static : Bool) :
    (signature pipeline static).run (locals,populated) =
      (.error (.revert (signaturePrefix pipeline ++ SourceAbiControls.data false pipeline)),
       (.cons (.bool false) .nil,after (signaturePrefix pipeline) pipeline)) :=
  SourceRethrow.expression_rethrow (global pipeline) {frame with static:=static} 18 0
    (.abiEncode .encodeWithSignature SourceAbiControls.signatureArgs) locals (.cons (.bool false) .nil)
    populated _ 2 _ (SourceAbiControls.signature_mixed_complete pipeline static)
    (SourceRethrow.allocated_object (SourceKeccak.afterLiteral populated binary) _)

theorem memory_complete (pipeline : Roadmap.Pipeline) (static : Bool) :
    (memorySignature pipeline static).run (locals,populated) =
      (.error (.revert (signaturePrefix pipeline ++ SourceAbiControls.data false pipeline)),
       (.cons (.bool false) .nil,memoryAfter pipeline)) :=
  SourceRethrow.expression_rethrow (global pipeline) {frame with static:=static} 18 0
    (.abiEncode .encodeWithSignature SourceAbiControls.memorySignatureArgs) locals (.cons (.bool false) .nil)
    populated _ 3 _ (SourceAbiControls.memory_signature_complete pipeline static)
    (SourceRethrow.allocated_object (SourceKeccak.afterLiteral (SourceAbiControls.afterSignature populated) binary) _)

/-- This vector retains the allocated string identity, not a bytes stand-in. -/
theorem memory_vector (pipeline : Roadmap.Pipeline) :
    ((memoryAfter pipeline).ex.world.accounts sender).balance = 93 ∧
    ((memoryAfter pipeline).ex.world.accounts self).balance = 7 ∧
    ((memoryAfter pipeline).ex.world.accounts self).code = some 0 ∧
    ((memoryAfter pipeline).ex.world.accounts self).nonce = 1 ∧
    ((memoryAfter pipeline).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    ((memoryAfter pipeline).ex.transient.cells self).read scratch = some (.bool true) ∧
    (memoryAfter pipeline).ex.journal.length = 3 ∧ (memoryAfter pipeline).heap.next = 4 ∧
    (memoryAfter pipeline).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (memoryAfter pipeline).heap.get 1 = some ⟨.string .memory,.string []⟩ ∧
    (memoryAfter pipeline).heap.get 2 = some ⟨.bytes .memory,.bytes binary⟩ ∧
    (memoryAfter pipeline).heap.get 3 = some ⟨.bytes .memory,.bytes (signaturePrefix pipeline ++ SourceAbiControls.data false pipeline)⟩ ∧
    (memoryAfter pipeline).events = populated.events ∧ (memoryAfter pipeline).logs = populated.logs ∧
    (memoryAfter pipeline).fnLocals = populated.fnLocals :=
  SourceAbiControls.memory_signature_vector pipeline

theorem selector_vector (pipeline : Roadmap.Pipeline) :
    let final := after SourceAbiControls.selectorBytes pipeline
    (final.ex.world.accounts sender).balance = 93 ∧
    (final.ex.world.accounts self).balance = 7 ∧
    (final.ex.world.accounts self).code = some 0 ∧ (final.ex.world.accounts self).nonce = 1 ∧
    (final.ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (final.ex.transient.cells self).read scratch = some (.bool true) ∧
    final.ex.journal.length = 3 ∧ final.heap.next = 3 ∧
    final.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    final.heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ ∧
    final.heap.get 2 = some ⟨.bytes .memory,.bytes (SourceAbiControls.selectorBytes ++ SourceAbiControls.data false pipeline)⟩ ∧
    final.events = populated.events ∧ final.logs = populated.logs ∧ final.fnLocals = populated.fnLocals :=
  SourceAbiControls.prefixed_complete_vector SourceAbiControls.selectorBytes pipeline

theorem identical_payload (pipeline : Roadmap.Pipeline) (static : Bool) :
    SourceStandardRethrowControls.revertBytes ((signature pipeline static).run (locals,populated)) =
      SourceStandardRethrowControls.revertBytes ((memorySignature pipeline static).run (locals,populated)) := by
  rw [signature_complete,memory_complete]
  rfl

theorem distinct_machine_allocation (pipeline : Roadmap.Pipeline) (static : Bool) :
    (signature pipeline static).run (locals,populated) ≠
      (memorySignature pipeline static).run (locals,populated) := by
  rw [signature_complete,memory_complete]
  intro same
  have counters := congrArg (fun result => result.2.2.heap.next) same
  change 3 = 4 at counters
  cases counters

theorem selector_not_signature (pipeline : Roadmap.Pipeline) (static : Bool) :
    (selector pipeline static).run (locals,populated) ≠
      (signature pipeline static).run (locals,populated) := by
  rw [selector_complete,signature_complete]
  intro same
  have bytes := Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  have heads := congrArg List.head? bytes
  simp only [signaturePrefix,SourceAbiControls.empty_signature_prefix,SourceAbiControls.selectorBytes,
    List.cons_append,List.head?_cons] at heads
  exact (by decide +kernel : (some (0:UInt8)) ≠ some 197) heads

theorem memory_payload_length (pipeline : Roadmap.Pipeline) (static : Bool) :
    (SourceStandardRethrowControls.revertBytes ((memorySignature pipeline static).run (locals,populated))).map List.length =
      some 324 := by
  rw [memory_complete]
  change some (signaturePrefix pipeline ++ SourceAbiControls.data false pipeline).length = some 324
  simp only [signaturePrefix,SourceAbiControls.empty_signature_prefix,List.length_append,
    List.length_cons,List.length_nil,(SourceAbiControls.mixed_lengths pipeline).1]

theorem memory_stale_pointer (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 1 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl 2) .nil)).run (Source.L0 E,memoryAfter pipeline) =
        (.error (.revert binary),(Source.L0 E,memoryAfter pipeline)) :=
  SourceCustomErrorFailures.rethrow_bytes (global pipeline) {frame with static:=static}
    0 .here _ _ 2 binary rfl rfl

theorem memory_stale_not_output (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 1 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl 2) .nil)).run (Source.L0 E,memoryAfter pipeline) ≠
        (.error (.revert (signaturePrefix pipeline ++ SourceAbiControls.data false pipeline)),
         (Source.L0 E,memoryAfter pipeline)) := by
  rw [memory_stale_pointer]
  intro same
  have bytes := Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  have lengths := congrArg List.length bytes
  simp only [binary,signaturePrefix,SourceAbiControls.empty_signature_prefix,List.length_append,
    List.length_cons,List.length_nil,(SourceAbiControls.mixed_lengths pipeline).1] at lengths
  cases lengths

theorem memory_statement_timeout (pipeline : Roadmap.Pipeline) (static : Bool) :
    (memorySignature pipeline static 18 0).run (locals,populated) =
      (.error .timeout,(.cons (.bool false) .nil,memoryAfter pipeline)) :=
  SourceStandardRethrow.expression_statement_timeout (global pipeline) {frame with static:=static}
    18 (.abiEncode .encodeWithSignature SourceAbiControls.memorySignatureArgs)
    locals (.cons (.bool false) .nil) populated _ 3
    (SourceAbiControls.memory_signature_complete pipeline static)

/-- A real string allocation survives a later argument timeout; neither hash
input nor result object has yet been allocated. This is not rollback. -/
theorem memory_argument_timeout (pipeline : Roadmap.Pipeline) (static : Bool) :
    (memorySignature pipeline static 7).run (locals,populated) =
      (.error .timeout,(.cons (.bool false) .nil,SourceAbiControls.afterSignature populated)) :=
  SourceRethrow.expression_failure (global pipeline) {frame with static:=static} 7 1
    (.abiEncode .encodeWithSignature SourceAbiControls.memorySignatureArgs)
    locals (.cons (.bool false) .nil) populated (SourceAbiControls.afterSignature populated) .timeout rfl

theorem memory_allocation_timeout (pipeline : Roadmap.Pipeline) (static : Bool) :
    (memorySignature pipeline static 0).run (locals,populated) =
      (.error .timeout,(locals,populated)) :=
  SourceRethrow.expression_failure (global pipeline) {frame with static:=static} 0 1
    (.abiEncode .encodeWithSignature SourceAbiControls.memorySignatureArgs) locals locals populated populated .timeout rfl

theorem memory_intrinsic_transport {C : Contract} {Δ : Ctx}
    (pipeline : Roadmap.Pipeline) (static : Bool) (target : State C Δ) :
    (memorySignature pipeline static).run (locals,populated) =
      (.error (.revert (signaturePrefix pipeline ++ SourceAbiControls.data false pipeline)),
       (.cons (.bool false) .nil,memoryAfter pipeline)) ∧
    (Stmt.revertData [.bytes (signaturePrefix pipeline ++ SourceAbiControls.data false pipeline)] : Stmt C Δ Δ).runC target =
      .error (THalt.ofData (signaturePrefix pipeline ++ SourceAbiControls.data false pipeline)) :=
  ⟨memory_complete pipeline static,SourceRethrow.intrinsic_rethrow _ target⟩

theorem signature_drop (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (signaturePrefix pipeline ++ bytes).drop 4 = bytes := by
  rw [signaturePrefix,SourceAbiControls.empty_signature_prefix]
  rfl

theorem drop_prefix_body (pipeline : Roadmap.Pipeline) (static : Bool) :
    (SourceStandardRethrowControls.revertBytes ((memorySignature pipeline static).run (locals,populated))).map
      (fun bytes => bytes.drop 4) =
      SourceStandardRethrowControls.revertBytes ((SourceStandardRethrowControls.standard pipeline static).run (locals,populated)) := by
  rw [memory_complete,SourceStandardRethrowControls.standard_complete]
  exact congrArg some (signature_drop pipeline (SourceAbiControls.data false pipeline))

#print axioms selector_complete
#print axioms signature_complete
#print axioms memory_complete
#print axioms memory_vector
#print axioms selector_vector
#print axioms identical_payload
#print axioms distinct_machine_allocation
#print axioms selector_not_signature
#print axioms memory_payload_length
#print axioms memory_stale_pointer
#print axioms memory_stale_not_output
#print axioms memory_statement_timeout
#print axioms memory_argument_timeout
#print axioms memory_allocation_timeout
#print axioms memory_intrinsic_transport
#print axioms signature_drop
#print axioms drop_prefix_body
end Solidity.Lowering.V08.SourcePrefixedRethrowControls
