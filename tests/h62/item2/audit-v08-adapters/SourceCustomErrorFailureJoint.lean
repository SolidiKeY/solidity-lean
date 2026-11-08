import Solidity.Lowering.V08.SourceCustomErrorFailureControls

/-! Regression: a successful converted head and failing tail must share the
same reached heap/locals, and EM.attempt observing a failure is not recovery.
Existing populated controls supply actual executions. No Source admission,
Solidity catch dispatch, target body/frame or full-session certificate. -/
namespace H62.AuditV08Adapters.SourceCustomErrorFailureJoint
open Solidity Source
open Solidity.Lowering.V08
open SourceCustomErrorControls SourceCustomErrorFailureControls

def Joint (pipeline : Roadmap.Pipeline) (static : Bool) : Prop :=
  (do Source.getV (← Source.convRV {frame with static:=static} 11 STy.bytes32
    (← Source.evalE (global pipeline) {frame with static:=static} 11 (SourceKeccak.literal binary))) :
    Source.EM E [.bool] _).run (locals,populated) =
    (.ok (digest pipeline),(locals,SourceKeccak.afterLiteral populated binary)) ∧
  (Source.evalConvArgs (global pipeline) {frame with static:=static} 11 panicTail).run
    (locals,SourceKeccak.afterLiteral populated binary) =
    (.error (.revert (Source.panicData .divZero)),
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary))

theorem joint (pipeline : Roadmap.Pipeline) (static : Bool) : Joint pipeline static :=
  ⟨converted_hash_head pipeline static,changed_local_tail_failure pipeline static⟩

theorem prefix_failure (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalConvArgs (global pipeline) {frame with static:=static} 12 panicArguments).run
      (locals,populated) =
      (.error (.revert (Source.panicData .divZero)),
        (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) := by
  have h := joint pipeline static
  exact SourceCustomErrorFailures.converted_tail_failure (global pipeline) {frame with static:=static}
    11 (SourceKeccak.literal binary) rfl panicTail locals locals (.cons (.bool false) .nil)
    populated _ _ (digest pipeline) (.revert (Source.panicData .divZero)) h.1 h.2

theorem actual (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 13 0 none
      (.revertError errorDeclaration rfl panicArguments : RStmt E [] false .body [.bool] [.bool])
      locals).run (Source.L0 E,populated) =
      (.error (.revert (Source.panicData .divZero)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  SourceCustomErrorFailures.arguments_failure (global pipeline) {frame with static:=static} 12
    errorDeclaration rfl panicArguments locals (.cons (.bool false) .nil) populated _
    (.revert (Source.panicData .divZero)) (prefix_failure pipeline static)

theorem observed (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.EM.attempt (Source.execS (global pipeline) {frame with static:=static} 13 0 none
      (.revertError errorDeclaration rfl panicArguments : RStmt E [] false .body [.bool] [.bool])
      locals)).run (Source.L0 E,populated) =
      (.ok (.error (.revert (Source.panicData .divZero))),
        (Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  SourceCustomErrorFailures.attempt_failure _ _ _ _ _ _ (actual pipeline static)

/-- A successful outer observation contains the original error, not normal execution. -/
theorem observation_not_recovery (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.EM.attempt (Source.execS (global pipeline) {frame with static:=static} 13 0 none
      (.revertError errorDeclaration rfl panicArguments : RStmt E [] false .body [.bool] [.bool])
      locals)).run (Source.L0 E,populated) ≠
      (.ok (.ok (.normal (.cons (.bool false) .nil))),
        (Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  rw [observed]
  intro same
  have result := congrArg Prod.fst same
  cases result

/-- Existing record allocation and failed encoding share the same reached state.
This local unsupported-encoding model is not global Source admission. -/
theorem encoding_joint (pipeline : Roadmap.Pipeline) (static : Bool) :
    recordError.paramTys E2 = some [STy.bytes32,.struct .memory recordName] ∧
    (Source.evalConvArgs (global2 pipeline) {frame2 with static:=static} 14 recordArgs).run
      (locals2,populated2) =
      (.ok (recordValues pipeline),(.cons (.bool false) .nil,recordState)) ∧
    (Source.encodeVals {frame2 with static:=static} 14 false (recordValues pipeline).toR :
      Source.EM E2 [] _).run (Source.L0 E2,recordState) =
      (.error (.stuck "not ABI-encodable"),(Source.L0 E2,recordState)) :=
  ⟨rfl,record_arguments pipeline static,record_encoding_failure pipeline static⟩

theorem encoding_actual (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global2 pipeline) {frame2 with static:=static} 15 0 none recordStatement
      locals2).run (Source.L0 E2,populated2) =
      (.error (.stuck "not ABI-encodable"),(Source.L0 E2,recordState)) := by
  have h := encoding_joint pipeline static
  exact SourceCustomErrorFailures.encoding_failure (global2 pipeline) {frame2 with static:=static} 14
    recordError h.1 recordArgs locals2 (.cons (.bool false) .nil) populated2 recordState recordState
    (recordValues pipeline) (.stuck "not ABI-encodable") h.2.1 h.2.2

/-- A source stuck result is not silently reclassified as an EVM-style revert. -/
theorem encoding_stuck_not_revert (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global2 pipeline) {frame2 with static:=static} 15 0 none recordStatement
      locals2).run (Source.L0 E2,populated2) ≠
      (.error (.revert []),(Source.L0 E2,recordState)) := by
  rw [encoding_actual]
  intro same
  have status := congrArg Prod.fst same
  cases status

/-- The rethrow reference selects exactly the allocated byte object. -/
theorem rethrow_joint (bytes : Roadmap.Bytes) :
    (.cons (.memRef rfl populated.heap.next) .nil : Source.Locals E.layout [.bytes .memory]).get
      .here = .memRef rfl populated.heap.next ∧
    (SourceKeccak.afterLiteral populated bytes).heap.get populated.heap.next =
      some ⟨.bytes .memory,.bytes bytes⟩ :=
  ⟨rfl,SourceKeccak.allocated populated bytes⟩

theorem rethrow_actual (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat)
    (bytes : Roadmap.Bytes) :
    (Source.execS (global pipeline) {frame with static:=static} (fuel+1) 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl populated.heap.next) .nil)).run
      (Source.L0 E,SourceKeccak.afterLiteral populated bytes) =
      (.error (.revert bytes),(Source.L0 E,SourceKeccak.afterLiteral populated bytes)) :=
  SourceCustomErrorFailures.rethrow_bytes (global pipeline) {frame with static:=static} fuel .here
    (.cons (.memRef rfl populated.heap.next) .nil) _ populated.heap.next bytes
    (rethrow_joint bytes).1 (rethrow_joint bytes).2

theorem rethrow_timeout (pipeline : Roadmap.Pipeline) (static : Bool) (bytes : Roadmap.Bytes) :
    (Source.execS (global pipeline) {frame with static:=static} 0 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl populated.heap.next) .nil)).run
      (Source.L0 E,SourceKeccak.afterLiteral populated bytes) =
      (.error .timeout,(Source.L0 E,SourceKeccak.afterLiteral populated bytes)) :=
  SourceCustomErrorFailures.rethrow_zero_horizon (global pipeline) {frame with static:=static}
    .here (.cons (.memRef rfl populated.heap.next) .nil) _

/-- Timeout and rethrow stay distinct even when the bytes are empty. -/
theorem rethrow_timeout_not_revert (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat)
    (bytes : Roadmap.Bytes) :
    (Source.execS (global pipeline) {frame with static:=static} 0 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl populated.heap.next) .nil)).run
      (Source.L0 E,SourceKeccak.afterLiteral populated bytes) ≠
    (Source.execS (global pipeline) {frame with static:=static} (fuel+1) 0 none
      (.rethrow .here : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      (.cons (.memRef rfl populated.heap.next) .nil)).run
      (Source.L0 E,SourceKeccak.afterLiteral populated bytes) := by
  rw [rethrow_timeout,rethrow_actual]
  intro same
  have status := congrArg Prod.fst same
  cases status

#print axioms encoding_joint
#print axioms encoding_actual
#print axioms encoding_stuck_not_revert
#print axioms rethrow_joint
#print axioms rethrow_actual
#print axioms rethrow_timeout
#print axioms rethrow_timeout_not_revert

#print axioms joint
#print axioms prefix_failure
#print axioms actual
#print axioms observed
#print axioms observation_not_recovery
end H62.AuditV08Adapters.SourceCustomErrorFailureJoint
