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

#print axioms joint
#print axioms prefix_failure
#print axioms actual
#print axioms observed
#print axioms observation_not_recovery
end H62.AuditV08Adapters.SourceCustomErrorFailureJoint
