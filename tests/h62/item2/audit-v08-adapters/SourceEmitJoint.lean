import Solidity.Lowering.V08.SourceEmitControls

/-! Regression: emit arguments and encoding must agree on the reached heap.
Static refusal occurs after these effects; argument panic precedes that refusal
and retains its distinct payload. Existing fixtures supply the actual steps,
not canonical Source admission, target emitter selection or session adequacy. -/
namespace H62.AuditV08Adapters.SourceEmitJoint
open Solidity Source
open Solidity.Lowering.V08
open SourceEmitControls

/-- Shared actual argument and encoding premises, including declaration typing. -/
def Joint (pipeline : Roadmap.Pipeline) (static : Bool) (extra : Nat) : Prop :=
  eventDeclaration.paramTys E = some [STy.bytes32,.bool,.bool] ∧
  (Source.evalConvArgs (global pipeline) {frame with static:=static} (extra+10)
    arguments).run (locals,populated) =
    (.ok (values pipeline),(.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) ∧
  (Source.encodeVals {frame with static:=static} (extra+10) false (values pipeline).toR :
    Source.EM E [] _).run (Source.L0 E,SourceKeccak.afterLiteral populated binary) =
    (.ok (encoded pipeline),(Source.L0 E,SourceKeccak.afterLiteral populated binary))

theorem joint (pipeline : Roadmap.Pipeline) (static : Bool) (extra : Nat) :
    Joint pipeline static extra :=
  ⟨rfl,arguments_execute pipeline static extra,encoding_execute pipeline static extra⟩

theorem actual (pipeline : Roadmap.Pipeline) (extra : Nat) :
    (Source.execS (global pipeline) frame (extra+11) 0 none statement locals).run
      (Source.L0 E,populated) =
    (.ok (.normal (.cons (.bool false) .nil)),
      (Source.L0 E,SourceEmit.logged (global pipeline) frame eventDeclaration
        [STy.bytes32,.bool,.bool] (encoded pipeline) (SourceKeccak.afterLiteral populated binary))) := by
  have h := joint pipeline false extra
  exact SourceEmit.exec_success (global pipeline) frame (extra+10) eventDeclaration h.1 arguments
    locals (.cons (.bool false) .nil) populated _ _ (values pipeline) (encoded pipeline)
    h.2.1 h.2.2 rfl

theorem static_actual (pipeline : Roadmap.Pipeline) (extra : Nat) :
    (Source.execS (global pipeline) {frame with static:=true} (extra+11) 0 none
      statement locals).run (Source.L0 E,populated) =
    (.error (.revert []),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  have h := joint pipeline true extra
  exact SourceEmit.exec_static (global pipeline) {frame with static:=true} (extra+10)
    eventDeclaration h.1 arguments locals (.cons (.bool false) .nil) populated _ _
    (values pipeline) (encoded pipeline) h.2.1 h.2.2 rfl

/-- Actual argument panic discharges the original failure premise even in static mode. -/
theorem argument_panic (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 11 0 none
      (.emit eventDeclaration rfl failingArguments : RStmt E [] false .body [.bool] [.bool])
      locals).run (Source.L0 E,populated) =
    (.error (.revert (Source.panicData .divZero)),
      (Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  SourceEmit.exec_argument_failure (global pipeline) {frame with static:=static} 10
    eventDeclaration rfl failingArguments locals locals populated _
    (.revert (Source.panicData .divZero)) (panic_arguments pipeline static)

/-- Two runs share the reached heap but retain their different failure payloads. -/
theorem panic_not_static_refusal (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) {frame with static:=true} 11 0 none
      (.emit eventDeclaration rfl failingArguments : RStmt E [] false .body [.bool] [.bool])
      locals).run (Source.L0 E,populated) ≠
    (Source.execS (global pipeline) {frame with static:=true} 11 0 none statement locals).run
      (Source.L0 E,populated) := by
  rw [argument_panic,static_actual pipeline 0]
  intro same
  have payload := congrArg (fun result => match result.1 with
    | .error (.revert bytes) => bytes
    | _ => []) same
  exact nonempty_panic payload

/-- Simultaneous premises in the original full typed domain. This deliberately
malformed reference is a local encoding-error model, not Source admission. -/
theorem encoding_error_joint (pipeline : Roadmap.Pipeline) :
    bytesEvent.paramTys E = some [.bytes .memory] ∧
    (Source.evalConvArgs (global pipeline) {frame with static:=true} 3
      danglingArguments).run (danglingLocals,populated) =
      (.ok danglingValues,(danglingLocals,populated)) ∧
    (Source.encodeVals {frame with static:=true} 3 false danglingValues.toR :
      Source.EM E [] _).run (Source.L0 E,populated) =
      (.error (.stuck "dangling memory reference"),(Source.L0 E,populated)) :=
  ⟨rfl,dangling_arguments_execute pipeline,dangling_encoding_execute⟩

theorem encoding_error_actual (pipeline : Roadmap.Pipeline) :
    (Source.execS (global pipeline) {frame with static:=true} 4 0 none
      (.emit bytesEvent rfl danglingArguments : RStmt E [] false .body [.bytes .memory] [.bytes .memory])
      danglingLocals).run (Source.L0 E,populated) =
      (.error (.stuck "dangling memory reference"),(Source.L0 E,populated)) := by
  have h := encoding_error_joint pipeline
  exact SourceEmit.exec_encoding_failure (global pipeline) {frame with static:=true} 3
    bytesEvent h.1 danglingArguments danglingLocals danglingLocals populated populated populated
    danglingValues (.stuck "dangling memory reference") h.2.1 h.2.2

#print axioms encoding_error_joint
#print axioms encoding_error_actual

#print axioms joint
#print axioms actual
#print axioms static_actual
#print axioms argument_panic
#print axioms panic_not_static_refusal
end H62.AuditV08Adapters.SourceEmitJoint
