import Solidity.Lowering.V08.SourceAbiControls

/-! Regression: ABI argument evaluation and encoding must share the reached
locals/heap; successful bytes alone do not identify the result allocation.
The existing mixed fixture supplies both actual steps, including argument-local
updates and hash-input allocation. Timeout preserves earlier effects rather
than assuming rollback. No new encoder, Source admission or target certificate. -/
namespace H62.AuditV08Adapters.SourceAbiJoint
open Solidity Source
open Solidity.Lowering.V08
open SourceCustomErrorControls

/-- Both original execution premises coexist with their exact shared state. -/
def Joint (pipeline : Roadmap.Pipeline) (static packed : Bool) : Prop :=
  (Source.evalArgs (global pipeline) {frame with static:=static} 16
    SourceAbiControls.arguments).run (locals,populated) =
    (.ok (SourceAbiControls.values pipeline),
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) ∧
  (Source.encodeVals {frame with static:=static} 16 packed
    (SourceAbiControls.values pipeline) : Source.EM E [.bool] _).run
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary) =
    (.ok (SourceAbiControls.data packed pipeline),
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary))

theorem joint (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    Joint pipeline static packed :=
  ⟨SourceAbiControls.arguments_execute pipeline static,
    SourceAbiControls.encoding_execute pipeline static packed⟩

/-- Full original ABI expression result, including reached allocator pointer. -/
theorem actual (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 17
      (.abiEncode (if packed then .encodePacked else .encode)
        SourceAbiControls.arguments)).run (locals,populated) =
    (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
      SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
        (SourceAbiControls.data packed pipeline))) := by
  have h := joint pipeline static packed
  exact SourceAbi.execute (global pipeline) {frame with static:=static} 16 packed
    SourceAbiControls.arguments locals (.cons (.bool false) .nil) (.cons (.bool false) .nil)
    populated _ _ (SourceAbiControls.values pipeline) _ h.1 h.2

/-- Existing insufficient-horizon execution retains the earlier local write. -/
theorem timeout_after_effects (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 6
      (.abiEncode (if packed then .encodePacked else .encode)
        SourceAbiControls.arguments)).run (locals,populated) =
    (.error .timeout,(.cons (.bool false) .nil,populated)) :=
  SourceAbiControls.insufficient_after_effects pipeline static packed

theorem timeout_not_rollback (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 6
      (.abiEncode (if packed then .encodePacked else .encode)
        SourceAbiControls.arguments)).run (locals,populated) ≠
      (.error .timeout,(locals,populated)) := by
  rw [timeout_after_effects]
  intro same
  have localSame := congrArg (fun result => result.2.1.get .here) same
  cases localSame

/-- Existing whole-state refusal prevents silently skipping the hash allocation. -/
theorem skipped_allocation_refused (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 17
      (.abiEncode (if packed then .encodePacked else .encode)
        SourceAbiControls.arguments)).run (locals,populated) ≠
      (.ok (.val (.memRef rfl 1)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral populated (SourceAbiControls.data packed pipeline))) :=
  SourceAbiControls.wrong_skipped_hash pipeline static packed

#print axioms joint
#print axioms actual
#print axioms timeout_after_effects
#print axioms timeout_not_rollback
#print axioms skipped_allocation_refused
end H62.AuditV08Adapters.SourceAbiJoint
