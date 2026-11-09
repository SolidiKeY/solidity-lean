import Solidity.Lowering.V08.SourceCustomErrorControls

/-! Regression: custom-error execution and selector transport require coherent
argument/encoding states, a real fixed pin and actual signature-input equality.
Existing fixtures supply them jointly; reverting does not erase prior allocation.
The non-ASCII input mismatch is not an identifier-admission exclusion or hash
noncollision claim. No canonical origin/admission or target certificate. -/
namespace H62.AuditV08Adapters.SourceCustomErrorJoint
open Solidity Source
open Solidity.Lowering.V08
open SourceCustomErrorControls

/-- All original execution and selector premises refer to the same fixture. -/
def Joint (pipeline : Roadmap.Pipeline) (static : Bool) (extra : Nat) : Prop :=
  errorDeclaration.paramTys E = some [STy.bytes32,.bool,.bool] ∧
  (Source.evalConvArgs (global pipeline) {frame with static:=static} (extra+10)
    arguments).run (locals,populated) =
    (.ok (values pipeline),(.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) ∧
  (Source.encodeVals {frame with static:=static} (extra+10) false
    (values pipeline).toR : Source.EM E [] _).run
      (Source.L0 E,SourceKeccak.afterLiteral populated binary) =
    (.ok (encoded pipeline),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) ∧
  (global pipeline).fixed.Keccak ∧
  Source.asciiBytes (Source.sigOf E.layout errorDeclaration.name [STy.bytes32,.bool,.bool]) =
    "Bad(bytes32,bool,bool)".toUTF8.toList

theorem joint (pipeline : Roadmap.Pipeline) (static : Bool) (extra : Nat) :
    Joint pipeline static extra :=
  ⟨rfl, arguments_execute pipeline static extra, encoding_execute pipeline static extra,
    Roadmap.Controls.toyFixed_keccak, signature_bytes⟩

theorem actual_source (pipeline : Roadmap.Pipeline) (static : Bool) (extra : Nat) :
    (Source.execS (global pipeline) {frame with static:=static} (extra+11) 0 none
      statement locals).run (Source.L0 E,populated) =
    (.error (.revert ((global pipeline).selector
      (Source.sigOf E.layout errorDeclaration.name [STy.bytes32,.bool,.bool]) ++ encoded pipeline)),
      (Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  have h := joint pipeline static extra
  exact SourceCustomErrors.execute (global pipeline) {frame with static:=static} (extra+10)
    errorDeclaration h.1 arguments locals (.cons (.bool false) .nil) populated _ _
    (values pipeline) (encoded pipeline) h.2.1 h.2.2.1

/-- Exact intrinsic selector observation; the Source execution remains independent. -/
theorem actual_payload (pipeline : Roadmap.Pipeline) (static : Bool) (extra : Nat) :
    (Source.execS (global pipeline) {frame with static:=static} (extra+11) 0 none
      statement locals).run (Source.L0 E,populated) =
    (.error (.revert (Semantics.selectorBytes
      (Semantics.customSelector "Bad(bytes32,bool,bool)") ++ encoded pipeline)),
      (Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  have h := joint pipeline static extra
  rw [actual_source, SourceCustomErrors.selector_of_bytes (global pipeline) h.2.2.2.1
    _ "Bad(bytes32,bool,bool)" h.2.2.2.2]

/-- An exact revert result still retains the allocation made by its arguments. -/
theorem error_not_rollback (pipeline : Roadmap.Pipeline) (static : Bool) (extra : Nat) :
    (Source.execS (global pipeline) {frame with static:=static} (extra+11) 0 none
      statement locals).run (Source.L0 E,populated) ≠
    (.error (.revert ((global pipeline).selector
      (Source.sigOf E.layout errorDeclaration.name [STy.bytes32,.bool,.bool]) ++ encoded pipeline)),
      (Source.L0 E,populated)) := by
  rw [actual_source]
  intro same
  have heapSame := congrArg (fun result => result.2.2.heap.next) same
  change 2 = 1 at heapSame
  cases heapSame

/-- Existing encoding-mismatch countermodel; not Source identifier rejection. -/
theorem unicode_premise_refused :
    ¬ (Source.asciiBytes ['é'] = "é".toUTF8.toList) :=
  SourceCustomErrors.distinct_input_encodings

#print axioms joint
#print axioms actual_source
#print axioms actual_payload
#print axioms error_not_rollback
#print axioms unicode_premise_refused
end H62.AuditV08Adapters.SourceCustomErrorJoint
