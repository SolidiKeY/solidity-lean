import Solidity.Lowering.V08.SourceStandardRethrow
import Solidity.Lowering.V08.SourceCustomErrorControls

/-! Regression: standard ABI rethrow must retain its encoded allocation on
statement timeout, without substituting raw bytes or Error(string) payloads.
Existing generic allocation/rethrow producers and a populated fixture are reused;
no Source admission, target body selection or session/frame certificate. -/
namespace H62.AuditV08Adapters.SourceStandardRethrowJoint
open Solidity Source
open Solidity.Lowering.V08
open SourceCustomErrorControls

/-- The exact expression premise and reached object coexist for arbitrary bytes. -/
theorem joint (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat)
    (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {frame with static:=static} (fuel+4)
      (SourceAbi.literal false bytes)).run (locals,populated) =
      (.ok (.val (.memRef rfl populated.heap.next)),
        (locals,SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)]))) ∧
    (SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)])).heap.get
      populated.heap.next = some ⟨.bytes .memory,.bytes (Source.abiLayout [(true,bytes)])⟩ :=
  ⟨SourceAbi.literal_execution (global pipeline) {frame with static:=static} fuel false bytes locals populated,
    SourceRethrow.allocated_object populated (Source.abiLayout [(true,bytes)])⟩

theorem statement_timeout (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat)
    (bytes : Roadmap.Bytes) :
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} (fuel+4) 0
      bytes).run (locals,populated) =
      (.error .timeout,(locals,SourceKeccak.afterLiteral populated (Source.abiLayout [(true,bytes)]))) :=
  SourceStandardRethrow.expression_statement_timeout (global pipeline) {frame with static:=static}
    (fuel+4) (SourceAbi.literal false bytes) locals locals populated _ populated.heap.next
    (joint pipeline static fuel bytes).1

/-- A timeout after encoding is not a restored pre-allocation machine. -/
theorem timeout_not_prestate (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat)
    (bytes : Roadmap.Bytes) :
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} (fuel+4) 0
      bytes).run (locals,populated) ≠ (.error .timeout,(locals,populated)) := by
  rw [statement_timeout]
  intro same
  have heapSame := congrArg (fun result => result.2.2.heap.next) same
  change 2 = 1 at heapSame
  cases heapSame

/-- Concrete payload observations on the existing binary input, not admission exclusions. -/
theorem payload_distinctions :
    Source.abiLayout [(true,binary)] ≠ binary ∧
    Source.abiLayout [(true,binary)] ≠ Source.errorData binary := by
  decide +kernel

/-- Even retaining the correct final heap cannot justify substituting the raw payload. -/
theorem raw_payload_refused (pipeline : Roadmap.Pipeline) (static : Bool)
    (allocationFuel statementFuel : Nat) :
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static}
      (allocationFuel+4) (statementFuel+1) binary).run (locals,populated) ≠
      (.error (.revert binary),
        (locals,SourceKeccak.afterLiteral populated (Source.abiLayout [(true,binary)]))) := by
  rw [SourceStandardRethrow.literal_execution]
  intro same
  have payload := congrArg (fun result => match result.1 with
    | .error (.revert bytes) => bytes
    | _ => []) same
  exact payload_distinctions.1 payload

/-- Both original early horizons retain the full prestate, for any later horizon. -/
theorem early_timeouts (pipeline : Roadmap.Pipeline) (static : Bool)
    (statementHorizon : Nat) (bytes : Roadmap.Bytes) :
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} 0
      statementHorizon bytes).run (locals,populated) =
      (.error .timeout,(locals,populated)) ∧
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} 1
      statementHorizon bytes).run (locals,populated) =
      (.error .timeout,(locals,populated)) :=
  ⟨SourceStandardRethrow.literal_allocation_timeout (global pipeline) {frame with static:=static}
      statementHorizon bytes locals populated,
    SourceStandardRethrow.literal_argument_timeout (global pipeline) {frame with static:=static}
      statementHorizon bytes locals populated⟩

/-- The same timeout classification does not identify the same complete machine. -/
theorem post_timeout_not_early (pipeline : Roadmap.Pipeline) (static : Bool)
    (allocationFuel statementHorizon : Nat) (bytes : Roadmap.Bytes) :
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} (allocationFuel+4)
      0 bytes).run (locals,populated) ≠
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} 0
      statementHorizon bytes).run (locals,populated) ∧
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} (allocationFuel+4)
      0 bytes).run (locals,populated) ≠
    (SourceStandardRethrow.literal (global pipeline) {frame with static:=static} 1
      statementHorizon bytes).run (locals,populated) := by
  have early := early_timeouts pipeline static statementHorizon bytes
  constructor
  · rw [early.1]
    exact timeout_not_prestate pipeline static allocationFuel bytes
  · rw [early.2]
    exact timeout_not_prestate pipeline static allocationFuel bytes

#print axioms early_timeouts
#print axioms post_timeout_not_early

#print axioms joint
#print axioms statement_timeout
#print axioms timeout_not_prestate
#print axioms payload_distinctions
#print axioms raw_payload_refused
end H62.AuditV08Adapters.SourceStandardRethrowJoint
