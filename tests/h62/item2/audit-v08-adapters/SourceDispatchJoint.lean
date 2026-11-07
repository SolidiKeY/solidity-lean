import Solidity.Lowering.V08.SourceDispatchControls

/-! Regression: outside-chain dispatch must not be witnessed by an empty chain
or silently select a same-name caller decoy. The existing nonempty Source model
jointly supplies free/outside predicates and distinct body identities. Existing
ambient calls are linked as operational components, not library deployment,
canonical body/link/admission or target correspondence certificates. -/
namespace H62.AuditV08Adapters.SourceDispatchJoint
open Solidity Source
open Solidity.Lowering.V08
open SourceDispatchControls

/-- Same environment/program, actual nonempty chain and different decoy body. -/
def Joint (pipeline : Roadmap.Pipeline) : Prop :=
  freeDecl.scope = none ∧ E.linearize frame.contract = some ["C"] ∧
  ((E.linearize frame.contract).getD [frame.contract]).any
    (some · == libraryFunction.scope) = false ∧
  (global pipeline).prog.body freeDecl = some body ∧
  (global pipeline).prog.body libraryFunction = some body ∧
  (global pipeline).prog.body callerDecoy = some decoyBody

theorem joint (pipeline : Roadmap.Pipeline) : Joint pipeline :=
  ⟨rfl, caller_chain, rfl, rfl, rfl, rfl⟩

/-- Both exact original selection laws apply with actual branch predicates. -/
theorem actual_selection (pipeline : Roadmap.Pipeline) :
    (global pipeline).dispatchFn frame.contract freeDecl = freeDecl ∧
    (global pipeline).dispatchFn frame.contract libraryFunction = libraryFunction := by
  have h := joint pipeline
  exact ⟨SourceDispatch.free_selection _ _ _ h.1,
    SourceDispatch.outside_selection _ _ _ h.2.2.1⟩

/-- Both original body laws retain the same real supplied body, not the decoy. -/
theorem actual_bodies (pipeline : Roadmap.Pipeline) :
    (global pipeline).prog.body ((global pipeline).dispatchFn frame.contract freeDecl) = some body ∧
    (global pipeline).prog.body ((global pipeline).dispatchFn frame.contract libraryFunction) = some body := by
  have h := joint pipeline
  constructor
  · rw [SourceDispatch.free_body _ _ _ h.1]
    exact h.2.2.2.1
  · rw [SourceDispatch.outside_body _ _ _ h.2.2.1]
    exact h.2.2.2.2.1

/-- Two independent existing Source calls retain ambient result and full state.
This is not a sequential session-composition theorem. -/
theorem ambient_calls (pipeline : Roadmap.Pipeline) :
    (Source.callInternal (global pipeline) frame 25 freeDecl params returnTypes).run
      (Source.L0 E,populated) =
      (.ok result,(Source.L0 E,SourceKeccak.afterLiteral populated binary)) ∧
    (Source.callInternal (global pipeline) frame 25 libraryFunction params returnTypes).run
      (Source.L0 E,populated) =
      (.ok result,(Source.L0 E,SourceKeccak.afterLiteral populated binary)) :=
  ⟨free_call pipeline, library_call pipeline⟩

/-- The actual outside branch cannot select the same-name caller declaration. -/
theorem decoy_selection_refused (pipeline : Roadmap.Pipeline) :
    (global pipeline).dispatchFn frame.contract libraryFunction ≠ callerDecoy := by
  rw [(actual_selection pipeline).2]
  intro same
  have scopes := congrArg Source.Decl.scope same
  exact (by decide +kernel : (some "L" : Option String) ≠ some "C") scopes

/-- The actual in-chain decoy cannot witness the outside-chain hypothesis. -/
theorem decoy_outside_refused :
    ¬ (((E.linearize frame.contract).getD [frame.contract]).any
      (some · == callerDecoy.scope) = false) := by decide +kernel

#print axioms joint
#print axioms actual_selection
#print axioms actual_bodies
#print axioms ambient_calls
#print axioms decoy_selection_refused
#print axioms decoy_outside_refused
end H62.AuditV08Adapters.SourceDispatchJoint
